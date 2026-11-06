"""Generate exact certificates and physically smaller copies of pinned models.

Python/ONNX import and export are checked adapters, not verified compilers.
Lean independently checks the rational certificate and binary32 decoding.
"""
import copy
from fractions import Fraction as F
import hashlib
import itertools
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

import numpy as np
import onnx
from onnx import numpy_helper
import onnxruntime as ort
import torch
from torch import nn

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BUILD = ROOT / '.build/network_reduction'
sys.path.insert(0, str(ROOT / 'anchor_view/trained'))
from onnx_model import DenseController

PIN = 'e9f6f1c52e0e5349455d2b4f69c2015567d3037f'
MODELS = {
    'Baseline': ('final_base_model_norm.onnx',
        '35c0654a5916b859e3d3bd8fa127f4555ee7ba52f8a47e03610371af0f25645b'),
    'Adversarial': ('final_adversarial_model_0.005.onnx',
        '1154145b50c6eb0d1f4b41f7725aed19ca8ac1fe256536c3b27ac696501aaa6e'),
}
DATA = 'python_training/data/Training_Data_Normalised.csv'
DATA_SHA = 'd0b84c0e372a25f7934953ae8adac8db08b7a3b241892a1aa697834f583acbf7'


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def require(ok, message):
    if not ok:
        raise ValueError(message)


def rational(x):
    return F(float(x))


def leanq(x):
    q = rational(x) if not isinstance(x, F) else x
    return f'(mkRat ({q.numerator}) {q.denominator})'


def leanlist(xs):
    return '[' + ', '.join(xs) + ']'


def flatten(arrays):
    # Match Lean's neuron-major weight order, followed by layer biases.
    return np.concatenate([np.concatenate([w.T.flatten(), b]) for w, b in arrays])


def network(arrays):
    layers = []
    for w, b in arrays:
        layers.append(leanlist(['⟨' + leanlist(map(leanq, w[:, j])) + ', '
                               + leanq(b[j]) + '⟩' for j in range(len(b))]))
    return '⟨\n  ' + ',\n  '.join(layers) + '\n⟩'


def interval_bounds(arrays):
    box = [(F(0), F(1))] * 6
    bounds = []
    for w, b in arrays[:2]:
        out = []
        for j in range(len(b)):
            lo = hi = rational(b[j])
            for weight, (l, u) in zip(w[:, j], box):
                v = rational(weight)
                lo += min(v*l, v*u)
                hi += max(v*l, v*u)
            out.append((lo, hi))
        bounds.append(out)
        box = [(max(F(0), l), max(F(0), u)) for l, u in out]
    return bounds


def export_reduced(graph, arrays, masks, target):
    k1, k2 = masks
    w1, b1 = arrays[0]; w2, b2 = arrays[1]; w3, b3 = arrays[2]
    reduced = [(w1[:, k1].copy(), b1[k1].copy()),
               (w2[np.ix_(k1, k2)].copy(), b2[k2].copy()),
               (w3[k2, :].copy(), b3.copy())]
    new = copy.deepcopy(graph)
    for i, (w, b) in enumerate(reduced):
        for name, a in zip(new.graph.node[2*i].input[1:], (w, b)):
            for t in new.graph.initializer:
                if t.name == name:
                    t.CopyFrom(numpy_helper.from_array(a, name))
    # Inferred intermediate shapes belong to the old widths.
    del new.graph.value_info[:]
    onnx.checker.check_model(new)
    onnx.save(new, target)
    loaded = onnx.load(target)
    tensors = {t.name: numpy_helper.to_array(t).copy() for t in loaded.graph.initializer}
    exported = [tuple(tensors[n] for n in loaded.graph.node[2*i].input[1:]) for i in range(3)]
    for expected, actual in zip(reduced, exported):
        for a, b in zip(expected, actual):
            require(a.shape == b.shape and np.array_equal(a.view(np.uint32), b.view(np.uint32)),
                    'Export changed parameter bits')
    return exported  # Generate Lean from the reloaded export, not an assumed plan.


ROOTS = ['original_shape', 'reduced_shape', 'original_decoded', 'reduced_decoded',
         'original_parameters', 'reduced_parameters', 'checked', 'export_matches_prune',
         'all_real_inputs', 'equivalent_on_cube', 'output_predicate', 'domain_nonempty',
         'reject_active_neuron', 'reject_bad_bound', 'reject_short_mask']


def generate_lean(name, arrays, reduced, bounds, masks):
    ns = 'Contribution.Reduction.' + name
    text = ['import Pruning', 'import Float32', '',
            'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
            'set_option autoImplicit false', 'namespace ' + ns,
            'open Contribution.Universal Contribution.Reduction',
            'def original : Network := ' + network(arrays),
            'def reduced : Network := ' + network(reduced),
            'def domain : List Interval := List.replicate 6 ⟨0, 1⟩',
            'def certificate : Certificate := {',
            '  firstBounds := ' + leanlist(['⟨'+leanq(l)+', '+leanq(u)+'⟩' for l,u in bounds[0]]),
            '  secondBounds := ' + leanlist(['⟨'+leanq(l)+', '+leanq(u)+'⟩' for l,u in bounds[1]]),
            '  firstKeep := ' + leanlist([str(bool(k)).lower() for k in masks[0]]),
            '  secondKeep := ' + leanlist([str(bool(k)).lower() for k in masks[1]]) + ' }',
            'def flat (n : Network) : List ℚ :=',
            '  [n.first, n.second, n.third].flatMap',
            '    (fun ns => ns.flatMap Neuron.weights ++ ns.map Neuron.bias)']
    for label, a in [('original', arrays), ('reduced', reduced)]:
        vals = flatten(a)
        text.extend([
            f'def {label}Bits : List Nat := ' + leanlist(map(str, vals.view(np.uint32).tolist())),
            f'def {label}Rationals : List ℚ := ' + leanlist(map(leanq, vals)),
            f'theorem {label}_decoded : {label}Bits.map Contribution.Float32.decode =',
            f'    {label}Rationals.map some := by decide +kernel',
            f'theorem {label}_parameters : flat {label} = {label}Rationals := by rfl',
            f'theorem {label}_shape :',
            f'    ({label}.first.map (fun n => n.weights.length),',
            f'     {label}.second.map (fun n => n.weights.length),',
            f'     {label}.third.map (fun n => n.weights.length)) =',
            '    (' + ', '.join(f'List.replicate {len(b)} {len(w)}' for w,b in a) + ') := by rfl'])
    text.extend([
        'theorem checked : Check original domain certificate := by decide +kernel',
        'theorem export_matches_prune : reduced =',
        '    prune original certificate.firstKeep certificate.secondKeep := by decide +kernel',
        'theorem all_real_inputs (xs : List ℝ) (hx : InBox domain xs) :',
        '    eval reduced xs = eval original xs := by',
        '  rw [export_matches_prune]',
        '  exact certified_prune original domain certificate checked xs hx',
        'theorem equivalent_on_cube : EquivalentOn domain reduced original := all_real_inputs',
        'theorem output_predicate (P : List ℝ → Prop) (xs : List ℝ) (hx : InBox domain xs) :',
        '    P (eval reduced xs) ↔ P (eval original xs) := by rw [all_real_inputs xs hx]',
        'theorem domain_nonempty : InBox domain [0,0,0,0,0,0] := by',
        '  norm_num [domain, InBox, Interval.Mem, List.replicate_succ, List.forall₂_cons]',
        'theorem reject_active_neuron : ¬ Check original domain',
        '    { certificate with firstKeep := [false,true,true,true,true,false] } := by decide +kernel',
        'theorem reject_bad_bound : ¬ Check original domain',
        '    { certificate with firstBounds := List.replicate 6 ⟨0,0⟩ } := by decide +kernel',
        'theorem reject_short_mask : ¬ Check original domain',
        '    { certificate with firstKeep := [] } := by decide +kernel',
        'end ' + ns, ''])
    (HERE / (name + '.lean')).write_text('\n'.join(text))


def generate(upstream):
    BUILD.mkdir(parents=True, exist_ok=True)
    def git(*args):
        return subprocess.check_output(['git', '-C', str(upstream), *args])
    require(git('rev-parse', 'HEAD').decode().strip() == PIN, 'Wrong checkpoint revision')
    info = {'upstream_commit': PIN, 'domain': '[0,1]^6 in raw SAIV model coordinates', 'models': {}}
    for name, (filename, expected_sha) in MODELS.items():
        relative = 'python_training/models/' + filename
        path = upstream / relative
        require(sha(path) == expected_sha and path.read_bytes() == git('show', PIN+':'+relative),
                'Checkpoint mismatch')
        graph = onnx.load(path)
        arrays = DenseController(graph).arrays
        bounds = interval_bounds(arrays)
        masks = [np.array([u > 0 for _, u in layer]) for layer in bounds]
        output = BUILD / (name + '.onnx')
        reduced = export_reduced(graph, arrays, masks, output)
        generate_lean(name, arrays, reduced, bounds, masks)
        def stats(a):
            return dict(widths=[6]+[len(b) for _,b in a],
                        parameters=sum(w.size+b.size for w,b in a),
                        dense_multiplications=sum(w.size for w,_ in a))
        info['models'][name] = dict(original_sha256=expected_sha, reduced_sha256=sha(output),
            original=stats(arrays), reduced=stats(reduced),
            removed=[dict(layer=i+1, neuron=j, upper_exact=str(u), upper=float(u))
                     for i,layer in enumerate(bounds) for j,(_,u) in enumerate(layer) if u <= 0],
            original_parameter_bits=flatten(arrays).view(np.uint32).tolist(),
            reduced_parameter_bits=flatten(reduced).view(np.uint32).tolist())
    (BUILD/'manifest.json').write_text(json.dumps(info, indent=2)+'\n')
    return info


class SmallController(nn.Module):
    def __init__(self, graph):
        super().__init__()
        tensors = {t.name: numpy_helper.to_array(t).copy() for t in graph.graph.initializer}
        self.arrays = [tuple(tensors[n] for n in graph.graph.node[2*i].input[1:]) for i in range(3)]
        self.layers = nn.ModuleList()
        for w,b in self.arrays:
            with torch.random.fork_rng(devices=[]):
                layer = nn.Linear(*w.shape)
            with torch.no_grad():
                layer.weight.copy_(torch.from_numpy(w.T.copy()))
                layer.bias.copy_(torch.from_numpy(b))
            self.layers.append(layer)
        self.eval()

    def forward(self, x):
        for layer in self.layers:
            x = torch.relu(layer(x))
        return x


def exact_eval(arrays, row):
    xs = list(map(rational, row))
    for w,b in arrays:
        xs = [max(F(0), rational(b[j]) + sum((rational(v)*x for v,x in zip(w[:,j],xs)), F(0)))
              for j in range(len(b))]
    return xs


def compare(a, b):
    require(a.shape == b.shape and np.isfinite(a).all() and np.isfinite(b).all(), 'Bad outputs')
    # Outputs are nonnegative because of the final ReLU. Unsigned words are ordered here.
    require((a >= 0).all() and (b >= 0).all(), 'Expected nonnegative outputs')
    words_a = a.view(np.uint32).astype(np.int64)
    words_b = b.view(np.uint32).astype(np.int64)
    np.testing.assert_allclose(a, b, rtol=2e-5, atol=2e-6)
    different = np.flatnonzero(np.any(words_a != words_b, axis=1))
    witness = None
    if len(different):
        i = int(different[0])
        witness = dict(index=i, original=a[i].tolist(), reduced=b[i].tolist(),
                       original_bits=words_a[i].tolist(), reduced_bits=words_b[i].tolist())
    return dict(points=len(a), bitwise_equal=int(np.all(words_a == words_b, axis=1).sum()),
                max_abs=float(np.max(np.abs(a.astype(np.float64)-b))),
                max_ulp=int(np.max(np.abs(words_a-words_b))),
                first_difference=witness,
                tolerance=dict(rtol=2e-5, atol=2e-6))


def timing_pair(f, g, iterations=200, repeats=15):
    for _ in range(50):
        f(); g()
    samples = [[], []]
    for r in range(repeats):
        for i in ([0,1] if r%2 == 0 else [1,0]):
            fn = [f,g][i]
            start = time.perf_counter_ns()
            for _ in range(iterations):
                fn()
            samples[i].append((time.perf_counter_ns()-start)/iterations/1000)
    a,b = [float(np.median(s)) for s in samples]
    return dict(original_us=a, reduced_us=b, ratio_original_over_reduced=a/b,
                samples_us=samples, repeats=repeats, iterations_per_repeat=iterations)


def runtime(upstream):
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    data_path = upstream/DATA
    require(sha(data_path) == DATA_SHA, 'Dataset mismatch')
    data = np.loadtxt(data_path, delimiter=',', dtype=np.float32)
    require(data.shape == (360,7), 'Dataset dimensions changed')
    corners = np.array(list(itertools.product([0.,1.], repeat=6)), dtype=np.float32)
    random = np.random.default_rng(20261105).random((8192,6), dtype=np.float32)
    points = np.concatenate([data[:,:6],corners,random])
    require((points >= 0).all() and (points <= 1).all(), 'Validation outside proof domain')
    report = dict(status='PASS', universal_float32_equivalence='NOT_PROVED',
                  platform=platform.platform(), machine=platform.machine(),
                  torch=torch.__version__, onnx=onnx.__version__, onnxruntime=ort.__version__,
                  threads=1, data_sha256=DATA_SHA, dataset_rows=360, corners=64, random=8192,
                  seed=20261105, models={})
    for name,(filename,_) in MODELS.items():
        original_path = upstream/'python_training/models'/filename
        reduced_path = BUILD/(name+'.onnx')
        original = DenseController(onnx.load(original_path))
        reduced = SmallController(onnx.load(reduced_path))
        options = ort.SessionOptions()
        options.intra_op_num_threads = options.inter_op_num_threads = 1
        options.graph_optimization_level = ort.GraphOptimizationLevel.ORT_DISABLE_ALL
        sessions = [ort.InferenceSession(str(p), sess_options=options, providers=['CPUExecutionProvider'])
                    for p in [original_path,reduced_path]]
        reference = [np.concatenate([s.run(None,{s.get_inputs()[0].name:row[None,:]})[0] for row in points])
                     for s in sessions]
        with torch.inference_mode():
            tensor = torch.from_numpy(points)
            a,b = [m(tensor).numpy() for m in [original,reduced]]
            comparisons = {'pytorch_reduction':compare(a,b), 'onnx_reduction':compare(*reference),
                           'original_import':compare(a,reference[0]), 'reduced_import':compare(b,reference[1])}
            # Test float32 execution with the shape used by the ONNX interface too.
            single = [np.concatenate([m(row[None,:]).numpy() for row in tensor]) for m in [original,reduced]]
            comparisons['pytorch_batch1_reduction'] = compare(*single)
            for c in comparisons.values():
                if c['first_difference'] is not None:
                    c['first_difference']['input'] = points[c['first_difference']['index']].tolist()
            benchmarks = {}
            for batch in [1,64,1024]:
                x = tensor[:batch]
                benchmarks['pytorch_batch'+str(batch)] = timing_pair(lambda:original(x),lambda:reduced(x))
            x = points[:1]
            benchmarks['onnx_batch1'] = timing_pair(
                lambda:sessions[0].run(None,{sessions[0].get_inputs()[0].name:x}),
                lambda:sessions[1].run(None,{sessions[1].get_inputs()[0].name:x}))
        for row in np.concatenate([corners,random[:32]]):
            require(exact_eval(original.arrays,row) == exact_eval(reduced.arrays,row),
                    'Rational export replay mismatch')
        report['models'][name] = dict(comparisons=comparisons, benchmark=benchmarks,
            exact_rational_replay_points=96,
            original_bytes=original_path.stat().st_size, reduced_bytes=reduced_path.stat().st_size)
    return report
