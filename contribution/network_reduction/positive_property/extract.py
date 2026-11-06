"""Strict ONNX extraction, rational certificates and smaller ONNX exports.

This is an untrusted producer. Lean checks arithmetic, pruning and bit decoding.
The byte-to-graph import and operator checks are part of the explicit bridge.
"""
import argparse
import copy
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import subprocess

import numpy as np
import onnx
from onnx import numpy_helper, helper

PIN = 'e9f6f1c52e0e5349455d2b4f69c2015567d3037f'
MODELS = {
    'DL2': ('DL2_Lipschitz.onnx', '64ed1bd8e69061357866879731a9aed301d11ce7db2aecf0fb531ab0af59032a', 31),
    'Godel': ('GD_Lipschitz.onnx', '5569b9931ee6774521bc2a7f2d2c99eba1873b39f1de7fc8a76f2f6e18b73ef1', 26),
}
DATA = 'python_training/data/Training_Data_Normalised.csv'
DATA_SHA = 'd0b84c0e372a25f7934953ae8adac8db08b7a3b241892a1aa697834f583acbf7'
SOURCES = [DATA, 'docs/paper/Paper_Arxiv.md',
           'vehicle_verification/property_verification/Alsomitra_Robustness.vcl']


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def pinned(upstream, name, expected=None):
    data = (upstream/name).read_bytes()
    blob = subprocess.check_output(['git', '-C', str(upstream), 'show', PIN+':'+name])
    if data != blob or (expected and hashlib.sha256(data).hexdigest() != expected):
        raise ValueError('Upstream bytes differ: '+name)
    return {'path': name, 'sha256': hashlib.sha256(data).hexdigest()}


def q(x):
    return F(float(x))


def leanq(x):
    v = F(x)
    return f'(mkRat ({v.numerator}) {v.denominator})'


def leanlist(xs, encode=leanq):
    return '[' + ', '.join(map(encode, xs)) + ']'


def bits(arrays):
    return np.concatenate([a.ravel().view(np.uint32) for a in arrays]).tolist()


def inspect_model(path):
    model = onnx.load(path, load_external_data=False)
    onnx.checker.check_model(model, full_check=True)
    if model.functions or model.graph.sparse_initializer:
        raise ValueError('Unexpected functions/sparse weights')
    if [(o.domain, o.version) for o in model.opset_import] != [('', 17)]:
        raise ValueError('Unexpected ONNX opset')
    if len(model.graph.input) != 1 or len(model.graph.output) != 1:
        raise ValueError('Unexpected graph arity')
    for v, width in [(model.graph.input[0], 6), (model.graph.output[0], 1)]:
        t = v.type.tensor_type
        if t.elem_type != onnx.TensorProto.FLOAT or len(t.shape.dim) != 2 or t.shape.dim[1].dim_value != width:
            raise ValueError('Unexpected input/output shape or type')
    nodes = list(model.graph.node)
    if [n.op_type for n in nodes] != ['Gemm', 'Relu', 'Gemm', 'Relu', 'Gemm']:
        raise ValueError('Unexpected graph topology/output activation')
    previous = model.graph.input[0].name
    for j, n in enumerate(nodes):
        if n.domain or len(n.output) != 1 or n.input[0] != previous:
            raise ValueError('Unexpected graph edge')
        if n.op_type == 'Gemm':
            i = j//2+1
            if list(n.input) != [previous, f'fc{i}.weight', f'fc{i}.bias']:
                raise ValueError('Unexpected Gemm operands')
            attrs = {a.name: helper.get_attribute_value(a) for a in n.attribute}
            if attrs.get('alpha', 1) != 1 or attrs.get('beta', 1) != 1 or attrs.get('transA', 0) != 0 or attrs.get('transB', 0) != 1 or set(attrs)-{'alpha','beta','transA','transB'}:
                raise ValueError('Unexpected Gemm attributes')
        elif len(n.input) != 1 or n.attribute:
            raise ValueError('Unexpected Relu operands/attributes')
        previous = n.output[0]
    if previous != model.graph.output[0].name:
        raise ValueError('Unexpected graph output')
    initializers = list(model.graph.initializer)
    names = [f'fc{i}.{suffix}' for i in [1,2,3] for suffix in ['weight','bias']]
    if len(initializers) != 6 or set(t.name for t in initializers) != set(names):
        raise ValueError('Unexpected initializer names')
    arrays = {t.name: numpy_helper.to_array(t) for t in initializers}
    result = []
    for i, shape in enumerate([(64,6), (32,64), (1,32)], 1):
        w, b = arrays[f'fc{i}.weight'], arrays[f'fc{i}.bias']
        if w.shape != shape or b.shape != (shape[0],) or any(a.dtype != np.float32 or not np.isfinite(a).all() for a in [w,b]):
            raise ValueError('Unexpected weight shape/dtype/value')
        result.append((w,b))
    return model, result


def rational_layers(layers):
    return [([[q(x) for x in row] for row in w], [q(x) for x in b]) for w,b in layers]


def bounds(layers):
    lo, hi = [F(0)]*6, [F(1)]*6
    cert = []
    for w,b in layers[:2]:
        ls = [bias+sum(min(a*l,a*u) for a,l,u in zip(row,lo,hi)) for row,bias in zip(w,b)]
        us = [bias+sum(max(a*l,a*u) for a,l,u in zip(row,lo,hi)) for row,bias in zip(w,b)]
        cert.append(list(zip(ls,us)))
        lo,hi = [max(F(0),v) for v in ls], [max(F(0),v) for v in us]
    return cert


def path_cost(layers):
    c = [F(1)]*6
    for w,_ in layers:
        c = [sum(abs(a)*b for a,b in zip(row,c)) for row in w]
    assert len(c)==1
    return c[0]


def source(name, layers, checkpoint_bits, reduced_bits, cert, cap):
    ls = rational_layers(layers)
    layer_text = ['[\n'+',\n'.join('  ⟨'+leanlist(row)+', '+leanq(bias)+'⟩' for row,bias in zip(w,b))+'\n]' for w,b in ls]
    masks = [[u>0 for _,u in bs] for bs in cert]
    bools = lambda vs: leanlist(vs, lambda b: 'true' if b else 'false')
    intervals = lambda bs: leanlist(bs, lambda b: '⟨'+leanq(b[0])+', '+leanq(b[1])+'⟩')
    return f'''-- Generated from pinned upstream ONNX bytes by extract.py.
import LinearPruning
import Float32
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace Contribution.PositiveProperty.{name}
open Contribution.Universal Contribution.Reduction
def network : Network := ⟨{', '.join(layer_text)}⟩
def flat (n : Network) : List ℚ := [n.first,n.second,n.third].flatMap
  (fun ns => ns.flatMap Neuron.weights ++ ns.map Neuron.bias)
def checkpointBits : List Nat := {leanlist(checkpoint_bits,str)}
theorem decoded : checkpointBits.map Contribution.Float32.decode =
    (flat network).map some := by decide +kernel
theorem shape : (network.first.map (fun n => n.weights.length),
    network.second.map (fun n => n.weights.length), network.third.map (fun n => n.weights.length)) =
    (List.replicate 64 6, List.replicate 32 64, List.replicate 1 32) := by rfl
theorem parameter_count : (flat network).length = 2561 := by rfl
theorem exact_path_cost : costs network (List.replicate 6 1) = [{leanq(path_cost(ls))}] := by decide +kernel
theorem checked : PositiveProperty.Check network {cap} := by decide +kernel
theorem global_bound (x y : Fin 6 → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ i, |x i-y i| ≤ d) : |output network x-output network y| ≤ {cap}*d :=
  checked_global network {cap} checked x y d hd h
theorem perturbation_bound (x y : Fin 6 → ℝ) (h : ∀ i, |x i-y i| ≤ 1/1000) :
    |output network x-output network y| ≤ {cap}/1000 := by
  have hh := global_bound x y (1/1000) (by norm_num) h
  norm_num at hh ⊢
  exact hh
theorem property5 : Property5 network (1/1000) (1/10000) :=
  property5_of_check network {cap} checked _ _ (by norm_num) (by norm_num)
def certificate : Certificate := ⟨{intervals(cert[0])}, {intervals(cert[1])},
  {bools(masks[0])}, {bools(masks[1])}⟩
theorem pruning_checked : Reduction.Check network cube certificate := by decide +kernel
def reduced : Network := prune network certificate.firstKeep certificate.secondKeep
theorem reduced_shape : (reduced.first.map (fun n => n.weights.length),
    reduced.second.map (fun n => n.weights.length), reduced.third.map (fun n => n.weights.length)) =
    (List.replicate 63 6, List.replicate 32 63, List.replicate 1 32) := by decide +kernel
theorem reduced_parameter_count : (flat reduced).length = 2522 := by decide +kernel
def reducedBits : List Nat := {leanlist(reduced_bits,str)}
theorem reduced_decoded : reducedBits.map Contribution.Float32.decode =
    (flat reduced).map some := by decide +kernel
theorem same_output (x : Fin 6 → ℝ) (hx : ValidInput x) :
    output reduced x = output network x := pruned_output network certificate pruning_checked x hx
theorem reduced_perturbation_bound (x y : Fin 6 → ℝ) (hx : ValidInput x) (hy : ValidInput y)
    (h : ∀ i, |x i-y i| ≤ 1/1000) : |output reduced x-output reduced y| ≤ {cap}/1000 := by
  rw [same_output x hx, same_output y hy]
  exact perturbation_bound x y h
theorem reduced_property5 : Property5 reduced (1/1000) (1/10000) :=
  property5_transfer network reduced _ _ same_output property5
theorem reject_zero_bound : ¬ PositiveProperty.Check network 0 := by decide +kernel
end Contribution.PositiveProperty.{name}
'''


def generate(upstream, out):
    out.mkdir(parents=True, exist_ok=True)
    evidence = {'upstream_commit': PIN, 'sources': [pinned(upstream,p,DATA_SHA if p==DATA else None) for p in SOURCES], 'models': {}}
    for name,(filename,expected,cap) in MODELS.items():
        rel = 'vehicle_verification/property_verification_2/'+filename
        rec = pinned(upstream,rel,expected)
        model,layers = inspect_model(upstream/rel)
        cert = bounds(rational_layers(layers))
        masks = [np.array([u>0 for _,u in bs]) for bs in cert]
        if [np.where(~m)[0].tolist() for m in masks] != [[58],[]]:
            raise ValueError('Unexpected pruning result')
        reduced_layers = [(layers[0][0][masks[0]],layers[0][1][masks[0]]),
                          (layers[1][0][masks[1]][:,masks[0]],layers[1][1][masks[1]]),
                          (layers[2][0][:,masks[1]],layers[2][1])]
        reduced = copy.deepcopy(model)
        replacement = {f'fc{i}.{suffix}':a for i,pair in enumerate(reduced_layers,1) for suffix,a in zip(['weight','bias'],pair)}
        for t in reduced.graph.initializer:
            t.CopyFrom(numpy_helper.from_array(replacement[t.name].copy(),t.name))
        onnx.checker.check_model(reduced, full_check=True)
        onnx.save(reduced,out/(name+'_reduced.onnx'))
        # Reload saved bytes before binding the exported bit patterns.
        exported = {t.name:numpy_helper.to_array(t) for t in onnx.load(out/(name+'_reduced.onnx')).graph.initializer}
        reduced_flat = [exported[f'fc{i}.{s}'] for i in [1,2,3] for s in ['weight','bias']]
        text = source(name,layers,bits([a for pair in layers for a in pair]),bits(reduced_flat),cert,cap)
        (out/(name+'Checkpoint.lean')).write_text(text)
        cost = path_cost(rational_layers(layers))
        if cost > cap:
            raise ValueError('Chosen bound too small')
        rec.update(path_cost_exact=str(cost), path_cost_approx=float(cost), certified_cap=cap,
                   removed_first_layer_indices=[58], original_parameters=2561, reduced_parameters=2522,
                   lean_sha256=sha(out/(name+'Checkpoint.lean')),
                   reduced_onnx_sha256=sha(out/(name+'_reduced.onnx')))
        evidence['models'][name]=rec
    (out/'EXTRACTION.json').write_text(json.dumps(evidence,indent=2)+'\n')
    return evidence


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream',required=True,type=Path)
    p.add_argument('--output',required=True,type=Path)
    a=p.parse_args()
    print(json.dumps(generate(a.upstream.absolute(),a.output.absolute()),indent=2))
