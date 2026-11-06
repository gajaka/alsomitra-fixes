"""Exact affine synthesis cases and a checkpoint-derived calibration witness."""
import copy
import csv
from fractions import Fraction as Q
import hashlib
import itertools
import json
from pathlib import Path
import re

import synthesize as syn

HERE = Path(__file__).resolve().parent
DATA = 'python_training/data/Training_Data_Normalised.csv'
DATA_SHA = 'd0b84c0e372a25f7934953ae8adac8db08b7a3b241892a1aa697834f583acbf7'
NAMES = ['a0', 'a1', 'a2', 'a3', 'bias']


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def calibration(upstream):
    data = upstream / DATA
    if sha(data) != DATA_SHA:
        raise ValueError('Published normalized data hash mismatch')
    original = (HERE.parent / 'Adversarial.lean').read_text()
    literal = re.search(r'^def originalRationals : List ℚ := (.*)$', original, re.M).group(1)
    params = [Q(int(a), int(b)) for a, b in re.findall(r'mkRat \((-?\d+)\) (\d+)', literal)]
    if len(params) != 75:
        raise ValueError('Unexpected exact checkpoint shape')
    with data.open() as stream:
        raw = next(csv.reader(stream))
    sample = list(map(Q, raw[:6]))
    target = Q(raw[6])
    if len(raw) != 7 or not all(0 <= x <= 1 for x in sample):
        raise ValueError('Calibration sample not in certified input cube')
    # The exact literal parameters are independently bound to the original
    # checkpoint by the existing receipt. The new Lean binding recomputes
    # these features from Adversarial.original, not this adapter's parser.
    position, values = 0, sample
    for width, size in [(6, 6), (6, 4)]:
        weights = [params[position+i*width:position+(i+1)*width] for i in range(size)]
        position += width*size
        biases = params[position:position+size]
        position += size
        values = [max(Q(0), sum((w*x for w, x in zip(row, values)), b))
                  for row, b in zip(weights, biases)]
    z = values + [Q(1)]
    if z[1] != 0 or z[3] != 0:
        raise ValueError('Features contradict the dormant-neuron certificate')
    initial = params[position:]
    if len(initial) != 5:
        raise ValueError('Unexpected output head')
    rate = Q(1, 100)
    matrix = [[Q(i == j)-rate*z[i]*z[j] for j in range(5)] for i in range(5)]
    offset = [rate*target*z[i] for i in range(5)]
    updates = {name: dict(terms={src: str(matrix[i][j]) for j, src in enumerate(NAMES)},
                          constant=str(offset[i])) for i, name in enumerate(NAMES)}
    spec = dict(coordinates=NAMES, seed=['a0', 'a2', 'bias'],
                operations=[dict(name='frozen_feature_delta_rule', updates=updates)])
    witness = dict(data_path=DATA, data_sha256=DATA_SHA, physical_row=1,
                   input=list(map(str, sample)), target=str(target), rate=str(rate),
                   features=list(map(str, z)), initial_head=list(map(str, initial)),
                   input_interpretation='Exact decimal rationals from the published CSV, not binary32 parsing',
                   loss='One-half squared error of the pre-final-ReLU affine score',
                   scope='One illustrative calibration sample; no held-out accuracy or upstream retraining claim')
    return spec, witness


def binding_source(witness):
    qs = lambda xs: ', '.join(syn.qlean(Q(x)) for x in xs)
    return '\n'.join([
        'import Calibration', 'import RationalFeatures', '',
        'set_option autoImplicit false', 'set_option maxRecDepth 100000', 'set_option maxHeartbeats 0',
        'namespace Contribution.Reduction.UpdateSynthesis.CalibrationBinding',
        'open Contribution.Universal AffineRetention RationalFeatures',
        'def sample : List ℚ := [' + qs(witness['input']) + ']',
        'def z : Vector 5 := ![' + qs(witness['features']) + ']',
        'def target : ℚ := ' + syn.qlean(Q(witness['target'])),
        'def rate : ℚ := ' + syn.qlean(Q(witness['rate'])),
        'theorem sample_in_domain : InBox Adversarial.domain (sample.map fun (x : ℚ) => (x : ℝ)) := by',
        '  norm_num [sample, Adversarial.domain, InBox, Interval.Mem, List.replicate_succ, List.forall₂_cons]',
        'theorem features_match_checkpoint : z = features sample := by decide +kernel',
        'theorem features_erased : z 1 = 0 ∧ z 3 = 0 := by decide +kernel',
        'theorem initial_head_bound : initialHead = ![' + qs(witness['initial_head']) + '] := by decide +kernel',
        'theorem calibration_matrix : (Calibration.ops 0).matrix =',
        '    (NetworkRetention.calibrate z target rate).matrix := by decide +kernel',
        'theorem calibration_offset : (Calibration.ops 0).offset =',
        '    (NetworkRetention.calibrate z target rate).offset := by decide +kernel',
        'theorem actual_delta_rule (x : Vector 5) (i : Fin 5) :',
        '    (Calibration.ops 0).apply x i =',
        '      x i + rate * (target - ∑ j, x j * z j) * z i := by',
        '  have h := NetworkRetention.calibration_rule z target rate x i',
        '  simpa only [Affine.apply, ← calibration_matrix, ← calibration_offset] using h',
        'def afterHead : Vector 5 := (Calibration.ops 0).apply initialHead',
        'def loss (x : Vector 5) : ℚ := (score z x - target)^2 / 2',
        'theorem nontrivial_calibration : afterHead 2 ≠ initialHead 2 := by decide +kernel',
        'theorem sample_loss_decreases : loss afterHead < loss initialHead := by decide +kernel',
        'theorem generated_state_dimension : Calibration.kept.card = 3 := by decide +kernel',
        'end Contribution.Reduction.UpdateSynthesis.CalibrationBinding', ''])


def replay(spec, initial=None):
    names, seed, ops = syn.read_spec(spec)
    keep, rounds = syn.retention(seed, ops)
    packed = syn.packed_ops(keep, ops)
    n = len(names)
    states = [[Q(0)]*n] + [[Q(i == j) for i in range(n)] for j in range(n)]
    states += [list(map(Q, values)) for values in itertools.product([-1, 1], repeat=n)]
    if initial is not None:
        states.append(initial)
    words = [word for length in range(5) for word in itertools.product(range(len(ops)), repeat=length)]
    checks = 0
    for state in states:
        for word in words:
            full, red = state[:], [state[i] for i in keep]
            for k in word:
                full, red = syn.apply(ops[k], full), syn.apply(packed[k], red)
            if red != [full[i] for i in keep]:
                raise AssertionError('Packed implementation differs on exact replay')
            checks += 1
    masks = [set(i for i, bit in enumerate(bits) if bit)
             for bits in itertools.product([False, True], repeat=n)]
    candidates = [mask for mask in masks if seed <= mask and syn.closed(mask, ops)]
    if not all(set(keep) <= mask for mask in candidates):
        raise AssertionError('Small-instance minimum disagrees with synthesis')
    return dict(retained=[names[i] for i in keep], rounds=rounds, states=len(states),
                words=len(words), exact_replays=checks, masks_enumerated=len(masks),
                closed_supersets_of_seed=len(candidates))


def input_controls(spec):
    cases = {}
    bad = copy.deepcopy(spec); bad['coordinates'][1] = bad['coordinates'][0]; cases['duplicate_coordinate'] = bad
    bad = copy.deepcopy(spec); bad['seed'].append('missing'); cases['unknown_seed'] = bad
    bad = copy.deepcopy(spec); bad['operations'][0]['updates']['missing'] = {'terms': {}}; cases['unknown_destination'] = bad
    bad = copy.deepcopy(spec); bad['operations'][0]['updates']['a0'] = {'terms': {'missing': '1'}}; cases['unknown_source'] = bad
    bad = copy.deepcopy(spec); bad['operations'][0]['updates']['a0'] = {'terms': {'a0': .1}}; cases['float_coefficient'] = bad
    bad = copy.deepcopy(spec); bad['operations'][0]['updates']['a0'] = {'terms': {'a0': '1/0'}}; cases['zero_denominator'] = bad
    bad = copy.deepcopy(spec); bad['operations'][0]['updates']['a0'] = {'nonlinear': 'a0*a1'}; cases['nonlinear_expression'] = bad
    result = {}
    for name, sample in cases.items():
        try:
            syn.read_spec(sample)
        except (ValueError, ZeroDivisionError):
            result[name] = 'REJECTED'
        else:
            raise AssertionError('Invalid input accepted: ' + name)
    return result


def prepare(output, upstream):
    output.mkdir(parents=True, exist_ok=True)
    specs = {name: json.loads((HERE/'examples'/(name.lower()+'.json')).read_text())
             for name in ['Shifts', 'Coupling', 'Chain']}
    specs['Calibration'], witness = calibration(upstream)
    results, roots = {}, []
    for name, spec in specs.items():
        source, summary = syn.emit(spec, name)
        (output/(name+'.lean')).write_text(source)
        (output/(name+'.json')).write_text(json.dumps(spec, indent=2)+'\n')
        (output/(name+'.reduced.json')).write_text(json.dumps(summary, indent=2)+'\n')
        initial = list(map(Q, witness['initial_head'])) if name == 'Calibration' else None
        results[name] = replay(spec, initial)
        roots += summary['audit_roots']
    (output/'CalibrationBinding.lean').write_text(binding_source(witness))
    binding_roots = ['sample_in_domain', 'features_match_checkpoint', 'features_erased', 'initial_head_bound',
                     'calibration_matrix', 'calibration_offset', 'actual_delta_rule', 'nontrivial_calibration',
                     'sample_loss_decreases', 'generated_state_dimension']
    roots += ['Contribution.Reduction.UpdateSynthesis.CalibrationBinding.'+x for x in binding_roots]
    names, _, ops = syn.read_spec(specs['Calibration'])
    initial = list(map(Q, witness['initial_head']))
    updated = syn.apply(ops[0], initial)
    z = list(map(Q, witness['features'])); target = Q(witness['target'])
    score = lambda x: sum((a*b for a,b in zip(z,x)), Q(0))
    witness['before_score'] = str(score(initial)); witness['after_score'] = str(score(updated))
    witness['before_score_approx'] = float(score(initial)); witness['after_score_approx'] = float(score(updated))
    witness['before_loss'] = str((score(initial)-target)**2/2)
    witness['after_loss'] = str((score(updated)-target)**2/2)
    (output/'calibration_witness.json').write_text(json.dumps(witness, indent=2)+'\n')
    return dict(cases=results, calibration=witness, input_controls=input_controls(specs['Coupling']),
                generated_audit_roots=roots)
