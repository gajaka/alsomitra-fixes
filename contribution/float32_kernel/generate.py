"""Generate numerical range certificates for the unchanged frozen network.

All proposed inequalities are checked by Lean's kernel, not trusted to Python.
"""
from fractions import Fraction as Q
import importlib.util
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
spec = importlib.util.spec_from_file_location('universal_generator', ROOT/'universal/generate.py')
universal = importlib.util.module_from_spec(spec)
spec.loader.exec_module(universal)


def generate():
    model = json.loads((ROOT/'universal/model.json').read_text())
    generation = json.loads((ROOT/'universal/generation.json').read_text())
    layers = universal.layers_from_manifest(model)
    box = [[Q(v) for v in pair] for pair in generation['cover_box']]
    ranges = universal.propagate(layers, box)
    # A whole-root range enclosure is enough for rounding error; the earlier
    # split-tree certificate remains responsible for the final output bound.
    maxima = []
    for ns, out in zip(layers, ranges):
        maxima.append(max(abs(b)+sum(abs(w)*max(abs(lo),abs(hi))
            for w,(lo,hi) in zip(ws,box)) for ws,b in ns))
        box = [(max(Q(0),a),max(Q(0),b)) for a,b in out]
    text = '''import RoundedNetwork
import FrozenModel
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Contribution.KernelBounds
open Contribution.Universal Contribution.Binary32 Contribution.Frozen
'''
    for name, bounds in zip(('firstRange','secondRange'),ranges[:2]):
        text += '\ndef '+name+' : List Interval := '+universal.intervals(bounds)+'\n'
    obligations = {
        'first_safe': 'SafeLayer first rootBox',
        'second_safe': 'SafeLayer second (reluBox firstRange)',
        'third_safe': 'SafeLayer third (reluBox secondRange)',
        'first_range': 'CheckLayer (1/1024) first rootBox firstRange',
        'second_range': 'CheckLayer (1/1024) second (reluBox firstRange) secondRange',
        'first_mass': '∀ n ∈ first, massBound n rootBox < 3',
        'second_mass': '∀ n ∈ second, massBound n (reluBox firstRange) < 3',
        'third_mass': '∀ n ∈ third, massBound n (reluBox secondRange) < 3',
    }
    for name, proposition in obligations.items():
        text += '\ntheorem '+name+' : '+proposition+' := by decide +kernel\n'
    text += '\nend Contribution.KernelBounds\n'
    (HERE/'KernelBounds.lean').write_text(text)
    return dict(state_sha256=model['state_sha256'],max_term_masses=list(map(str,maxima)),
                mass_bound=16,max_rounded_operations=129,
                local_rounding_bound='1/524288',neuron_error_bound='129/524288',
                required_neuron_budget='1/1024')


if __name__ == '__main__':
    print(json.dumps(generate(),indent=2))
