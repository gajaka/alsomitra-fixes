"""Synthesize a coordinate projection and emit a kernel-checkable Lean witness.

The input language is finite rational affine assignments, executed simultaneously.
Unassigned coordinates retain their values. The Python reader/emitter is an
adapter; Lean checks the emitted literal system and the packed implementation.
"""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re


def rational(value):
    if isinstance(value, bool) or not isinstance(value, (str, int)):
        raise ValueError('Coefficients must be exact strings or integers')
    return Q(value)


def read_spec(spec):
    names = spec['coordinates']
    if not isinstance(names, list) or not names or len(set(names)) != len(names):
        raise ValueError('Coordinate names must be nonempty and distinct')
    if any(not isinstance(x, str) or not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', x) for x in names):
        raise ValueError('Invalid coordinate name')
    seed = spec['seed']
    if not isinstance(seed, list) or len(seed) != len(set(seed)) or not set(seed) <= set(names):
        raise ValueError('Invalid seed')
    n = len(names)
    ops = []
    if not isinstance(spec['operations'], list) or not spec['operations']:
        raise ValueError('Supply at least one operation')
    for op in spec['operations']:
        matrix = [[Q(i == j) for j in range(n)] for i in range(n)]
        offset = [Q(0)] * n
        updates = op['updates']
        if not set(updates) <= set(names):
            raise ValueError('Unknown destination coordinate')
        for dst, expression in updates.items():
            if set(expression) - {'terms', 'constant'}:
                raise ValueError('Only rational affine expressions are supported')
            terms = expression.get('terms', {})
            if not isinstance(terms, dict) or not set(terms) <= set(names):
                raise ValueError('Unknown source coordinate')
            i = names.index(dst)
            matrix[i] = [rational(terms.get(src, 0)) for src in names]
            offset[i] = rational(expression.get('constant', 0))
        ops.append((matrix, offset))
    return names, {names.index(x) for x in seed}, ops


def retention(seed, ops):
    keep = set(seed)
    rounds = [sorted(keep)]
    while True:
        expanded = keep | {j for matrix, _ in ops for i in keep
                           for j, coefficient in enumerate(matrix[i]) if coefficient}
        if expanded == keep:
            return sorted(keep), rounds
        keep = expanded
        rounds.append(sorted(keep))


def closed(keep, ops):
    return all(not a or j in keep for matrix, _ in ops for i in keep
               for j, a in enumerate(matrix[i]))


def apply(op, state):
    matrix, offset = op
    return [sum((a*x for a, x in zip(row, state)), Q(0)) + b
            for row, b in zip(matrix, offset)]


def packed_ops(keep, ops):
    return [([[matrix[i][j] for j in keep] for i in keep], [offset[i] for i in keep])
            for matrix, offset in ops]


def qlean(x):
    return f'(mkRat ({x.numerator}) {x.denominator})'


def vector(items):
    return '![' + ', '.join(items) + ']'


def affine(op):
    matrix, offset = op
    return '⟨' + vector([vector([qlean(x) for x in row]) for row in matrix]) + ', ' + \
        vector([qlean(x) for x in offset]) + '⟩'


def finset(xs):
    return '{' + ', '.join(map(str, sorted(xs))) + '}' if xs else '∅'


def emit(spec, namespace):
    if not re.fullmatch(r'[A-Z][A-Za-z0-9_]*', namespace):
        raise ValueError('Invalid Lean namespace')
    names, seed, ops = read_spec(spec)
    keep, rounds = retention(seed, ops)
    if not keep:
        raise ValueError('This prototype emitter requires a nonempty retained set')
    reduced = packed_ops(keep, ops)
    n, m, r = len(names), len(ops), len(keep)
    lines = ['import NetworkRetention', '',
        'set_option autoImplicit false', 'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 0',
        'namespace Contribution.Reduction.UpdateSynthesis.' + namespace,
        'open AffineRetention',
        f'def seed : Finset (Fin {n}) := {finset(seed)}',
        f'def kept : Finset (Fin {n}) := {finset(keep)}',
        f'def ops : Fin {m} → Affine {n} := ' + vector([affine(op) for op in ops]),
        f'def packedOps : Fin {m} → Affine {r} := ' + vector([affine(op) for op in reduced]),
        f'def order : Fin {r} → Fin {n} := ' + vector(list(map(str, keep))),
        f'def pack (x : Vector {n}) : Vector {r} := fun i => x (order i)',
        'theorem computed : synthesize ops seed = kept := by decide +kernel',
        'theorem kept_closed : Closed ops kept := by',
        '  rw [← computed]; exact (synthesize_spec ops seed).2.1',
        'theorem seed_retained : seed ⊆ kept := by',
        '  rw [← computed]; exact (synthesize_spec ops seed).1',
        f'theorem packed_commutes (k : Fin {m}) (x : Vector {n}) :',
        '    pack ((ops k).apply x) = (packedOps k).apply (pack x) := by',
        '  fin_cases k',
        '  all_goals',
        '    funext i',
        '    fin_cases i',
        '    all_goals simp [pack, order, ops, packedOps, Affine.apply, Fin.sum_univ_succ]',
        f'theorem packed_sequence (word : List (Fin {m})) (x : Vector {n}) :',
        '    pack (run ops word x) = run packedOps word (pack x) := by',
        '  induction word generalizing x with',
        '  | nil => rfl',
        '  | cons k ks ih => simp only [run, ih, packed_commutes]',
        f'theorem minimal (other : Finset (Fin {n})) (hs : seed ⊆ other)',
        f'    (red : Fin {m} → Reduced other → Reduced other)',
        '    (hf : ∀ k x, project other ((ops k).apply x) = red k (project other x)) :',
        '    kept ⊆ other := by rw [← computed]; exact synthesis_minimal ops seed other hs red hf',
        f'theorem stable (word : List (Fin {m})) :',
        '    Stable (run ops word) (observableAlgebra kept) := algebra_stable_run ops kept kept_closed word']
    roots = ['computed', 'kept_closed', 'seed_retained', 'packed_commutes',
             'packed_sequence', 'minimal', 'stable']
    if names == ['a0', 'a1', 'a2', 'a3', 'bias'] and {0, 2, 4} <= seed:
        idx = [keep.index(i) for i in [0, 2, 4]]
        lines += [
            f'def packedOutput (input : OutputUpdates.Input) (x : Vector {r}) : ℝ :=',
            f'  OutputUpdates.reducedOutput (input, ⟨x {idx[0]}, x {idx[1]}, x {idx[2]}⟩)',
            'theorem output_factors (input : OutputUpdates.Input) (x : Vector 5) :',
            '    NetworkRetention.output input x = packedOutput input (pack x) := by',
            '  exact OutputUpdates.output_factors (input, NetworkRetention.head x)',
            f'theorem network_sequence (input : OutputUpdates.Input) (word : List (Fin {m}))',
            '    (x : Vector 5) :',
            '    NetworkRetention.output input (run ops word x) =',
            '      packedOutput input (run packedOps word (pack x)) := by',
            '  rw [output_factors, packed_sequence]']
        roots += ['output_factors', 'network_sequence']
    lines += ['end Contribution.Reduction.UpdateSynthesis.' + namespace, '']
    summary = dict(coordinates=names, retained=[names[i] for i in keep], indices=keep,
                   closure_rounds=[[names[i] for i in row] for row in rounds],
                   full_dimension=n, reduced_dimension=r,
                   operations=[dict(matrix=[[str(x) for x in row] for row in matrix],
                                    offset=list(map(str, offset))) for matrix, offset in reduced],
                   audit_roots=['Contribution.Reduction.UpdateSynthesis.' + namespace + '.' + x for x in roots],
                   scope='Least coordinate projection containing seed, for all rational states and given affine operations')
    return '\n'.join(lines), summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('spec', type=Path)
    parser.add_argument('--output-dir', required=True, type=Path)
    parser.add_argument('--name', default='Generated')
    args = parser.parse_args()
    spec = json.loads(args.spec.read_text())
    source, summary = emit(spec, args.name)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    source_path = args.output_dir / (args.name + '.lean')
    report_path = args.output_dir / (args.name + '.json')
    if source_path.exists() or report_path.exists():
        parser.error('Output files already exist; choose a fresh output directory/name')
    source_path.write_text(source)
    summary['input_sha256'] = hashlib.sha256(args.spec.read_bytes()).hexdigest()
    summary['lean_sha256'] = hashlib.sha256(source.encode()).hexdigest()
    summary['proof_status'] = 'NOT_RUN'
    report_path.write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(dict(retained=summary['retained'], lean=str(source_path), proof_status='NOT_RUN'), indent=2))


if __name__ == '__main__':
    main()
