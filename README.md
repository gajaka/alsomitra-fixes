# Alsomitra Property2: reproducing two implementation bugs

This package reproduces two bugs in the companion code for **A General
Framework for Property-Driven Machine Learning** and supplies a minimal local
correction. All upstream reproductions target the unchanged revision
`616df1e5baaabf7b42dc26320c00fb297903c87a` of
[property-driven-ml](https://github.com/tflinkow/property-driven-ml).

The main handoff is [upstream_property2.patch](upstream_property2.patch), a
two-file diff, together with the equivalent local classes in
[property2_patch.py](alsomitra_fixes/property2_patch.py). Both preserve the
framework's anchor-relative rectangular regions. The test runner never applies
the patch to the upstream checkout; a regression test applies it to temporary
copies and compares the result with the local correction.

An optional candidate-coupled region implementation and a real-number Lean
model are included separately. The coupled region changes the specification;
it is **not a third implementation bug** in the framework. No PPG code or
formal dependency is included.

Additional [formalization experiments](contribution/README.md) include an
executable exact-rational Property2 contract and proofs. They are separate
from the minimal upstream patch.

## 1. The two confirmed implementation bugs

### Swapped threshold arguments

`AlsomitraProperty2Constraint` passes these positional arguments:

```text
device, y_threshold, v_y_threshold, omega_threshold
```

The `AlsomitraProperty2` precondition expects:

```text
device, v_y_threshold, y_threshold, omega_threshold
```

With the defaults, this stores `v_y_threshold = 2.0` and
`y_threshold = -0.3`, instead of `-0.3` and `2.0`. The local correction uses
keyword arguments.

The resulting ordered `y` interval has its lower bound above its upper bound.
**This does not stop sampling.** Upstream computes
`rand * (hi - lo) + lo`, which still returns finite points between reversed
endpoints. Thus an infeasible ordered interval does not mean that the rule is
inactive. The tests explicitly exercise this behavior.

### Bounds normalized twice

Property2's `get_bounds` first computes physical bounds, normalizes them, and
then passes them to `apply_domain_bounds`. That helper expects physical bounds,
clips them to the physical domain, and normalizes them itself.

Even after fixing the constructor binding, the extra normalization gives the
wrong `y` interval. It also loses the intended upper caps on `v_y` and `omega`:
the returned upper bounds decode to the domain maxima, approximately `-0.043021`
and `0.049180`, rather than `-0.3` and `-0.12`.

The minimal correction removes the two premature normalization calls.
`apply_domain_bounds` then clips physical bounds and normalizes them once.
The output postcondition, output scale, sampler, attack implementation, and
Property1 defaults remain as in upstream.

### Use the minimal local correction

With this directory and the pinned upstream package on `PYTHONPATH`:

```python
import torch
from alsomitra_fixes.property2_patch import CorrectedAlsomitraProperty2Constraint

constraint = CorrectedAlsomitraProperty2Constraint(torch.device("cpu"))
# Use this in place of upstream AlsomitraProperty2Constraint.
```

To inspect whether the equivalent patch applies, without modifying upstream:

```sh
git -C /path/to/property-driven-ml apply --check /path/to/alsomitra-fixes/upstream_property2.patch
```

Derived source retains the upstream MIT notice in
[LICENSE.upstream](LICENSE.upstream).

## 2. Two different region specifications

Here an **anchor** is the original input around which the framework defines a
local region. A **candidate** is an input sampled or searched inside that region.

For corrected Property2, with a physical anchor `x0` and the upstream code's
`v_y` coordinate choice, the anchor-relative rectangle requires:

```text
0 <= x0 + y_candidate <= 2
v_y_candidate <= -0.3
omega_candidate <= -0.12
```

The candidate's `x` coordinate can vary independently. This matches the local
region approach in the framework paper, Section 4.2 and Appendix A.3,
Equations (23) and (25). Section 5.2 explicitly discusses the limitation of
hyperrectangles for coupled input conditions. The velocity-coordinate notation
in Equation (27) differs from the code; see Section 3 below.

The separate gliding-drone case study uses the candidate's own coordinates:

```text
0 <= x_candidate + y_candidate <= 2
```

These are different preconditions. A framework sample can satisfy its
anchor-relative rectangle while violating the candidate-coupled band. That
observation alone is not an implementation defect.

[alsomitra_fix.py](alsomitra_fixes/alsomitra_fix.py) provides the optional
candidate-coupled variant. Its historical `FixedAlsomitraProperty1*` and
`FixedAlsomitraProperty2*` names are retained, but should not be read as a claim
that this specification change is a required upstream fix.

The variant samples `x` first and `y` conditionally on that same `x`.
`get_bounds` returns only an axis-aligned envelope of the coupled region.
Independent sampling or an unadapted rectangular attack inside that envelope
would not enforce the band. Use the variant's sampler and, for upstream
PGD/APGD, its `AlsomitraAttackAdapter`:

```python
from alsomitra_fixes.alsomitra_fix import (
    AlsomitraAttackAdapter, FixedAlsomitraProperty2Constraint,
)

# N, normalized_inputs, targets, and oracle come from the existing application.
constraint = FixedAlsomitraProperty2Constraint(normalized_inputs.device)
adapter = AlsomitraAttackAdapter(oracle)
candidates = adapter.attack(N, normalized_inputs, targets, constraint)
```

The adapter searches unit-cube coordinates and decodes them into the coupled
region before evaluating the network. PGD supports float32/float64; upstream
APGD requires float32. The adapter requires `mean=0`, `std=1`, keeps the model
in evaluation mode during search, and restores its original module mode flags
even if an exception occurs. Tests run the actual upstream attacks on small
CPU models, rather than mocking their optimization loops.

Sequential sampling is not uniform by physical volume. Floating-point region
membership uses an explicit numerical tolerance; it is not a formal
certificate. These are declared local implementation choices.

The optional [normalization.py](alsomitra_fixes/normalization.py) helper freezes
statistics for a seed-42, 544/136 split of the 680-row dataset. Training
statistics and the declared physical domain are recorded separately, with
dataset and contract hashes. It is not required by the minimal two-bug patch.
It is not a general dataset loader: its shape, split, domain, and expected
output extrema are deliberately fixed and validated.

## 3. Questions about paper/code agreement

### Property1's theta bound

Upstream defaults to `theta_threshold = (-0.786, +0.747)`. After domain
clipping, its effective upper bound is about `-0.068003`. The framework paper's
Appendix A.3, Equation (24), and the drone paper's Equation (23), use the
negative upper bound `-0.747`.

This is documented as a specification discrepancy for the authors to clarify,
not a third confirmed implementation bug. The minimal patch does not change
it. The optional coupled Property1 variant explicitly selects the paper's
negative upper bound; callers can choose the interval explicitly.

### Property2's velocity coordinate

The framework paper's Appendix A.3, Equation (27), writes `movingFast` as
`v_x' <= -0.3`, while the
[pinned precondition code](https://github.com/tflinkow/property-driven-ml/blob/616df1e5baaabf7b42dc26320c00fb297903c87a/src/property_driven_ml/constraints/preconditions.py#L338-L339)
constrains `v_y`. The paper's input-domain table gives a strictly positive
range for `v_x'` (approximately `0.967568` to `3.489893`), so the printed
inequality cannot hold within that domain. This discrepancy appears in the
[PDF, page 18](https://arxiv.org/pdf/2505.00466v2#page=18), as well as the
[HTML appendix](https://arxiv.org/html/2505.00466v2).

The separate [drone case study](https://arxiv.org/html/2505.00622v1),
Equation (24), uses `x_2 <= -0.3`, the second input component (local
`y`-velocity). This supports the code's `v_y` choice. A typographical error in
the framework equation is a plausible explanation, but author intent has not
been confirmed.

The minimal patch preserves the upstream code's `v_y` coordinate and fixes
argument binding and normalization. It does not change the velocity coordinate
to match Equation (27) literally, or classify this paper/code discrepancy as
another confirmed implementation bug.

## 4. Run the Python checks

Requirements: Python 3.11 or newer, Git, and `torch`, `numpy`, `pandas`, `pytest`.
Use an existing compatible environment and a clean upstream checkout:

```sh
git clone https://github.com/tflinkow/property-driven-ml
git -C property-driven-ml checkout 616df1e5baaabf7b42dc26320c00fb297903c87a
```

From this package's root:

```sh
python run_python_tests.py --upstream /path/to/property-driven-ml
```

The runner checks the exact Git root and revision, tracked-file cleanliness,
added Python package sources (including ignored additions), and actual import
origins before testing and again afterward. Probes and tests use the same
interpreter and explicit package search path. This is provenance evidence,
not a sandbox for arbitrary Python execution.

The runner exits nonzero for a failed provenance check, a failed/empty test
run, or any non-passing test. It writes fresh CSV files:

- `results/python_tests.csv`: individual test outcomes and timings.
- `results/python_run_info.csv`: generated local log, excluded from Git. It
  records environment, pre/post provenance, imported source paths and SHA-256
  hashes, totals, and final `run_status`. Each run recreates it on that machine.

| Test file | What it checks |
| --- | --- |
| `test_property2_bugs.py` | Both upstream bugs; the minimal correction; patch application in a temporary directory; the distinction between rectangular and coupled regions; the theta discrepancy. |
| `test_local_variants.py` | Coupled geometry, corners, degenerate intervals, projection, encode/decode, autograd, actual PGD/APGD, and restoration of model state. |
| `test_normalization.py` | Frozen split/statistics, float32 dataset bytes, RNG isolation, serialization, metadata tampering, and physical/normalized thresholds. |
| `test_lean_model_correspondence.py` | Sampled agreement between handwritten Python transcriptions of model formulas and the actual implementations. |
| `test_python_runner.py` | Negative controls for checkout provenance, imports, and stale/failed/incomplete test reporting. |
| `test_lean_audit_runner.py` | Negative controls for failed/partial Lean audits, diagnostics, root coverage, and forbidden axioms. |

The correspondence tests do **not** execute or parse the Lean definitions.
They compare manually transcribed Python formulas with Python implementations;
a Lean-only change would not automatically be detected by those tests.

## 5. Optional Lean model

[lean/README.md](lean/README.md) lists the 12 audited theorem roots, their
scope, and the independent build command. The model proves real-arithmetic
facts about the argument swap, double normalization, the two region
specifications, and the theta interval discrepancy.

Lean proves statements about that model. This original bug-fix formalization
does not provide a formally verified Python-to-Lean translation, floating-point semantics,
end-to-end training correctness, trained-network guarantees, or evidence of
an effect on the paper's experimental results. No independent second-kernel
proof replay is included.

The separate [formalization experiments](contribution/README.md) cover bit
observation and a universal frozen-network proof under an explicit rounding
semantics. They do not prove the actual PyTorch/Apple Accelerate backend correct.

## 6. References and property numbering

**Framework paper:** Thomas Flinkow, Marco Casadio, Colin Kessler, Rosemary
Monahan, and Ekaterina Komendantskaya. *A General Framework for Property-Driven
Machine Learning*. arXiv:2505.00466v2 (2025).
[Paper](https://arxiv.org/abs/2505.00466v2),
[full text](https://arxiv.org/html/2505.00466v2),
[DOI](https://doi.org/10.48550/arXiv.2505.00466).

**Drone case study:** Colin Kessler, Ekaterina Komendantskaya, Marco Casadio,
Ignazio Maria Viola, Thomas Flinkow, Albaraa Ammar Othman, Alistair Malhotra,
and Robbie McPherson. *Neural Network Verification for Gliding Drone Control:
A Case Study*. arXiv:2505.00622v1 (2025).
[Paper](https://arxiv.org/abs/2505.00622v1),
[full text](https://arxiv.org/html/2505.00622v1),
[DOI](https://doi.org/10.48550/arXiv.2505.00622).

| Code name | Framework paper | Drone case study |
| --- | --- | --- |
| `AlsomitraProperty1Constraint` | Intermediate-pitch property, `phi_2`, Eq. (15) | Property 3, Eq. (23); coupled coordinates |
| `AlsomitraProperty2Constraint` | Pitching-and-moving property, `phi_3`, Eq. (16) | Property 4, Eq. (24); coupled coordinates |

The numbering correspondence does not make the local and global preconditions
identical. The confirmed bugs concern the implementation of the framework's
Property2 at the pinned source revision. Current upstream fixes or prior
reports have not been surveyed. BibTeX entries are in
[REFERENCES.bib](REFERENCES.bib).
