# Formalization experiments

This directory contains exploratory Lean models, executable checkers, and
verification scripts for Alsomitra properties. The minimal upstream bug fix
is documented separately at the repository root.

## Verified controller repair

The [repair walkthrough](model_repair/directed_repair/README.md) follows an
initial violation through fitting, an explicit six-ReLU output correction,
universal directional proofs and exact reference-quality checks. Initial and
final ASCII networks and a step-by-step code/definition/check table make the
construction reviewable. Its 3.73% lower MSE is measured on the 360 fitting
rows. The directional guarantee applies to the complete core-plus-block
controller. [Reproduction commands](model_repair/README.md) verify the frozen
candidate without retraining.

## Certified network reduction

Start with [Can a Smaller Network Keep Its Promise?](network_reduction/NETWORK_REDUCTION.pdf),
an example-led guide with explicit input/output requirements, concrete states,
RR and the observable subalgebra. The [source and reproduction guide](network_reduction/README.md)
links the Lean proofs, checkpoint adapters and recorded checks.

Two published DL2/Gödel checkpoints satisfy the stated robustness implication
for all permitted real input pairs. Exact reduction preserves that guarantee
and reduces each model from 2,561 to 2,522 parameters. Separate examples cover
Baseline/Adversarial reductions and counterexamples, compatible parameter
updates, momentum-state reduction and an equal-history RMSProp invariant.
The guide distinguishes these claims from finite float32 execution checks.

## Specification compilation

The [spec_compiler experiment](spec_compiler/README.md) proves preservation of
Boolean input regions, strict boundaries and positive affine normalization,
with an executable rational checker and a bridge to the existing Alsomitra
contract. It also distinguishes exact membership from the supported
continuous zero-loss semantics.

The [ACAS Xu example](spec_compiler/acas/README.md)
([PDF guide](spec_compiler/acas/ACAS_CHECKER.pdf)) applies the checker to
Equations (7) and (8) in the paper, with explicit states, counterexamples,
and a proof that corrected bounds preserve the source input condition.

The [research assessment](spec_compiler/RESEARCH_ASSESSMENT.md) records strong
overlap with Vehicle/LDL: technical feasibility is established by the checked
artifact; a novel standalone research contribution is not established.
See [the verification result](results/region_compiler_verification.json) for
the actual proof and runtime outcomes.

## Executable contract for Alsomitra Property2

The first implementation gives the existing anchor-relative Property2 an
exact-rational contract. **The functions proved about in Lean are the same
functions executed by the demonstration.** There is no second handwritten
Python implementation standing in for the formal core.

It covers all six coordinates, named thresholds, arbitrary positive affine
input normalizers, region compilation, empty-region detection, candidate
generation, inverse coordinates, and a three-way input/output monitor.

This closes the model/execution gap for this **new Lean rational core**.
The next implementation connects it to observed PyTorch float32 bits; it does
not prove all PyTorch arithmetic or a network correct for every input.
The original fixes and their tests remain independent and unchanged.

## PyTorch / float32 bridge

[FLOAT32_BRIDGE.md](FLOAT32_BRIDGE.md) defines the exact bit interpretation,
candidate acceptance gate, two distinct numerical observations, and provenance
receipts. [Float32.lean](Float32.lean) adds eight proved theorem roots;
[torch_bridge.py](torch_bridge.py) captures actual tensor bits and invokes the
executable Lean checker. An optional integration executes the original
`AlsomitraNet` and denormalizers with deterministic, untrained weights.

```sh
# Use a Python environment with PyTorch; also reruns the rational baseline.
python -B contribution/verify_float32.py
# Add: --upstream /path/to/property-driven-ml to exercise the pinned original.
python -B contribution/torch_bridge.py
```

The bridge reproduces a boundary case accepted by a rounded PyTorch comparison
but rejected by the exact normalized-output contract. These are explicitly
different numerical meanings. See
[results/float32_verification.json](results/float32_verification.json) for the
latest actual checks and their scope.

## Universal certificate for the frozen network

[universal/README.md](universal/README.md) describes the next step: a Lean
interval certificate covering every real input in the fixed Property2 region
with `anchor = 10`. It uses the same 2,561 frozen, untrained AlsomitraNet
parameters as the float32 integration. It also states a separate universal
claim for executions with an explicit per-neuron error budget.

```sh
python -B contribution/universal/verify.py --upstream /path/to/property-driven-ml
```

The checker verifies the 99-leaf cover, every interval inequality, parameter
decoding, and the connection to the original predicate. Inspect
[results/universal_verification.json](results/universal_verification.json)
for the completed proof status and matching source hashes. The numerical
error budget for **all actual PyTorch executions** remains an unproved backend
obligation; sampled error measurements are reported separately.

## Deriving the rounding budget

[float32_kernel/README.md](float32_kernel/README.md) derives the per-neuron
budget from finite-binary32 nearest rounding, with separated operations,
different addition trees and FMA. The 42 new audited theorem roots connect
that arithmetic semantics to the frozen network's universal Property2 proof.
The measured backend is Apple Accelerate; its universal refinement into this
semantics remains unproved. Neither sampled execution nor source dispatch is
treated as such a refinement proof.

```sh
python -B contribution/float32_kernel/verify.py
python -B contribution/float32_kernel/inspect_backend.py
```

See [results/rounding_verification.json](results/rounding_verification.json)
for the checked mathematical result and
[results/float32_backend_observation.json](results/float32_backend_observation.json)
for the separately recorded runtime observations.

## Read and run

1. [SPECIFICATION.md](SPECIFICATION.md) defines every input, predicate,
   transformation, theorem obligation, and trust boundary.
2. [Property2.lean](Property2.lean) contains the executable definitions and proofs.
3. [Main.lean](Main.lean) and [Protocol.lean](Protocol.lean) expose them through
   a JSON-lines adapter.
4. [RESEARCH_PLAN.md](RESEARCH_PLAN.md) distinguishes this first result from
   the remaining implementation and research questions.
5. [results/verification.json](results/verification.json) records the latest
   verification outcome and source hashes; inspect its status before citing it.

Use the existing parent project's Lean 4.35.0 and pinned Mathlib setup:

```sh
# From the repository root; Python's standard library is sufficient.
python3 -B contribution/verify.py
```

The runner recompiles this directory's Lean sources, audits all 19 theorem
roots, checks rejection of a typed double-normalization attempt, and compares
the actual executable against independent Python `Fraction` predicates.
It also checks that malformed/incomplete axiom reports are rejected.

It reuses the dependencies installed for `lean/`; it does not modify the
parent Lean library or require an upstream Python checkout. If those
dependencies are absent, follow [the parent Lean setup](../lean/README.md).

After verification, an interactive example from the repository root is:

```sh
cd lean
LEAN_PATH="../contribution/.build" lake env lean --run ../contribution/Main.lean <<'JSON'
{"action":"bounds","anchor":"10"}
{"action":"sample","anchor":"10","unit":["1/2","1/2","1/2","1/2","1/2","1/2"],"output":"1/2"}
{"action":"sample","anchor":"10","band_upper":"-3/10","velocity_upper":"2","unit":["1/2","1/2","1/2","1/2","1/2","1/2"]}
JSON
```

The first request reports physical `y` bounds `[-10,-8]`, `vy <= -3/10`,
and `omega <= -3/25`. The second gives an in-region candidate and a
`satisfied` verdict at the exact output boundary. The third reproduces the
swapped-default configuration and returns `rejected` / `empty_region`.

Rational inputs are JSON strings such as `"10"` or `"-3/10"`; JSON numeric
values, decimal strings, zero denominators, and non-finite spellings are
rejected. The order of vector components is always
`[vx, vy, omega, theta, x, y]`. The protocol is detailed in the specification.

## Evidence and scope

The 19 theorem roots cover the exact mathematical contract for **all rational
inputs satisfying their hypotheses**. Runtime checks cover selected boundary,
interior, degenerate, malformed, and regression cases. The latter are not a
substitute for universal theorems or a formal proof of the JSON parser.

The runner writes readable audit logs and the summary under `results/`.
Generated Lean artifacts, emitted C, and the request/response transcript live
under ignored `.build/`. Emitted C is a compiler artifact, not a verified C ABI
or a standalone `libppgraph` deliverable. Execution currently uses Lean's runner.

There is no trained-network proof, training run, PPG graph, hazard calculus,
RR equivalence, or stable-subalgebra claim in this rational core.

## Sources

- Flinkow et al., [A General Framework for Property-Driven Machine Learning,
  arXiv:2505.00466v2](https://arxiv.org/html/2505.00466v2), particularly
  Sections 3 and 5.2 and Appendix A.3.
- [Upstream preconditions at revision 616df1e](https://github.com/tflinkow/property-driven-ml/blob/616df1e5baaabf7b42dc26320c00fb297903c87a/src/property_driven_ml/constraints/preconditions.py).
- Flinkow, Pearlmutter, Monahan, [Comparing differentiable logics for learning
  with logical constraints, arXiv:2407.03847v2](https://arxiv.org/html/2407.03847v2),
  Section 5.2, for inference monitoring and preservation under retraining.

The upstream six-decimal domain constants and the code's `vy` coordinate are
retained deliberately. The paper/code discrepancies are explained in the
[repository README](../README.md). Upstream attribution is retained in
[LICENSE.upstream](../LICENSE.upstream). Novelty relative to existing contract
compilers and differentiable-logic formalizations has not been established.
