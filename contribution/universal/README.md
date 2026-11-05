# Universal Property2 certificate for the frozen Alsomitra network

This directory attempts a universal proof for the **same original AlsomitraNet
parameters used in the preceding float32 bridge**, without modifying the
weights, training a model, changing the Property2 thresholds, or treating
samples as proof. Inspect `../results/universal_verification.json`: only a
`PASS` for the current source hashes establishes completion of the checked
artifact described below.

## Fixed object and quantified claim

The frozen network has shape `6 -> 64 -> 32 -> 1`, with two hidden ReLU layers
and 2,561 parameters. These parameters are float32 bit patterns from the
original `examples.models.AlsomitraNet` initialized with seed `20261105`.
They are **untrained**. Its parameter-state SHA-256 is
`7c029e308980f34302fba366746c6a35455beaeb00c19a81d23c12c26c2fe988`.
The exporter checks this identity against the preceding bridge receipt.

`model.json` stores all bits, shapes, the original source hashes, normalization
bits and the fixed specification. `FrozenModel.lean` interprets every weight
and bias as an exact rational, then defines the affine/ReLU function over real
inputs. `parameters_decoded` checks in Lean that decoding all stored binary32
words gives exactly the exported parameter values. `parameters_bound` connects
that list to the network definition; `network_shape` checks the dimensions.
No native-decide axiom or unchecked solver result is used.

The property is the existing **anchor-relative Property2 with anchor = 10**:
all six physical coordinates lie in the original six-decimal domain,
`0 <= 10 + y <= 2`, `vy <= -3/10`, and `omega <= -3/25`. The input normalizer
uses the captured upstream float32 offsets and scales, interpreted exactly.
These are the same numeric meanings as in the preceding bridge.

For every real normalized input in this box, the exact network must satisfy:

```text
N(z) <= 1/2

and hence, in the specified physical output units:
181/1000 + (12/1000)*N(z) <= 187/1000.
```

This quantifies over the entire box, including its boundaries and irrational
real points. It is not restricted to tested inputs or to representable floats.
It does not quantify over other anchors, other weights, or retrained models.
`property2_region_nonempty` proves that the precondition has a witness.

## Proof construction

1. The existing proved Property2 compiler determines the exact normalized box.
2. A rational outer box encloses it. `root_encloses` checks all six inclusion
   inequalities. The initial domain is enlarged, never silently narrowed.
3. A binary split tree covers that box. Each child is obtained by clipping a
   parent interval at its split point. `bisect_covers` proves that every point
   belongs to at least one child; arbitrary lists with missing regions are
   not accepted as cover certificates.
4. Each leaf contains proposed intervals for every affine neuron in all three
   layers. Lean checks the lower and upper inequalities with exact rationals.
5. `dot_bounds`, `neuron_sound`, `layer_sound` and `relu_sound` prove these
   interval checks sound over real-valued executions.
6. `tree_sound` composes the leaf results and coverage proof. The final theorems
   connect this certificate back to the original Property2 predicate and to
   the existing bit-observation monitor.

The generated certificate has 99 leaves and 197 total tree nodes. There are
no uncovered gaps at split boundaries. Bounds are rounded **outward** to a
rational grid for compact certificate data; their inequalities are still
checked exactly. Python is a certificate producer: Lean's kernel checks each
leaf and the composition. The generator's floating-point behavior is not
trusted to establish the result.

`generation.json` records the largest final-neuron interval upper endpoint,
`256337/524288` (about `0.4889240265`). `all_approximate_bound` establishes this
uniform upper bound; `cap_lt_half` proves it is strictly below `1/2`.

## Exact execution and bounded-error execution are separate claims

The certificate is deliberately checked with a per-neuron affine-result
error budget `epsilon = 1/1024`. A `Trace network epsilon xs ys` allows every
neuron, independently, to return any value in:

```text
exact_affine_value(actual_previous_layer_values) +/- epsilon
```

ReLU is the exact real `max(0,x)` of the chosen affine result. The interval
proof propagates these errors through subsequent weights and activations;
it does not assume that small layer errors remain small without amplification.
The error budget is an explicit hypothesis chosen for this trace theorem,
not an estimate promoted to a universal fact about PyTorch.

- `all_exact_inputs` is unconditional for the defined exact real network.
- `all_approximate_inputs` covers every trace satisfying the error budget.
- `property2_exact` expresses the exact result in physical output units.
- `property2_approximate` expresses the bounded-error result in those units.
- `observed_satisfied` concludes that the existing float32 monitor returns
  `satisfied`, **if** the decoded output is connected to such a trace.

**A universal error bound for the actual PyTorch/BLAS backend is not proved.**
The subsequent [rounding proof](../float32_kernel/README.md) derives the
per-neuron budget for a specified nearest-rounding reduction semantics and
connects it to this certificate. The vendor implementation refinement remains
open; that extension does not identify Apple Accelerate with the semantics.
The trace hypothesis must be justified for that implementation before claiming
unconditional safety of all its float32 executions. These results do not
verify backend instruction selection, fused operations, summation order,
non-finite behavior or the hardware. There is no axiom asserting that PyTorch
satisfies the trace relation.

This separation is substantive: PyTorch documents that mathematical
rearrangements need not produce identical floating-point results in its
[numerical accuracy notes](https://docs.pytorch.org/docs/2.15/notes/numerical_accuracy.html).
The distinction between real-network verification and machine arithmetic
also appears in Jia and Rinard's
[Exploiting Verified Neural Networks via Floating Point Numerical Error](https://arxiv.org/abs/2003.03021).

## Reproduce and inspect

Use the same Lean 4.35.0 / pinned Mathlib setup in the parent `lean/` project
and the Python environment used for the float32 bridge:

```sh
# From the repository root; run the bridge verification first if absent/stale.
/Users/gajaka/projects/ppg-lab/.venv/bin/python -B contribution/universal/verify.py \
  --upstream /Users/gajaka/projects/ppg-lab/external/property-driven-ml
```

The checker regenerates the certificate from the frozen bits, rebuilds the
Lean modules, audits theorem dependencies and checks rejection of corrupted
certificates. It records source and artifact hashes and fails if sources
change during checking. The original model source must match the earlier
pinned receipt for the execution replay; no upstream files are edited.

The numerical proofs are in `FrozenLeaves.lean`; `FrozenCertificate.lean`
contains the short universal consequences, and `Property2Network.lean` binds
them to Property2. This separation permits a focused retry after editing a
consequence: `--reuse-build` reuses only successful kernel builds whose source,
dependency, compiled-artifact and Mathlib-manifest hashes, and toolchain
version, still match. It does not treat a successful Python interval
calculation as a proof.

`NegativeControls.lean` explicitly proves the negations of three corrupted
certificate claims: an incorrect output interval, missing second-layer neurons,
and an outer box omitting the admissible y region. A failed tactic or an
incomplete reduction alone is not counted as evidence that a claim is false.

`check_execution.py` replays the actual original network with the frozen
weights. It uses 64 corners and 64 deterministic interior inputs, compares
captured layer calls to the original `forward`, and evaluates each affine
expression independently with exact fractions. It checks 12,416 observed
neuron errors against the trace budget. These are **sampled consistency
checks**, not the justification of the universal trace hypothesis. A different
small demonstration model from the prior bridge is correctly rejected at a
concrete input; it cannot inherit this frozen network's certificate.

`../results/universal_verification.json` and the `universal_*.log` files contain
actual outcomes, including axiom lists for the three rejection theorems.
The allowed foundational axioms are `propext`, `Classical.choice`, and
`Quot.sound`. Kernel reduction (`decide +kernel`) is used for concrete proof
obligations; `native_decide` / `Lean.ofReduceBool` is not accepted by the audit.

The remaining trusted boundary includes the chosen specification, the
interpreted binary32 encoding, capture/export/provenance infrastructure,
Lean/Mathlib and their checking environment. No aerodynamic accuracy,
training success, C ABI, PPG/RR invariant, or repair-preservation claim follows
from this network-property certificate.
