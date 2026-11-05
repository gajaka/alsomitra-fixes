# Float32 rounding proof for the frozen Alsomitra network

This extends the universal Property2 proof by **deriving** its per-neuron error
budget from a specified arithmetic semantics. The weights, input region,
normalizer and Property2 thresholds are unchanged. The frozen network is the
same **untrained**, seed-20261105, `6 -> 64 -> 32 -> 1` model recorded in
`../universal/model.json`; this is not a theorem about every possible training
result or every real input outside the Property2 precondition.

Check `../results/rounding_verification.json` for the actual kernel-check result
and hashes. A `PASS` establishes the mathematical model below. **The universal
refinement of the installed PyTorch/Apple Accelerate implementation remains
NOT_PROVED.** No axiom identifying that implementation with the model is added.

## What is proved

`Rounding.lean` defines the finite binary32 value format as

```text
x = m * 2^e,  |m| < 2^24,  -149 <= e <= 104,  m,e integers.
```

This includes normal and subnormal values and zero, allowing redundant
representations. It omits NaNs, infinities and the sign of zero. `Nearest x y`
requires that `y` be a representable value minimizing distance to `x`; either
choice is allowed at a tie, so nearest-even is included. This is a mathematical
value semantics, not a verified implementation of a bit-level rounding routine.

For `|x| <= 32`, a representable grid point exists within `delta = 2^-19` of
`x`. Any nearest result is at least as close. The proof explicitly constructs
the grid witness; no empirical error estimate is used.

An expression can contain exact input atoms, rounded multiplication, rounded
addition, and fused multiply-add with one final rounding. Its mass is the sum
of the absolute values of its exact terms, and its cost counts rounded
operations. Structural induction proves:

```text
mass <= 16, cost <= 129, nearest rounding
    => every rounded operand is within [-32,32]
    => |rounded_expression - exact_expression| <= cost * 2^-19
    => error <= 129/524288 < 1/1024.
```

`RoundedNetwork.lean` requires each neuron expression to contain a permutation
of exactly its bias and all weight-times-input terms. Input dimensions must
match. This permits different addition trees, permutations and placements of
FMA. Counting these terms proves the operation bound; it is not a separately
assumed per-neuron error. Algorithms introducing other terms or arithmetic
operations need an additional refinement argument.

`KernelBounds.lean` checks exact rational range certificates over the entire
outer input box. In particular, each neuron's term mass is strictly below 3
in all three layers, including the propagated `1/1024` errors. The dependency
is inductive, not circular: input bounds justify first-layer rounding, those
rounded outputs justify second-layer rounding, and then the third layer.

`FrozenRounding.lean` proves that such executions satisfy the previous `Trace`
relation, then applies the already-checked 99-leaf universal certificate:

```text
forall r, xs, ys,
  CorrectRounding r
  and InBox exactBox xs
  and RoundedNetwork r network xs ys
  imply every y in ys satisfies y <= 256337/524288 < 1/2.
```

`property2_rounded` restates this using the original Property2 precondition
and exact physical readout `181/1000 + (12/1000)*y <= 187/1000`.
`rounded_observed_satisfied` links decoded output bits back to the existing
monitor, provided their execution is related to this arithmetic semantics.
This does not itself verify floating-point input normalization or materialized
physical-output arithmetic outside that specification.

The semantics is inhabited: `RoundingExistence.lean` proves that a nearest
value exists, and `ReductionExistence.lean` constructs both separated and FMA
sequential expressions for every correctly shaped input. The final file also
proves that an execution has exactly one output and gives an admissible-input
witness satisfying the property. The semantic choice function is noncomputable
and is not presented as a replacement executable kernel.

Four negative-control theorems prove that bad rounding, an insufficient error
budget, duplicated expression terms, and an invalid zero-neuron output are
rejected. The axiom audit allows only `propext`, `Classical.choice`, and
`Quot.sound`, including the imported universal proof dependencies.

## The remaining implementation obligation

The installed PyTorch is version 2.15.0, commit
`d0f2af8b66b20da4baa50644c0cd3f887a2eae2e`, built with Apple Accelerate BLAS.
Pinned source files and their license are in `sources/`, with URLs and SHA-256
hashes in `sources/manifest.json`. `Linear.cpp` routes these biased 2D calls
to `addmm`; `LinearAlgebra.cpp` and `CPUBlas.cpp` route supported CPU dimensions
to `sgemm_`.

`inspect_backend.py` confirms the runtime dispatch in a dedicated child process
using `trace_sgemm.c`. It records 9 calls for the three layers at batch sizes
1, 2 and 128, checks the resolved Accelerate library, and compares outputs with
an uninstrumented process. The diagnostic input is six values of `0.5`; it is
not asserted to satisfy the Property2 precondition. The observation confirms
batch-sensitive outputs, so a proof tied to just one summation order would
not justify all these executions. These observations are not universal proofs.

To transfer the theorem to the actual backend, it remains to establish for
every admitted input that its returned values refine `RoundedNetwork` for a
rounding function satisfying `CorrectRounding`. That includes the actual
reduction algorithm, primitive rounding behavior, handling of subnormals,
data movement and ReLU behavior. The pinned dispatch sources and nine observed
calls do not establish those facts about the internal Accelerate code.

PyTorch also documents floating-point ordering and batch differences in its
[numerical accuracy notes](https://docs.pytorch.org/docs/2.15/notes/numerical_accuracy.html).
Neither the original backend nor the trained status was changed to obtain
this arithmetic-model theorem.

## Reproduce

From the repository root, after the existing bridge and universal verifications:

```sh
/Users/gajaka/projects/ppg-lab/.venv/bin/python -B contribution/float32_kernel/verify.py
/Users/gajaka/projects/ppg-lab/.venv/bin/python -B contribution/float32_kernel/inspect_backend.py
```

The proof verifier checks prerequisite source/artifact hashes, regenerates the
range certificate, builds all seven new Lean modules and audits 42 theorem
roots. It records a separate result from the backend observation. It fails on
warnings, stale dependencies, nonstandard axioms, incomplete audits, or source
changes during verification. The backend probe targets this Mac's existing
Apple arm64 environment and uses its installed macOS 26.5 SDK for compilation.
