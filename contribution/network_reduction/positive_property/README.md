# Positive robustness certificates for published DL2 and Gödel models

This experiment connects a **true property of a published trained network**
to exact neuron removal and property transfer. It uses two additional
checkpoints, not the smaller Baseline/Adversarial networks whose Above(2)
and Below(2) properties were refuted in `../property_decision/`.

## Exact statement

Let `f` denote either original ONNX network interpreted over the reals,
with every finite binary32 weight decoded to its exact rational value.
For every pair of real six-dimensional inputs:

```text
|x_i - y_i| <= d for every i, d >= 0
    ==> |f(x) - f(y)| <= K*d

DL2:   K = 31
Godel: K = 26
```

In particular, for `epsilon = 1/1000`, the output change is at most
`31/1000` or `26/1000`. These imply the network-to-network form of
Property 5 in section 7.2 of the companion Alsomitra paper at the
published Table 2 parameter pair `epsilon = 0.001`, `Lstar = 0.0001`:

```text
forall x,y in [0,1]^6,
  (forall i, |x_i-y_i| <= 0.001)
    ==> |f(x)-f(y)| <= Lstar/epsilon = 0.1.
```

This covers **all anchors in the cube and all allowed perturbations**.
It is not a finite test over the dataset. A separate theorem supplies
distinct, strictly interior inputs satisfying the premise. The global
bound on the original network holds outside the cube as well; the
pruning and transferred result are restricted to the cube.

`Lstar` is the parameter in the paper's quotient threshold, **not** the
actual Lipschitz constant `K`. This result does not prove a Lipschitz
constant of `0.0001`. `property5_two_sided` proves the correspondence
with the two output inequalities used in the Vehicle source. The source's
`LipschitzRobustness` compares network outputs; the different
`standardRobustness` can refer to externally supplied training labels.
We do not conflate those requirements.

## Source and meaning

The pinned source is
[SAIV_2025_Alsomitra](https://github.com/ckessler2/SAIV_2025_Alsomitra/tree/e9f6f1c52e0e5349455d2b4f69c2015567d3037f):

- `vehicle_verification/property_verification_2/DL2_Lipschitz.onnx`.
- `vehicle_verification/property_verification_2/GD_Lipschitz.onnx`.
- `vehicle_verification/property_verification/Alsomitra_Robustness.vcl`.
- `docs/paper/Paper_Arxiv.md`, sections 6 and 7.2, Table 2.

The filenames identify the archived DL2/Gödel Lipschitz models. Their
training is not rerun here, and the repository does not provide a
checkpoint-specific training receipt linking every hyperparameter to these
bytes. We therefore certify these exact published files; we do not claim
to reproduce an entire training experiment, the models for the other
properties in Table 1, or the outcome of future training runs.

The architecture is `6 -> 64 -> 32 -> 1`, with ReLU after the two hidden
layers and a **linear output**. `extract.py` checks all ONNX graph edges,
operator types, Gemm attributes, shapes, finite float32 parameters, pinned
SHA-256 hashes and Git blobs. The declared coordinates are already
normalized. No physical-unit conversion is inserted into the theorem.

## Certificate and reduction

The sensitivity certificate uses the standard absolute-weight bound:

```text
c0 = (1,1,1,1,1,1)
c1 = |W1| c0
c2 = |W2| c1
c3 = |W3| c2
```

ReLU is nonexpansive and biases cancel in differences. `Lipschitz.lean`
proves that every accepted rational bound implies the real inequality.
The exact path bounds are approximately `30.332954861` and
`25.385532149`, respectively. The checker is conservative; these are not
claimed to be optimal Lipschitz constants or a new bounding method.

Both models also admit removal of first-layer neuron 58 (zero-based)
through the existing interval certificate. Their certified reduction is:

```text
6-64-32-1 (2,561 parameters) -> 6-63-32-1 (2,522 parameters)
```

`LinearPruning.lean` reuses the earlier certificate and proof lemmas for
the correct linear-output semantics. Lean checks exact equality on
`[0,1]^6`, then transfers the positive two-input property. The smaller
ONNX exports have their parameter bits checked against this formal pruning.
The reduction is modest: 39 parameters, about 1.52%; no speedup is claimed.

```text
Pinned trained checkpoint
          |
          +--> exact parameter interpretation --> universal robustness
          |
          +--> checked inactive-neuron removal --> identical function on cube
                                                      |
                                                      v
                                            robustness of reduced model
```

## Checks and reproduction

From the repository root, using a Python environment containing NumPy,
ONNX and ONNX Runtime, and the repository's pinned Lean/Mathlib installation:

```sh
python contribution/network_reduction/positive_property/verify.py \
  --upstream /path/to/SAIV_2025_Alsomitra
```

The runner regenerates models and certificates from pinned input bytes,
compares the generated Lean files byte-for-byte, rebuilds the local proof
dependencies in a fresh attempt directory, audits theorem axioms and checks
deliberately false bounds and incorrect deletion masks. It accepts only
`propext`, `Classical.choice` and `Quot.sound`; it rejects warnings,
`sorryAx`, native-decision axioms and omitted audit roots. Parser controls
are inherited from the existing strict audit harness. It also runs finite
ONNX execution checks and saves a new, separate receipt:

`contribution/results/positive_property_verification.json`.

The attempt directory contains source snapshots, generated ONNX files,
extraction hashes, compilation logs and `RUNTIME.json`. Earlier receipts
and their proof files are preserved. This is a Lean kernel audit; no second
independent kernel or independent human review is claimed.

## Evaluation and limitations

Finite execution checks include 360 published normalized data rows,
64 corners, and 2,048 dyadic anchor/perturbation pairs, both one-row and
batched evaluation. Dataset error is descriptive on these 360 rows.
We do not know a held-out split for these archived checkpoints, so it is
**not a test-set/generalization score** and does not establish acceptable
closed-loop control quality. An in-sample best-constant comparator and
prediction range help expose a degenerate constant-output solution;
neither checkpoint is retrained or changed to obtain the property.

The proof is about real affine arithmetic with exact checkpoint constants.
It does not prove a bound for every PyTorch/ONNX float32 execution, all
normalization paths, physical reachability, trajectory tracking, stability
or flight safety. Differences between original and smaller float32
executions are recorded separately. The 0.1 threshold is one of the
paper's parameters; its engineering adequacy and tighter thresholds remain
separate questions.

The contribution here is a reproducible, kernel-checked positive instance
and its certified reduction. It supplies one verification stage after
property-driven training; it does not prove that the training objective
caused the property or that the full controller satisfies all requirements.
