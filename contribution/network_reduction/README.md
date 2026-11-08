# Certified reduction of trained networks

Start with **Can a Smaller Network Keep Its Promise?**, available as
[PDF](NETWORK_REDUCTION.pdf) and [editable source](REPORT.md).
The [interactive graph and PDF viewer](https://gajaka.github.io/alsomitra-fixes/)
lets you trace questions, assumptions, insights, and evidence back to their
source passages. See the [viewer controls](research_graph/README.md).

The guide begins with explicit `P -> Q` definitions and a pair of nearby
inputs. It follows the guarantee through actual checkpoint reduction,
then uses two concrete states to explain RR, compatible updates and the
observable subalgebra. Worked momentum and RMSProp examples show why
optimizer memory matters. Each new concept is introduced where needed;
proof locations, exact models and reproduction details follow in appendices.

The [equal-history RMSProp extension](rmsprop_symmetric/README.md) proves
exact reduced execution on its invariant state space. The separate
[property-transfer module](property_transfer/README.md) instantiates
transfer of controller specifications and counterexamples for both
trained checkpoints, including two requirements from the companion
Vehicle specification. Transfer does not establish that the original
controller satisfies the requirement.

The [concrete property decisions](property_decision/README.md) now refute
both selected Vehicle requirements at margin 2 for both original trained
checkpoints. Lean checks interior witnesses, their exact outputs and the
same refutations for the reduced models. The separate finite ONNX replay
checks the four witnesses on the original and reduced artifacts.

The [positive-property extension](positive_property/README.md) completes a
positive chain for two additional published DL2/Gödel Lipschitz models:
global real sensitivity bounds imply the chosen all-anchor robustness
requirement, exact pruning reduces each model from 2,561 to 2,522 parameters,
and the smaller model inherits the property. These checkpoints have a
linear output, so the preservation proof explicitly uses that semantics.
The result is separate from the earlier directional-property refutations
and from the stateful optimizer experiments.

For this positive instance:

```text
P(x,y): x,y in [0,1]^6 and every |x_i-y_i| <= 0.001
Q_N(x,y): |N(x)-N(y)| <= 0.1

Proved: forall x,y, P(x,y) -> Q_N(x,y)
        for each original and certified reduced DL2/Godel model.
```

The pruning certificate and sensitivity certificate have different
obligations. Exact reduction transfers the property of a fixed network;
agreement through parameter updates does not establish that the original
property remains true after those updates. The report separates these
claims explicitly in Sections 3–4 and returns to their relationship in
Section 10.

The following sections document the original Baseline/Adversarial
experiment; the [positive-property guide](positive_property/README.md)
documents the additional models. The two original SAIV controllers have
been physically reduced by deleting
hidden ReLU neurons that are provably zero throughout the input cube.
Lean checks that the smaller and original networks compute the same
real-valued function for **every input in `[0,1]^6`**. Separate execution
checks expose a small float32 discrepancy in the baseline model; the real
equality theorem does not assert identical floating-point executions.

| Model | Original -> reduced widths | Parameters | Dense multiplications per input |
| --- | --- | --- | --- |
| Baseline | `6-6-4-1` -> `6-5-4-1` | 75 -> 64 | 64 -> 54 |
| Adversarial | `6-6-4-1` -> `6-4-2-1` | 75 -> 41 | 64 -> 34 |

The adversarial reduction removes 45.3% of parameters and 46.9% of direct
dense scalar multiplications. These structural counts do not predict
hardware speedups. Both exports keep all six inputs, the scalar output
and final ReLU. No training is performed.

## Source models and domain

The trained checkpoints come from the authors' companion repository,
[SAIV_2025_Alsomitra](https://github.com/ckessler2/SAIV_2025_Alsomitra/tree/e9f6f1c52e0e5349455d2b4f69c2015567d3037f),
at commit `e9f6f1c52e0e5349455d2b4f69c2015567d3037f`:

- `python_training/models/final_base_model_norm.onnx`.
- `python_training/models/final_adversarial_model_0.005.onnx`.

The runner checks the original files against pinned SHA-256 values and
their Git blobs. The full hashes appear in the
[verification receipt](../results/network_reduction_verification.json).
The upstream checkpoint files are read only; smaller copies are generated
under `contribution/.build/network_reduction/`.

The domain is exactly the raw normalized model input cube, in coordinate
order `[vx, vy, omega, theta, x, y]`:

```text
D = { [x0,x1,x2,x3,x4,x5] : every xi is real and 0 <= xi <= 1 }

For every x in D:
    reduced(x) = original(x)
```

This is independent of the earlier anchor-view experiment. There is no
anchor in this theorem. The framework's rounded normalization bridge is
not used here: a caller applying that bridge must establish that its
result lies in this exact cube. All six candidate coordinates are retained.

## Mathematical construction

A neuron consists of rational weights and a rational bias. Its affine
value is `z(x) = sum_i w_i*x_i + b`, interpreted over the reals, and its
activation is `max(0,z(x))`. Each checkpoint binary32 constant is decoded
to its exact rational value. Affine arithmetic itself is not rounded in
this semantics.

For an interval box with coordinates `[l_i,u_i]`, the checker uses:

```text
L = b + sum_i min(w_i*l_i, w_i*u_i)
U = b + sum_i max(w_i*l_i, w_i*u_i)

For every x in the box: L <= z(x) <= U.

U <= 0  ==>  max(0,z(x)) = 0 for every x in the box.
```

ReLU propagates an interval `[L,U]` to `[max(0,L),max(0,U)]`.
The first hidden layer bounds therefore supply a sound box for the second
hidden layer. Correlations between activations may be lost, making these
bounds conservative; the procedure need not find every removable neuron.

The certificate contains both hidden layers' preactivation intervals and
Boolean keep masks. `Check` verifies interval inequalities, mask lengths
and a nonpositive upper bound for every deleted neuron.

To remove a neuron, the exporter deletes its incoming weights and bias,
then deletes the matching input weights from the next layer. The proof
uses the identity `w*0 = 0`, preserving every retained neuron's affine
value. It does this for both hidden layers before preserving the output.

```text
Pinned trained ONNX
        |
        +--> exact binary32 parameters --> rational interval certificate
        |                                      |
        |                                      v
        |                                  Lean checker
        |                                      |
        v                                      v
Smaller ONNX --> reload its exact weights --> equality for ALL x in D
        |
        +--> PyTorch / ONNX Runtime comparisons and timing
              (finite execution evidence, recorded separately)
```

## Concrete removable neurons

Layer numbering starts at one; neuron indices start at zero.
All displayed upper bounds are exact fractions computed from checkpoint
weights and checked in Lean.

| Model | Layer / neuron | Certified upper bound before ReLU |
| --- | --- | --- |
| Baseline | 1 / 5 | `-2750849/8388608`, approximately -0.327927 |
| Adversarial | 1 / 3 | `-169149103/536870912`, approximately -0.315065 |
| Adversarial | 1 / 5 | `-11703883/33554432`, approximately -0.348803 |
| Adversarial | 2 / 1 | `-8393689/16777216`, approximately -0.500303 |
| Adversarial | 2 / 3 | `-6045025/16777216`, approximately -0.360312 |

The baseline's sixth first-layer neuron is an especially direct example:
every input weight is negative and its bias is `-2750849/8388608`.
Every coordinate in the cube is nonnegative, so every weighted input
contribution is nonpositive. Its affine value cannot exceed that negative
bias. Consequently its activation is always exactly zero in real arithmetic.

```text
Baseline
    6 inputs --> 6 hidden --> 4 hidden --> 1 output
                    |
              neuron 5 always zero
                    |
    6 inputs --> 5 hidden --> 4 hidden --> 1 output

Adversarial
    6 inputs --> 6 hidden --> 4 hidden --> 1 output
                    |            |
               remove 3,5   remove 1,3
                    |            |
    6 inputs --> 4 hidden --> 2 hidden --> 1 output
```

## What Lean checks

[Pruning.lean](Pruning.lean) proves a reusable deletion theorem for networks
with three affine/ReLU layers. [Baseline.lean](Baseline.lean) and
[Adversarial.lean](Adversarial.lean) instantiate it with the published
weights and the actual reloaded smaller ONNX weights. Each instance proves:

- Correct network dimensions and exact binary32-to-rational decoding for
  both parameter sets.
- Validity of the interval certificate.
- Equality of the reloaded export's rational network with the defined
  pruning transformation.
- Equality of the two real output functions on the entire cube.
- Preservation of any predicate of that output, for an in-domain input.
- Nonemptiness of the input domain.

Each instance also proves rejection of three invalid certificates:
deleting an uncertified active neuron, claiming zero preactivation bounds
everywhere, and providing an empty first-layer mask.

```lean
theorem all_real_inputs (xs : List Real)
    (hx : InBox domain xs) :
    eval reduced xs = eval original xs
```

`EquivalentOn D a b` means equality of the networks' real output functions
throughout `D`. `networkSetoid` proves reflexivity, symmetry and transitivity.
Thus the reduced and original networks belong to the same functional
equivalence class for this domain, despite having different hidden widths.

If a real-output safety predicate was already established for the original
model on the cube, it transfers to the smaller model. Equality alone does
not establish that the original model is safe. A violation is preserved too.

The completed run audits 43 roots: 9 general reduction results, 4 shared
interval results and 15 results for each trained model. Concrete certificate
checks use `decide +kernel`. The transitive axiom audit admits only
`propext`, `Classical.choice` and `Quot.sound`; it admits no `sorryAx` or
native-evaluation axiom.

The ONNX importer/exporter remains an executable adapter, not a verified
compiler. Its graph checks, exact bit comparisons, reloaded export binding
and independent runtime comparisons make this boundary explicit. The
formal theorem concerns the exact real network definitions in the Lean files.

## Float32 execution results

For each original/reduced pair, execution is compared on 8,616 inputs:
all 360 rows of the published normalized training CSV, all 64 cube corners,
and 8,192 pseudorandom interior points, seed `20261105`.
The CSV is a source corpus, not an independently held-out test set.
There are also 96 exact-rational adapter comparisons per pair.

| Execution comparison | Baseline | Adversarial |
| --- | --- | --- |
| PyTorch, one batch of 8,616 inputs | All outputs bit-identical | All outputs bit-identical |
| ONNX Runtime, batch size one | All outputs bit-identical | All outputs bit-identical |
| PyTorch, batch size one | 8,279 bit-identical; 337 differ | All outputs bit-identical |
| Largest PyTorch batch-one difference | `4.76837158203125e-7`; up to 4 ULP | Zero observed |

The baseline discrepancy provides a concrete counterexample to universal
bitwise equality for the tested PyTorch batch-one execution. For example,
one input produces these distinct output words:

```text
input = [0.42239952087402344, 0.38187476992607117,
         0.08920209854841232, 0.5550547242164612,
         0.043541014194488525, 0.907623827457428]

original output = 0.9654448628425598   word = 1064773477
reduced output  = 0.965444803237915    word = 1064773476
```

Changing a matrix shape can change the backend's arithmetic order and
rounding. The real theorem remains valid, but it does not make these
executions identical. Comparisons use `rtol=2e-5, atol=2e-6` as a test
acceptance criterion; these are not universally proved error bounds.
The adversarial model's observed equality likewise does not establish a
universal float32 theorem. No input-gradient or training equivalence is
claimed by this experiment.

## Measured computation

The completed local microbenchmark uses macOS ARM64, PyTorch 2.15.0 and
ONNX Runtime 1.31.1, with one CPU thread and inference mode. ONNX graph
optimization is disabled. Each pair has 50 warm-up calls followed by 15
repeats of 200 calls, alternating measurement order. Values below are
median microseconds per call; the receipt retains every timing sample.

| Model and execution | Original us | Reduced us |
| --- | --- | --- |
| Baseline, PyTorch batch 1 | 8.057 | 8.033 |
| Baseline, PyTorch batch 64 | 9.608 | 9.297 |
| Baseline, PyTorch batch 1024 | 26.121 | 26.029 |
| Baseline, ONNX batch 1 | 3.526 | 3.490 |
| Adversarial, PyTorch batch 1 | 7.945 | 7.912 |
| Adversarial, PyTorch batch 64 | 9.702 | 9.287 |
| Adversarial, PyTorch batch 1024 | 26.073 | 23.111 |
| Adversarial, ONNX batch 1 | 3.436 | 3.412 |

The adversarial batch-1024 median is about 11.4% lower in this run. At batch
one, differences are small and do not support a substantial latency claim.
These tiny networks have considerable invocation overhead relative to their
arithmetic. Timings are local measurements, not a statistical or portable
speedup guarantee. Parameter reduction is much larger than ONNX file-size
reduction because graph metadata remains: 1,829 -> 1,784 bytes for the
baseline, and 1,829 -> 1,691 bytes for the adversarial model.

## Reproduce and inspect

Use the repository's pinned Lean/mathlib environment and a Python environment
with NumPy, PyTorch, ONNX and ONNX Runtime. The recorded run used NumPy 2.4.6,
PyTorch 2.15.0, ONNX 1.23.2 and ONNX Runtime 1.31.1. Check out the companion
repository at the revision above. From this repository's root:

```sh
python -B contribution/network_reduction/verify.py \
  --upstream /path/to/SAIV_2025_Alsomitra
```

This regenerates the two concrete Lean instances and reduced ONNX files,
rebuilds their local Lean dependencies, audits the proof roots, runs the
execution comparisons and benchmarks, and writes:

```text
contribution/results/network_reduction_verification.json
contribution/.build/network_reduction/Baseline.onnx
contribution/.build/network_reduction/Adversarial.onnx
contribution/.build/network_reduction/manifest.json
contribution/.build/network_reduction/Audit.log
```

A failed stage leaves a `FAIL` receipt. A completed `PASS` receipt includes
source hashes, checkpoint hashes, exported model hashes, proof artifacts,
axiom dependencies, concrete numerical differences and timing samples.
It does not certify the untouched upstream training loop.

## Output-update contract

The [output-update extension](output_updates/README.md) is incorporated in
Sections 5–7 of the guide. For the adversarial network's fixed certified
hidden layers, it proves agreement for every rational output head and every
finite sequence of compatible updates. Its view drops two output weights;
the resulting observable subalgebra is proper and stable under five
specified update families.

The operation `a0 := a0 + a1` is a checked counterexample: it preserves the
hidden-neuron certificate but has no exact implementation from the reduced
state alone. A separate 36-root audit records this extension's formal
evidence. No additional float32 or timing result is inferred.

## Update synthesis and optimizer-state reduction

Sections 6 and 8 of [the guide](REPORT.md) explain the
[coordinate-synthesis](update_synthesis/README.md) and
[linear-observation](linear_observations/README.md) experiments. The first
proves least coordinate retention relative to required seed observations.
The second checks a least invariant linear row space and the corresponding
reduced affine implementation.

For the specified coupled momentum model, coordinate selection retains all
ten head-and-momentum coordinates, while linear observations retain eight.
The projection keeps `a1+a3` and `v1+v3` instead of their separate components.
For ordinary momentum, both methods retain six. These are exact scalar-state
dimensions, not new hidden-neuron counts or measured speedups.

The symbolic momentum theorem allows finite sequences of varying rational
configurations. A general transport theorem explains the required Gram
factor in the reduced gradient. A real RMSProp counterexample shows why
the same aggregate view does not support all valid second-moment states.
The 78-root and 82-root receipts record the two extensions separately;
their audit counts overlap. Section 9 explains the separately mechanized
equal-history RMSProp restriction, recorded in the 47-root extension
alongside property transfer. Sections 10–11 distinguish these results
from a demonstrated drone deployment. Exact definitions, theorem locations,
audit receipts and reproduction instructions are in Appendices A–D;
the detailed execution and timing records remain in the experiment receipts.

## Scope of the study

This is a self-contained formal verification case study: a reusable Lean
deletion theorem, exact certificates for two trained checkpoints, smaller
ONNX exports and reproducible execution measurements. The preservation proof
uses interval enclosure, the ReLU definition and deletion of zero terms.

The pruning result does not prove a minimal network or equality outside
the cube. Hidden-layer changes require a new certificate. The later
extensions establish exact correspondence for specified output-head and
optimizer updates, with scoped coordinate or linear-state minimality.
Numerical execution remains separate from the exact theorem. A dedicated
prior-work comparison is needed before claiming a new general reduction
method. See Sections 10–11 of [the guide](REPORT.md) for scope and further
evaluation.

## Replay the complete experiment sequence

### First-time setup

Install Elan so that `lake` is on `PATH`; the pinned toolchain is Lean
4.35.0. Prepare the pinned Mathlib dependencies as described in the
[Lean setup guide](../../lean/README.md). From this repository's root:

```sh
cd lean
lake exe cache get
cd ..
python3 -m venv contribution/.build/runtime-env
. contribution/.build/runtime-env/bin/activate
python -m pip install numpy torch onnx onnxruntime
git clone https://github.com/ckessler2/SAIV_2025_Alsomitra.git ../SAIV_2025_Alsomitra
git -C ../SAIV_2025_Alsomitra checkout e9f6f1c52e0e5349455d2b4f69c2015567d3037f
```

Use `../SAIV_2025_Alsomitra` for the upstream path in the commands below.
The initial dependency setup needs network access. Local proof modules are
then rebuilt by the runners rather than supplied as precompiled artifacts.

### Ordered replay

The positive-property guide gives the shortest route to its result when
the preceding PASS receipts and unchanged proof sources are present.
To regenerate the whole chain, use an environment with the packages
listed in the individual guides and run these commands in order:

```sh
python -B contribution/network_reduction/verify.py \
  --upstream /path/to/SAIV_2025_Alsomitra
python3 -B contribution/network_reduction/output_updates/verify.py
python3 -B contribution/network_reduction/update_synthesis/verify.py \
  --upstream /path/to/SAIV_2025_Alsomitra
python3 -B contribution/network_reduction/linear_observations/verify.py \
  --upstream /path/to/SAIV_2025_Alsomitra
python3 -B contribution/network_reduction/rmsprop_symmetric/verify.py
python3 -B contribution/network_reduction/property_decision/verify.py
python -B contribution/network_reduction/positive_property/verify.py \
  --upstream /path/to/SAIV_2025_Alsomitra
```

The linear stage checks predecessor bindings, including historical
document bindings. After a document revision, rerun coordinate synthesis
before linear synthesis. An old-document hash mismatch is an integrity
check, not a failed mathematical theorem. The property-decision runner's
optional ONNX replay is documented in its guide.

### Verification records

The seven public verification receipts record a fresh replay from an
isolated checkout containing only this study and its tracked prerequisites.
Pinned Mathlib dependencies and the existing Python environment are reused;
the study's local Lean modules are freshly compiled. The mathematical proof
sources are unchanged. Earlier numerical tables describe the initial recorded
experiment; the new receipts contain the repeated execution measurements.

Absolute machine paths in the published JSON command records are normalized
to `<CHECKOUT>`, `<UPSTREAM>` and `<HOME>`. An `export_metadata` field states this
transformation and records the SHA-256 of the unmodified raw receipt, retained
with the local build artifacts. Proof-source, executable, log and checkpoint
digests are not rewritten. Each later runner binds the already normalized
predecessor receipt, so the published chain remains internally consistent.
These command arrays describe a past run; use the portable commands above to
repeat it on another machine.

The dated `output_updates/REVIEW.json` is an earlier source review, not a
review of the current PDF. Its historical bindings are retained as such.

## Build the standalone report

The PDF uses `REPORT.md` as its source. With ReportLab, markdown-it-py,
Matplotlib and svglib installed, run from the repository root:

```sh
python contribution/network_reduction/build_report.py
```

The entry point reuses the shared renderer's macOS Arial and Courier New
fonts and adds vector equations, step diagrams and section page breaks.
It reads the title and revision date from the Markdown source. Rendering
does not rerun inference or modify a verification receipt. Earlier editions
and the document-review manifest remain under `contribution/.build/network_reduction/`.
