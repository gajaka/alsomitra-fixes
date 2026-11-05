# Property2: connecting the contract to PyTorch float32 observations

Research contribution by Dragan Stosic, with Codex assistance.

This implementation checks **actual observed CPU float32 input/output bits**
with the executable Lean contract. It also runs the original `AlsomitraNet`
class in an optional integration check. It does not prove a trained network
correct for all inputs, or prove PyTorch arithmetic equivalent to rational
arithmetic. The model in the upstream integration has deterministic initial
weights and is explicitly **not trained**.

## What is connected

```text
exact Spec + captured input-normalizer bits
                  |
                  v
 Lean region compiler -> inward float32 bounds -> PyTorch candidate
                                                    |
                                              capture its bits
                                                    |
                                      Lean decode + admissibility gate
                                                    |
                                           accepted input tensor
                                                    |
                                        actual PyTorch inference
                                                    |
                                    capture actual output tensor bits
                                                    |
                                       Lean decode + exact monitor
                                                    |
                           outside / satisfied / violated + provenance
```

The primary verdict refers to the exact contract evaluated on the decoded
normalized input/output. A separate verdict refers to physical values that
PyTorch has **already materialized and rounded**. These meanings are not
silently identified.

## Definitions and mathematical boundary

The coordinate order, six-decimal physical domain, anchor-relative predicate,
and exact thresholds are defined in [SPECIFICATION.md](SPECIFICATION.md).
In particular, the original domain is not replaced by rounded endpoints.

For an unsigned 32-bit word `w`, let `s` be its sign bit, `e` its eight-bit
exponent, and `f` its 23-bit fraction. The decoder specifies:

```text
e = 0:        D(w) = (-1)^s * f / 2^149
1 <= e < 255: D(w) = (-1)^s * (2^23 + f) * 2^e / 2^150
e = 255:      reject (NaN or infinity)
w >= 2^32:    reject
```

Both signed zeros denote rational zero; their distinct bits remain in the
observation record. Subnormal values are accepted as encoded. This definition
follows the single-format representation in Oracle's
[IEEE Arithmetic reference](https://docs.oracle.com/cd/E19957-01/806-3568/ncg_math.html).
It is a mathematical specification of the encoding, not a formal verification
of a CPU's floating-point unit or of Python's bitcast implementation.

For captured offset and scale words, the input interpretation is:

```text
offset[i] = D(offset_bits[i])
scale[i]  = D(scale_bits[i]) > 0
z[i]      = D(input_bits[i])
p[i]      = offset[i] + scale[i] * z[i]   (exact rational arithmetic)
```

The adapter captures `min` and the actual float32 tensor `max - min` from
upstream normalization. It does not substitute the exact decimal difference
for this already-rounded scale. The intended output contract remains fixed:

```text
y = D(output_bits)
OutputOK(y) := 181/1000 + (12/1000)*y <= 187/1000
            <=> y <= 1/2
```

The primary verdict is `outside` when `Pre(spec,p)` is false, `satisfied` when
it and `OutputOK(y)` hold, and `violated` when the precondition holds but the
output contract does not. Outside is not reported as a successful certificate.

Separately, the adapter computes and captures these actual eager operations:

```python
physical = inputs * scale_tensor + offset_tensor
physical_output = torch.tensor(.181, dtype=torch.float32) + (
    torch.tensor(.012, dtype=torch.float32) * outputs
)
```

The secondary verdict applies the **same exact physical predicate and cap**
to those newly decoded physical values. It is named `rounded_verdict` in the
protocol. The upstream integration checks that these materializations agree
bit-for-bit with the original input/output denormalizer methods on its cases.
The output mapping above is fixed to this contribution; other output
normalizers require a new specified contract.

## A reproduced numerical disagreement

For an interior input satisfying both input interpretations, choose the next
float32 value above `0.5`:

| Quantity | Observed value |
| --- | --- |
| Normalized output bits | `0x3f000001` |
| Normalized output | `0.5000000596046448` |
| Exact intended normalized cap | `0.5` |
| Original code's computed float32 normalized cap | `0.5000010132789612` |
| Original code's float32 denormalized output | `0.18699999153614044` |
| Exact normalized-output contract | `violated` |
| Contract on materialized physical output | `satisfied` |
| Comparison to original computed normalized cap | accepts |

The original postcondition computes its normalized cap by float32 subtraction
and division. The difference above is reproduced using that original class,
not inferred from a replacement Python model. This is a **difference between
numeric contracts**, not by itself a claim that an additional upstream bug
has been established or that a trained model violates its chosen contract.
No numerical tolerance is used in the Lean verdict.

## Candidate generation and its guarantee

The adapter asks Lean for exact normalized box bounds. It searches the finite
binary32 ordering to round lower bounds upwards and upper bounds downwards,
then performs actual float32 interpolation and clamps to those inward bounds.
Every resulting row must pass the proved Lean gate before it is returned.

The formal guarantee is about this final gate, independently of how the
candidate was proposed. The Python rounding/search/interpolation implementation
is tested, not universally proved. Overflow/non-finite results are rejected.
An empty exact region and a nonempty exact region with **no float32
representative** are different errors; the tests include both, as well as a
representable zero-width region.

The test's ordinary affine float32 construction fails the exact input gate at
all 64 corners of its selected box. The guarded construction checks all 64
corners and 64 deterministic interior samples. This is evidence for the need
for an explicit boundary contract, not a claim about every upstream sampler.

## Lean theorems and trusted components

[Float32.lean](Float32.lean) adds eight audited theorem roots to the 19 rational
roots:

- `decode_none_iff`: exactly the out-of-range or exponent-255 words are rejected.
- `admissible_iff`: an accepted bit vector decodes to a point satisfying `Pre`.
- `observe_{satisfied,violated,outside}_iff`: each primary verdict has exactly
  its stated decoded input/output meaning.
- `physicalMonitor_{satisfied,violated,outside}_iff`: the corresponding meaning
  for already-materialized physical values.

The executable monitor calls these same Lean definitions. There is no
handwritten Python replacement for the verdict function. The audit rejects
missing/duplicate roots and extra axioms, including `sorryAx`.

The trusted boundary includes the intended domain/units/specification, the
chosen binary32 encoding definition, Lean and its runtime/compiler, imported
Mathlib, JSON transport, tensor snapshot/bitcast code, and the operating
environment. The Python boundary and parsing are integration-tested, not
formally proved. Standard Lean axioms are reported explicitly.

No theorem here specifies GEMM rounding, fused operations, PyTorch kernels,
GPU execution, flushing of subnormals, gradients, training, termination of a
network, or universally quantifies over a model's inputs. PyTorch itself
documents numerical differences across devices, versions and operation
arrangements in its [numerical accuracy notes](https://docs.pytorch.org/docs/2.15/notes/numerical_accuracy.html).
The bridge checks the values actually observed in its supported CPU execution.

## Model and observation binding

`infer_checked` supports ordinary eval-mode `Sequential`, `Linear`, `ReLU`
and `Identity` modules. It runs a private model snapshot with CPU autocast
disabled. It records the graph with module paths, parameter bits, exact Spec,
normalizer bits, input/output shapes and bits, relevant contract source hashes,
and PyTorch version. It checks that captured inputs/model state did not change
during execution. Other modules, module hooks and custom/compiled forwards are
rejected by this convenience wrapper.

`assert_binding` detects changed inputs, outputs, model parameters,
normalization, specification, or receipt contents. A receipt is a pointwise
observation with provenance, **not a universal model theorem**, a signature,
or protection against malicious code that can rewrite the receipt and hash.
Execution assumes an ordinary unmodified PyTorch installation with no global
hooks or concurrent mutation of model/input objects. The generic `observe`
function accepts an already-produced pair; the caller supplies its provenance.

The optional upstream check executes the original `AlsomitraNet.forward`,
captures its actual outputs and verifies both original denormalizers. Its
separate receipt records the pinned source hashes and model-state hash. It
uses 16 inputs and deterministic initialization, with no training or claims
about the aerodynamics accuracy of those weights.

## Run and inspect

From the repository root, using a Python environment with PyTorch installed:

```sh
python -B contribution/verify_float32.py
python -B contribution/torch_bridge.py
```

The first command reruns the rational baseline, rebuilds the float32 Lean
modules, audits all added theorem roots, and runs the actual tensor integration
checks. The second prints a checked inference receipt for the small fixed
demonstration network. It requires a successful report matching current
sources and compiled artifacts.

To include the original upstream classes:

```sh
python -B contribution/verify_float32.py --upstream /path/to/property-driven-ml
```

The checkout must be at `616df1e5baaabf7b42dc26320c00fb297903c87a`, with the
three exercised source files unchanged, and its Python dependencies available.
Locally, the verified invocation uses
`/Users/gajaka/projects/ppg-lab/.venv/bin/python` and upstream checkout
`/Users/gajaka/projects/ppg-lab/external/property-driven-ml`.

Inspect [results/float32_verification.json](results/float32_verification.json)
for status, source/artifact hashes, environment, counts, boundary witness and
receipts. The full JSON-lines transcript is under ignored
`.build/float32_cases.jsonl`; its hash is recorded in the report.

The CLI is [Float32Main.lean](Float32Main.lean), with shared rational parsing in
[Protocol.lean](Protocol.lean). Bit words are unsigned JSON integers; rational
Spec fields remain integer/fraction strings. `decode`, `bounds`, `gate`, and
`observe` are distinct actions. `observe` can additionally take
`physical_bits` and `physical_output_bits`, but must receive both together.
Non-finite output values and invalid normalizers produce errors, never a
successful verdict. This is still a Lean-process adapter, not a production C
ABI or a real-time performance claim.
