# Deciding two controller requirements

**Both `Above(2)` and `Below(2)` are false for each of the two selected
trained checkpoints on the declared cube.** Lean proves concrete interior
counterexamples for the original networks and transfers the same witnesses
to their certified reductions. This resolves the previously open
satisfaction question for these four checkpoint/property combinations.

## Exact requirements and results

The definitions are imported unchanged from
[PropertyTransfer.lean](../property_transfer/PropertyTransfer.lean).
For normalized inputs in `[0,1]^6`, in order
`[vx,vy,omega,theta,x,y]`, put:

```text
X = 41.232296222734604*x[4] + 0.482420778264618
Y = 45.878638794593570*x[5] - 41.681405266088724

Above(2): Y >= -X+2 ==> output >= 1/2
Below(2): Y <= -X-2 ==> output <= 1/2
```

These follow the selected companion Vehicle file with exact decimal
constants and inclusive inequalities. They are not the framework's
different anchor-relative Property2. Outputs are normalized commands.

| Checkpoint | Requirement | Exact input | X+Y, approximately | Exact-real output, approximately |
| --- | --- | --- | --- | --- |
| Baseline | Above(2) | `[1/4,1/2,1/2,1/4,1/4,3/4]` | 3.518069 | 0.399148 |
| Baseline | Below(2) | `[1/4,1/4,1/4,1/4,1/4,1/4]` | -19.421251 | 0.782783 |
| Adversarial | Above(2) | `[1/8,1/8,7/8,1/8,1/8,7/8]` | 4.098861 | 0.275250 |
| Adversarial | Below(2) | `[1/4,1/4,1/4,1/4,1/4,1/4]` | -19.421251 | 1.124245 |

All coordinates are strictly between zero and one. Every antecedent holds
with a strict gap, and every output violates the required half threshold.
The proofs use exact fractions, not the rounded numbers in this table.
An output above one is possible because the checkpoint ends with ReLU,
not clipping to the unit interval.

## What is proved

[ExactEvaluation.lean](ExactEvaluation.lean) defines executable rational
evaluation and proves that casting its result equals the existing real
checkpoint semantics, including all three ReLUs.
[Witnesses.lean](Witnesses.lean) then proves:

1. Each witness belongs to the cube and lies in its interior.
2. Its physical-coordinate antecedent holds.
3. Kernel evaluation computes the exact output of the original checkpoint.
4. The output violates the postcondition, refuting the universal property.
5. The same witness refutes the property for the certified reduced network.

The four exact original outputs, ordered as in the table, are:

```text
 7539692050513325688975 / 18889465931478580854784
14786350527961685237583 / 18889465931478580854784
2662054634994919894468397 / 9671406556917033397649408
5436513554077876856478061 / 4835703278458516698824704
```

[search.py](search.py) finds the candidates using deterministic rational
grids. Search is not trusted: Lean checks the exact results against the
existing original checkpoint definitions. A generated binding additionally
checks that the reproduced search results match the static proof witnesses.
No weights, predicates, thresholds or domains are changed to obtain a result.

## Meaning for the originating study

The companion paper *Neural Network Verification for Gliding Drone Control:
A Case Study*, Section 7.3, Table 1 reports larger critical distances for
these requirements (above: 46/30 for naive/adversarial; below: 42/42).
Its source is pinned with the companion repository. Refutation at distance
2 is therefore consistent with its reported limitations. This work does
not claim discovery of a previously unknown vulnerability or contradiction
of the authors' results. The added artifact is kernel-checked exact evidence
and its verified transfer through concrete network reduction.

This is a statement about the selected input/output requirements on the
declared cube. It is not a demonstrated reachable flight failure, a proof
about all controllers, or a refutation at every margin. Runtime evidence
is finite and separate from the real-arithmetic theorem.

## Reproduce

From the repository root, with the pinned Lean/mathlib installation:

```sh
python3 -B contribution/network_reduction/property_decision/verify.py
```

For the additional eight ONNX executions, use an interpreter with NumPy,
ONNX and ONNX Runtime. The existing smaller ONNX artifacts must be present:

```sh
python3 -B contribution/network_reduction/property_decision/verify.py \
  --runtime-python /path/to/python-with-onnx \
  --upstream /path/to/SAIV_2025_Alsomitra
```

The verifier rebuilds all required local Lean dependencies, audits every
new theorem, checks the reproduced search bindings, and rejects a wrong
output claim and a witness outside the specified antecedent. Each attempt
has separate retained sources and logs. Earlier receipts remain untouched.
Inspect [the new receipt](../../results/property_decision_verification.json)
for actual proof status and optional runtime results.

The runtime adapter checks artifact hashes and parameter words against the
existing checkpoint receipt, uses the CPU provider with graph optimization
disabled and one thread, and records exact input/output words. These inputs
are dyadic, so binary32 represents them exactly. Eight observed violations
do not constitute a universal floating-point refinement theorem.
