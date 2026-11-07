# A repaired controller with an explicit directional guarantee

This walkthrough follows a concrete controller repair from an initial
violation to executable code and checked proofs. Each step has a precise
definition, a code artifact and an explicit account of what was verified.
The two questions are: can the controller satisfy the selected directional
requirements everywhere in the specified domain, and can it retain useful
predictions on the supplied data?

The frozen construction answers both questions under the conditions below.
Its reference mean squared error is **0.001475236171**, compared with the
original checkpoint's **0.001532418405**, about **3.73% lower on the same
360 rows used for fitting**. This is not a held-out result.

The roles of the two components are central to the result. Training supplies
a fitted neural core. An additional continuous block with six ReLU
operations establishes the directional guarantee. The proof concerns the
complete core-plus-block controller. This explicitly changes the architecture;
the core alone is not claimed to satisfy the two universal requirements.

## What must hold?

An input contains six normalized coordinates:

```text
x = [vx, vy, omega, theta, position_x, position_y] in [0,1]^6.
```

Using the existing exact normalization constants, recover physical X and Y
and write `d = X + Y`. The requirements are unchanged:

```text
P_above(x): d >=  2       Q_above(x): repaired(x) >= 0.5
P_below(x): d <= -2       Q_below(x): repaired(x) <= 0.5

For every x in the cube:
  P_above(x) implies Q_above(x)
  P_below(x) implies Q_below(x).
```

There is no directional requirement in the gap `-2 < d < 2`. These are the
companion Vehicle Above/Below properties, not the previously proved
two-input robustness property of the different DL2/Godel checkpoints.

The separate quality gate requires MSE against all 360 ORIGINAL CSV labels
to be no greater than the original checkpoint's error and strictly smaller
than constant `1/2` prediction. Merely returning `1/2` everywhere cannot pass.
MSE means the average squared difference between a predicted output and its
reference label; smaller values mean closer agreement on these rows.

## Initial state: the published controller

```text
               ORIGINAL ADVERSARIAL CHECKPOINT

6 normalized inputs --> 6 ReLU --> 4 ReLU --> 1 ReLU --> N_old(x)

Trainable parameters: 75          ReLU operations: 11
```

For the concrete input `x=[0,0,0,0,0,0]`, the physical displacement is about
`-41.19898449`. This satisfies the Below(2) precondition, which requires an
output at most `0.5`. The original exact model instead returns about
`1.36078430`. The input belongs to the specified cube; physical reachability
of that state is a separate question.

The repair intentionally changes the controller's function. Its purpose is
to satisfy the requirement while meeting the reference-quality gate.

## Final state: fitted core and explicit correction

```text
                     REPAIRED CONTROLLER

six normalized inputs x
       |
       +------> fitted core: 6 -> 4 -> 2 -> 1 ------> z
       |                                              |
       +------> physical displacement d = X+Y          |
                           |                          |
                           v                          v
                     [lower(d), upper(d)] ------> project z
                                                      |
                                                      v
                                                repaired output

Fitted core parameters: 41
Core ReLUs: 7          Additional repair-block ReLUs: 6
```

At the same zero input, the final controller returns approximately
`0.30580117`, satisfying Below(2). The block leaves that fitted prediction
unchanged. The next examples also show cases where the block actively
corrects the core's output.

For this candidate, k=64:

```text
lower(d) = min(0.5, max(0, 0.5 + 64*(d-2)))
upper(d) = max(0.5, min(1, 0.5 + 64*(d+2)))

repaired(x) = max(lower(d), min(upper(d), core(x))).
```

The interval is always nonempty, with `0 <= lower <= 0.5 <= upper <= 1`.
For `d>=2`, the lower bound is exactly `0.5`. For `d<=-2`, the upper bound
is exactly `0.5`. Projecting the core output into this interval therefore
establishes both implications, regardless of the core's behavior.

If the core output already lies in the interval, it is unchanged. Repeating
the projection also leaves the result unchanged. These facts, the output
range and the directional implications are proved in `ProjectionRepair.lean`.

This block has a ReLU-only expression, using shared intermediate values:

```text
max(a,b) = a + ReLU(b-a)
min(a,b) = a - ReLU(a-b).
```

`reluBlock_eq_project` proves that expression equals the projection.
The fixed slope 64 creates a narrow transition near each boundary. No
global Lipschitz, sensitivity or flight-stability claim follows from the
directional theorem.

## Concrete reference examples

Rows are indexed from zero. Displayed values are rounded; proofs use exact
rational values and real semantics.

| CSV row | d | Original label | Fitted core | Repaired output |
| --- | ---: | ---: | ---: | ---: |
| 0 | 1.822511 | 0.75 | 0.750135 | 0.750135 |
| 129 | 2.070171 | 0.373198 | 0.369787 | 0.5 |
| 169 | 2.417322 | 0.478191 | 0.474202 | 0.5 |
| 10 | 0.699138 | 0 | 0 | 0 |
| 1 | 2.023885 | 1 | 2.844242 | 1 |

Row 129 shows a real conflict between a label and the selected requirement.
The corrected output must be at least `0.5`, even though the label is lower.
The label has not been changed for evaluation. There are ten such conflicts;
their unavoidable errors alone give a reference MSE floor about `0.001461609`.

The candidate still passes the original gate by fitting the remaining
behavior more accurately. Its reference outputs span 0 to 1; the output
block changes the fitted core's prediction on 74 of the 360 rows.

## Code, definitions and checks at each step

| Step | Code or artifact | Mathematical statement | Check |
| --- | --- | --- | --- |
| Fit the core | [train.py](train.py), [FIT.json](FIT.json) | Select parameters using the 360 reference rows and the fixed output block. | Optimizer replay and comparison with frozen weights; training itself is not a proof. |
| Freeze its meaning | [freeze.py](freeze.py), [CANDIDATE.json](CANDIDATE.json) | Fix rational weights and the original decimal inputs/labels. | Hash checks, exact Lean-input regeneration and rational-to-real evaluation lemmas. |
| Enforce the contract | [ProjectionRepair.lean](ProjectionRepair.lean), [RepairNetwork.lean](RepairNetwork.lean) | Every in-domain Above/Below precondition implies the required output condition. | Lean proofs for the complete core-plus-block model and the six-ReLU expression. |
| Check reference quality | [RepairReference.lean](RepairReference.lean), [RepairResult.lean](RepairResult.lean) | MSE is no greater than the original model's and below constant-half prediction. | Exact computations checked by the Lean kernel, then transferred to real semantics. |
| Reduce the fitted core | [RepairedCore.lean](RepairedCore.lean) | Full and reduced repaired controllers agree on the whole cube. | A new interval certificate and the general pruning theorem. |
| Execute and audit | [runtime.py](runtime.py), [verify.py](verify.py) | Evaluate the frozen construction and check the declared proof roots. | Exact execution, fresh Lean build, axiom audit and negative controls. |

The code makes the example runnable. The definitions say exactly what the
objects and requirements mean. The checks establish the stated guarantees
within their declared domains. None of these roles substitutes for the others.

## The combined theorem

`repaired_controller_contract` in [RepairResult.lean](RepairResult.lean) (in the
`Contribution.DirectedRepair` namespace) combines:

1. Universal Above(2) satisfaction on the cube.
2. Universal Below(2) satisfaction on the cube.
3. Reference MSE no greater than the original checkpoint's.
4. Reference MSE strictly below constant `1/2` prediction.

The proof of quality uses exact, kernel-checked rational computations:

```text
repaired MSE <= 0.001476
original MSE >= 0.001532
constant MSE >= 0.109.
```

Cast lemmas connect executable rational network evaluation and MSE to the
real model. The universal implications are not inferred from testing the
360 rows. The dataset is used for the separate, finite quality claim.

The frozen core has dyadic weights with denominator dividing 65,536.
The maximum core-parameter change during fitting was about 18.64, so this
is not claimed to be a small or minimal perturbation of the old weights.

## Reduction is checked again

The fitted 41-parameter core is embedded into a 75-parameter full core, keeping
the formerly removed neurons and their unused parameters explicit. A NEW
interval certificate verifies that the same four neurons are still inactive
on the cube. `core_equal` proves full and reduced fitted cores agree.
`smaller_repair_equal` transfers this equality through the repair block.
Here a pruning certificate contains preactivation interval bounds and
Boolean masks specifying which neurons to retain. The checker verifies that
every removed neuron has nonpositive preactivation throughout the cube, so
its ReLU output is always zero.

```text
Fitted full core, 75 parameters --> SAME repair block --> R_full(x)
                                                           ||
                                                equal for every x in cube
                                                           ||
Reduced fitted core, 41 parameters -> SAME repair block --> R_small(x)
```

This equality compares the two repaired versions. It does not equate the
repaired controller with the original controller that violated the target.

The repaired full graph has 17 ReLU operations and its reduced counterpart
has 13, counting the six added block operations. The original unrepaired
full graph had 11. Thus the new repaired graph is not claimed to be smaller
than the old unrepaired network. Existing subalgebra/update certificates are
not automatically extended to this changed model.

## Run it

Exact rational execution needs only Python's standard library:

```sh
python3 -B contribution/model_repair/directed_repair/runtime.py 0 0 0 0 0 0
python3 -B contribution/model_repair/directed_repair/runtime.py 0 0 0 0 1 1
```

Rebuild the proof using the repository's pinned Lean/Mathlib setup:

```sh
python3 contribution/model_repair/prepare_inputs.py --reference-only
python3 -B contribution/model_repair/directed_repair/freeze.py --check
python3 -B contribution/model_repair/directed_repair/verify.py
```

Proof replay uses the frozen candidate and original CSV; retraining and
PyTorch are unnecessary. The verifier performs a fresh local compilation,
an axiom audit and deliberately false negative controls. See `RESULT.json`
for the actual replay status. No independent second-kernel run is claimed.

For an optional replay of the selected fit, use an environment with NumPy
and PyTorch, then run:

```sh
python3 -B contribution/model_repair/directed_repair/train.py \
  --out contribution/model_repair/results/training-replay
```

Use a new output directory. The replay reports whether its quantized weights
match [CANDIDATE.json](CANDIDATE.json). [TRAINING.md](TRAINING.md) records the
selected initialization, optimizer settings and numerical environment.
Floating optimizer reproducibility can depend on the environment; the
proof replay verifies the published frozen parameters directly.

The four negative controls are intentional verifier tests: reversed repair
slope, the original violating output, constant prediction failing quality,
and deleting an active neuron. Successful verification requires their
rejection. They are not proposed repaired models.

## Limits of the result

The fitted core itself is not asserted to satisfy Above/Below. The repaired
core-plus-block construction does. The quality result covers the supplied
reference corpus used during fitting, not unseen trajectories. The proofs
use exact rational constants and real arithmetic; they do not establish
universal float32 execution behavior or closed-loop flight safety. No claim
of novelty or superiority over established constrained-controller repair
methods is made.
