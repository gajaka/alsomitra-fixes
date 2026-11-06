# Certified linear observations for stateful network updates

This experiment extends coordinate retention to **linear combinations of
parameters and optimizer memory**. It constructs a reduced state, checks
that its updates commute with the full system, and certifies the least
invariant row space containing specified evaluation coordinates.

The concrete cases use the actual adversarial Alsomitra checkpoint with
frozen, certified hidden layers. The changing state contains five rational
output-head parameters and five momentum values. No previous proof, report,
checkpoint or receipt is modified.

| Update model | Full state | Exact coordinate retention | Linear observations |
| --- | --- | --- | --- |
| Ordinary momentum, frozen features | 10 | 6 | 6 |
| Momentum with the specified coupled penalty | 10 | 10 | 8 |

These are scalar dimensions of the changing state. They are not measured
memory bytes, runtime improvements or parameter counts of the whole network.
The reduced forward network remains `6-4-2-1`.

## The concrete optimizer and objective

Let `a=(a0,a1,a2,a3,b)` be the output head, `v` its momentum, and
`z=(h0,0,h2,0,1)` the frozen hidden features with a bias coordinate.
The two middle zeros come from the checked dormant-neuron result. We use:

```text
score(a) = a0*h0 + a2*h2 + b

L(a) = (score(a)-y)^2 / 2 + lambda*(a0+a1+a3)^2 / 2

g = (score(a)-y)*z + lambda*(a0+a1+a3)*(1,1,0,1,0)
v' = mu*v + g
a' = a - eta*v'
```

The penalty is explicitly chosen to test cross-parameter dependencies.
It is a new experiment objective, not the authors' training algorithm and
not an established beneficial regularizer for this controller. `lambda=0`
gives the ordinary momentum comparison. The displayed gradient formula is
specified algebraically; no general differentiation engine is verified.

With nonzero coupling, future `a0` depends on both `a1` and `a3`. Coordinate
retention must keep each, along with the relevant momentum coordinates.
Linear observations instead retain their sums:

```text
Full:
    a0, a1, a2, a3, b, v0, v1, v2, v3, vb

Reduced:
    a0, (a1+a3), a2, b, v0, (v1+v3), v2, vb
```

The aggregate gradients contain `2*lambda*(a0+a1+a3)`: this factor is
essential, because two full coordinates contribute to the sum.

## What the synthesis certificate establishes

For a finite rational affine family `x' = A_k*x + b_k`, the producer starts
from the rows observing `a0`, `a2` and `b`. It closes their span under
`row -> row*A_k`, using exact Gaussian elimination. Unlike the preceding
coordinate algorithm, it can retain a sum without retaining its summands.

The producer emits a projection matrix `B`, reduced affine maps, pivot
coordinates, and a derivation DAG explaining every retained row. The Lean
checker verifies:

- **Derivation:** each retained row is generated from seed rows using rational
  linear combinations and pullback by the supplied update matrices.
- **Closure:** every retained row pulled back by any supplied operation is
  a linear combination of retained rows.
- **Independence:** checked pivot coordinates prove that the retained rows
  are linearly independent.
- **Execution:** `B*A_k = A_reduced_k*B` and `B*b_k = b_reduced_k`.
- **Seeds:** the required initial observations can be recovered from `B*x`.

The generic theorem then proves that this row space is contained in every
invariant rational linear subspace containing the seeds. Together with
independence, this gives a dimension lower bound of six or eight for the
respective concrete case. The generated space attains the bound.

This minimum is relative to the required seed observations and linear
reduction model. It is not a minimum among arbitrary nonlinear encodings,
reachable-state abstractions or all network architectures. The seeds come
from the preceding network reduction; the procedure does not discover
every possible functional redundancy of the checkpoint.

Gaussian elimination and the emitter are untrusted producers. Lean checks
their output certificates. We do not claim a verified implementation or
termination proof of this Python producer.

## A symbolic result beyond the fixed instance

`MomentumQuotient.lean` proves the eight-coordinate projection correct for
**all rational values** of `h0`, `h2`, `y`, `eta`, `mu` and `lambda`, and all
rational initial heads and momenta. This is an algebraic correspondence,
not a convergence claim for arbitrary optimizer parameters.

The result allows a different configuration at every step. For every finite
list of configurations:

```text
q(fullRun(configurations, state))
    = reducedRun(configurations, q(state)).
```

The actual full and reduced checkpoint networks therefore agree after every
such sequence, for every real evaluation input in the certified cube.
The hidden-neuron certificate continues to hold. Updates may change both
networks' outputs and may invalidate an unrelated safety property.

Equality under `q` is an equivalence relation preserved by these sequences.
The real-valued observables factoring through `q` form a proper Mathlib
subalgebra, stable under all these sequences. Properness is witnessed by
changing `a1` and `a3` by opposite amounts: the raw coordinate changes while
the entire retained view remains unchanged.

The theorem receives the same configuration list in both runs. Adaptive
sample selection or parameter tuning requires a separate proof that those
decisions use retained information.

## Transporting the optimizer, not just its state

An exact reduced representation does not justify applying the original
optimizer unchanged to the reduced coordinates. `GradientTransport.lean`
proves a general correction rule. For a rational matrix `B`, suppose the
full gradient function satisfies

```text
G(a) = B^T * g(B*a).
```

For arbitrary such functions, including nonlinear ones, the projected
momentum state `u=B*a, w=B*v` evolves exactly as

```text
w' = mu*w + (B*B^T)*g(u)
u' = u - eta*w'.
```

The theorem is conditional on the displayed gradient factorization; it does
not prove a differentiation algorithm or the chain rule for arbitrary loss
functions. It permits varying gradient functions, rates and momentum values
over any finite sequence, provided each full gradient has this factorization.

For the concrete head projection `B*a=(a0,a1+a3,a2,b)`, Lean checks
`B*B^T=diag(1,2,1,1)` and the factorization of the specified full gradient.
This explains the factor two on the aggregate coordinate. A separate checked
example projects two weights to their sum: from zero, a unit full gradient
step changes that sum to `-2`, while an uncorrected reduced gradient step
changes it to `-1`. The Gram-corrected step agrees with the full execution.

The matrix identity is standard linear algebra. Its role here is to make
explicit what a correct optimizer implementation must retain and change
when using the certified reduced representation.

## Checkpoint binding and exact replay

The concrete affine instances use the first published normalized training
row, target `3/4`, rate `1/100`, momentum `9/10`, and penalty `0` or `1/100`.
The feature constants are bound in Lean to the preceding checked feature
evaluation from `Adversarial.original`. An additional theorem proves that
the emitted affine matrix implements the displayed momentum rule for every
rational full state.

Each fixed-operation case is replayed for 16 steps from twelve initial states:
the actual trained head with zero momentum, the all-zero state, and ten
coordinate basis states. Full and reduced states are compared exactly.

A separate mixed replay takes the first eight published CSV rows in order,
twice. It starts from the actual head with zero momentum and compares three
implementations: the direct momentum formula, the full affine map, and the
eight-coordinate aggregate update. Inputs are interpreted as exact decimal
rationals, with domain and dormant-feature checks. This is an execution
cross-check, not held-out evaluation or an accuracy benchmark.

## A checked boundary: RMSProp

`AdaptiveBoundary.lean` tests the same pattern of aggregate observations for
RMSProp, where the last five coordinates store second moments rather than
momentum. It specifies decay `1/2`, rate `1`, epsilon `1`, no centering and no
momentum, with the same kind of coupled quadratic objective and target zero.

Two states have identical heads `(1,0,0,0,0)`. Their discarded-coordinate
second moments are `(1,97)` and `(49,49)`, respectively; both sum to 98 and
all moments are nonnegative. The retained views are identical. After the
step, those second moments become `(1,49)` and `(25,25)`. Per-coordinate
normalization gives different sums of updated weights:

```text
first state:  a1' + a3' = -1/2 - 1/8 = -5/8
second state: a1' + a3' = -1/6 - 1/6 = -1/3
```

Lean proves that **no deterministic reduced update on this particular view**
can implement the specified RMSProp step for all valid states. This does not
exclude other RMSProp abstractions. These valid nonnegative histories are
not proved reachable from zero initialization; no claim about all actual
fresh training runs follows from the witness.

## Reproduction and artifacts

From the repository root:

```sh
python3 -B contribution/network_reduction/linear_observations/verify.py
```

Use `--upstream /path/to/SAIV_2025_Alsomitra` if the pinned companion checkout
is not under `~/projects/ppg-lab/external/`. The source CSV must match its
recorded checksum. The verifier uses the Python standard library and the
existing pinned Lean 4.35.0/mathlib installation.

The previous [synthesis receipt](../../results/update_synthesis_verification.json)
and its generated calibration sources must be present. They are checked
against their recorded hashes, then rebuilt in the new isolated attempt.
The new [verification receipt](../../results/linear_observations_verification.json)
records source bindings, generated artifacts, all build logs, axiom audit,
replay and deliberate rejection controls. Attempts remain under
`contribution/.build/linear_observations/attempt-NNN/`.

The negative controls corrupt a row-derivation witness and a reduced update
coefficient. Both must fail the proof checks. The audit admits only
`propext`, `Classical.choice` and `Quot.sound`. No new second-kernel, float32,
ONNX-runtime or performance result is claimed.

## Relation to prior work and paper scope

Invariant subspaces, observability and linear lumping are established ideas.
[CLUE](https://arxiv.org/abs/2004.11961) computes constrained exact linear
reductions for polynomial differential equations, a broader nonlinear
continuous-time setting. Neural-network reduction also has prior
[bisimulation](https://arxiv.org/abs/2110.03726) and
[lumping](https://arxiv.org/abs/2209.07475) approaches.

The contribution tested here is the mechanically checked connection between
a real trained-network reduction, generated optimizer-state observations,
a strict comparison with coordinate retention, and an explicit optimizer
boundary. These artifacts strengthen a potential case study; they do not
by themselves establish methodological priority or publication readiness.

- [LinearObservations.lean](LinearObservations.lean): certificate soundness,
  least invariant row space, dimension bound and affine correspondence.
- [MomentumQuotient.lean](MomentumQuotient.lean): symbolic update family,
  actual network equality, RR and proper stable observable subalgebra.
- [AdaptiveBoundary.lean](AdaptiveBoundary.lean): RMSProp nonfactorization.
- [GradientTransport.lean](GradientTransport.lean): general conditional
  momentum transport, Gram correction and an uncorrected-update counterexample.
- [linear_synthesis.py](linear_synthesis.py): exact producer and replay.
- [verify.py](verify.py): isolated build, audit and negative controls.
- [PLAN.md](PLAN.md): pre-experiment scope and comparison rules.
