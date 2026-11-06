# Update-aware synthesis of retained network state

This experiment chooses retained parameters from a **specified update family**,
then generates smaller update code and Lean proofs of its correctness. It
extends the existing trained-network reduction and output-update contract.
The original checkpoints, earlier proofs, receipts and PDF are unchanged.

The supported update language is a finite family of simultaneous rational
affine maps. The synthesis theorem is generic in state dimension. The
network instances use the actual certified adversarial Alsomitra controller,
with fixed hidden layers and variable rational output-head parameters.

## The distinction this experiment tests

The certified dormant neurons make the original output weights `a1` and `a3`
irrelevant to evaluation on the input cube. Evaluation needs
`{a0, a2, bias}`. However, an update such as `a0 := a0 + a1` needs the old
value of `a1`, so the update state must also retain it.

```text
Evaluation seed: {a0, a2, bias}
                  |
                  +-- independent shifts ------> {a0, a2, bias}
                  |
                  +-- a0 := a0 + a1 ------------> {a0, a1, a2, bias}
                  |
                  +-- also a1 := a1 + a3 -------> {a0, a1, a2, a3, bias}
                  |
                  +-- frozen-feature calibration -> {a0, a2, bias}
```

An extra retained weight is **update memory**. It does not restore the
deleted neuron to the forward computation. The reduced inference network
remains `6-4-2-1`. The five-to-three/four/five dimensions below describe the
variable output-head update state, not the whole network's parameter count.

## Exact input language and semantics

For `n` coordinates, a state is `Fin n -> Rational`. An operation has a
rational matrix `A` and offset `b`, with semantics:

```text
T(x)[i] = sum_j A[i,j] * x[j] + b[i].
```

Every right-hand side reads the old state. The JSON language specifies
destination coordinates, rational linear terms and a constant; coordinates
with no assignment retain their values. A sequence is an ordered list of
operation indices. Operation indices and arguments are supplied equally to
full and reduced executions. Adaptive selection needs its own justification
that the selection depends only on retained information.

The adapter accepts exact rational strings and integers, and rejects floating
coefficients, unknown coordinates and nonlinear expressions. The core Lean
construction also covers empty coordinate sets and empty operation families;
this first Python emitter requires nonempty coordinates, retained state and
operation family.

## Synthesis and its proved scope

Start with a seed `K0`. Repeatedly add coordinate `j` whenever some permitted
operation has `A[i,j] != 0` for a currently retained coordinate `i`. Stop when
the set does not change. The Lean definition `synthesize` implements this
recursion; termination follows because every nonterminal round strictly
increases the retained finite set.

The computed set `K` satisfies:

- It contains the seed and is closed under the nonzero matrix dependencies.
- Projection commutes with every operation, and with every finite sequence.
- It is the least coordinate set containing the seed that admits exact
  reduced updates **for all rational states**.

The necessity proof uses two states that differ only at one discarded
coordinate. A nonzero matrix coefficient makes their next retained values
different. Consequently, no function on the retained state alone can implement
that operation exactly. This proves necessity for any candidate reduced
function, not only affine candidate implementations.

The guarantee concerns coordinate projections containing the supplied seed.
It is not minimality among arbitrary linear summaries, arbitrary subalgebras,
reachable-state invariants or all possible neural-network reductions. The
seed is justified by the prior network theorem; synthesis does not discover
every possible functional redundancy of that network.

## Generated implementation and network theorem

The Python emitter produces a physically smaller matrix and offset, using
only retained rows and columns. Each generated Lean module independently
checks the selected mask and proves that this **particular packed matrix**
commutes with the original affine update. The emitted sequence theorem
covers every finite operation word and every rational initial head.

The original hidden-neuron certificate holds for every head because hidden
layers remain fixed. For each real input in `[0,1]^6`, the actual full network
and existing reduced network agree after every operation sequence. Their
output is allowed to change during calibration; this is not preservation of
a previous output value or an independently established safety threshold.

The relation `RR(x,y)` is equality of retained coordinates. It is an equivalence
relation and is preserved by the permitted operation sequences. Real-valued
observables that factor through the generated projection form a Mathlib
subalgebra, proved stable under the operations and their sequences. Network
output, for each fixed in-domain input, belongs to that subalgebra.

## Checkpoint-derived calibration example

The practical update instance is an online delta rule for the affine score
**before the network's final ReLU**, with hidden features frozen:

```text
z = (h0(input), h1(input), h2(input), h3(input), 1)
score(a) = sum_j a[j] * z[j]
loss(a)  = (score(a) - target)^2 / 2
a'[i]   = a[i] + rate * (target - score(a)) * z[i]
```

This is the usual squared-score-error gradient step. Lean proves the exact
affine/delta-rule identity; it does not formalize a general automatic
differentiation system or the correctness of an optimizer implementation.

The example uses physical row 1 of the published
`python_training/data/Training_Data_Normalised.csv`, decoded as exact decimal
rationals, the actual checkpoint's exact rational weights, target `3/4` from
that row, and an explicitly chosen rate `1/100`. The six sample coordinates
are checked to lie in the domain. Hidden features are recomputed in Lean
from `Adversarial.original`; a generic lemma links this rational hidden-layer
evaluation to the existing real semantics.

The features are approximately `(0, 0, 1.6370777744, 0, 1)`. The synthesized
update state retains `{a0, a2, bias}`. The exact initial score is approximately
`0.7378555422`; one step moves it toward `0.75`. Lean checks both that a retained
weight changes and that this sample's exact squared-score loss decreases.

This is an illustrative new calibration objective, not a reproduction of
the authors' training procedure. It uses a published training row, not held-out
evaluation. A one-sample loss decrease does not establish accuracy improvement,
convergence or preservation of controller properties.

## Reproduction

From the repository root, using the existing pinned Lean/mathlib installation:

```sh
python3 -B contribution/network_reduction/update_synthesis/verify.py
```

The default upstream checkout is `~/projects/ppg-lab/external/SAIV_2025_Alsomitra`.
Use `--upstream /path/to/SAIV_2025_Alsomitra` to override it. The calibration
CSV must match its pinned checksum. The experiment uses the Python standard
library and existing Lean dependencies; it does not run PyTorch or ONNX.

Every verifier run creates a fresh directory under
`contribution/.build/update_synthesis/attempt-NNN/`. It snapshots the inputs,
generates the four case modules, rebuilds local Lean dependencies, audits all
new theorem roots and records exact arithmetic replay. The current result is
[the separate verification receipt](../../results/update_synthesis_verification.json).
Failed attempts and deliberately rejected compiler controls remain available.

To generate another case without claiming it has been proved:

```sh
python3 -B contribution/network_reduction/update_synthesis/synthesize.py \
  contribution/network_reduction/update_synthesis/examples/coupling.json \
  --output-dir contribution/.build/update_synthesis/my-case \
  --name MyCase
```

This writes `MyCase.lean` and `MyCase.json`, with `proof_status: NOT_RUN`.
Use a fresh output directory/name. The example verifier demonstrates the
subsequent compilation and audit procedure; successful generation alone
does not mean the Lean proof was checked.

## Validation and boundaries

The four instances include a one-round and a transitive dependency closure.
Finite exact replay compares full and packed implementations on zero states,
basis states, all sign vectors, and words of length at most four. Calibration
also includes the actual trained head. All 32 masks are enumerated per case
as a small-instance cross-check of the generic minimality theorem.

Two negative compilation controls deliberately remove a required coordinate
and corrupt a generated packed coefficient. They must fail their Lean proof
obligations. Input-reader controls reject malformed or unsupported operations.
Only the standard `propext`, `Classical.choice` and `Quot.sound` axioms are
permitted in the transitive proof audit. No second-kernel check is claimed.

The JSON reader/emitter and CSV adapter are not verified parsers. Lean proves
the emitted literal problem, packed implementation and explicit checkpoint
feature bindings. Source hashes make this translation boundary inspectable.
Arithmetic is exact rational/real; no new float32 equivalence, hardware speedup
or hidden-layer retraining result is claimed.

Dependency closure and affine restriction are standard techniques. This work
is a mechanized construction and checkpoint-linked experiment; it does not
establish priority for pruning or model reduction. Relevant prior directions
include [formal pruning](https://arxiv.org/abs/2105.13649) and
[bisimulation-based reduction](https://arxiv.org/abs/2110.03726).

## Source map

- [AffineRetention.lean](AffineRetention.lean): terminating synthesis, soundness,
  necessity, coordinate leastness, sequences, RR and stable observable algebra.
- [NetworkRetention.lean](NetworkRetention.lean): actual network bridge, masks,
  rejection result and general delta-rule identity.
- [RationalFeatures.lean](RationalFeatures.lean): exact checkpoint feature evaluation.
- [synthesize.py](synthesize.py): restricted input language and packed-code emitter.
- [experiment.py](experiment.py): sample provenance, generated binding, exact replay.
- [verify.py](verify.py): fresh proof build, audit, negative compilation controls.
- [PLAN.md](PLAN.md): scope chosen before the experiment.
