# A contract for output-layer updates after certified reduction

This extension keeps the trained adversarial model's two hidden layers and
their inactive-neuron certificate fixed. It specifies which changes to its
output parameters can be executed using only the smaller parameter state.
Its proof sources and verification receipt are separate from the original
fixed-checkpoint experiment. Section 6 of the expanded
[network-reduction report](../REPORT.md) now presents this extension alongside
the original reduction results.

There are three different obligations:

1. Changing the output layer preserves the existing hidden-neuron certificate.
2. Each allowed full-state update has an exact implementation on the reduced
   state.
3. Full and reduced evaluation agree after every finite word of those updates.

The first already follows from the general pruning theorem: `Check` reads
only the first and second hidden layers. The explicit update operations,
state projection, sequence contract and failure boundary are the additional
formal interface developed here. They are not a new pruning algorithm.

## Domain, states and output

The input type is the subtype of real lists in the existing certified box:

```text
D = { x : List Real | InBox Adversarial.domain x }
Adversarial.domain = six copies of [0,1]

S = D x FullHead       FullHead has rational fields a0,a1,a2,a3,bias
V = D x ReducedHead    ReducedHead has rational fields a0,a2,bias

q(x,a0,a1,a2,a3,bias) = (x,a0,a2,bias)
RR(s,t) iff q(s) = q(t)
```

Domain membership includes the six-coordinate shape. Every defined state has
an in-domain input; the modeled operations leave this input unchanged.
The hidden layers, masks and certificate are fixed context, not mutable
fields. The existing adversarial masks remove first-layer indices 3 and 5
and second-layer indices 1 and 3 (zero-based indexing).

Let `h0,h1,h2,h3` be the original second hidden-layer activations. The existing
certificate proves `h1(x)=h3(x)=0` throughout `D`. Therefore the real output is

```text
full(s)    = relu(a0*h0(x) + a1*0 + a2*h2(x) + a3*0 + bias)
reduced(q) = relu(a0*h0(x)        + a2*h2(x)        + bias)
```

The implementation binds this equality to the actual full and reduced
network definitions through `certified_prune`; it is not a replacement
handwritten numerical network. Parameters are rational, interpreted over
real inputs, and the published final ReLU remains present.

## Operations and the sequence contract

Positive examples add externally supplied rational values to output
parameters. Updates of retained coordinates have the corresponding update
on `V`; updates of discarded coordinates leave `V` unchanged. The operation
arguments are shared inputs, not functions secretly inspecting discarded
state.

For every allowed operation:

```text
q(step(op,s)) = reducedStep(op,q(s))
```

Induction gives the same equation for every finite operation word. Combining
it with output factorization gives:

```text
full(run(word,s)) = reduced(reducedRun(word,q(s)))
```

The accompanying equivalence `RR` is preserved. These are supplied-word
contracts. A controller that chooses operations adaptively from forgotten
coordinates needs a separate policy-factorization proof.

## The actual observable subalgebra

The algebra is a Mathlib subalgebra of real-valued functions on `S`:

```text
B_q = { g composed with q | g : V -> Real }
```

Composition is an algebra homomorphism and `B_q` is its range. Stability
means that precomposing a member with an allowed operation is still a
member. The all-word theorem extends this to finite sequences.

This is the same composition/range construction as the PPG observable
algebra. The extension remains self-contained in this repository and adds
no PPGraph package dependency or full graph-controller claim.

Properness is witnessed by two states differing only in a discarded
parameter. The observable reading that parameter cannot factor through `q`.
Thus the state projection genuinely forgets parameter information, even
though the domain-wide zero activations themselves are reconstructible.

Stability does not require every observable to remain constant. A retained
coordinate can change while the algebra remains stable. Full/reduced
agreement also does not preserve the old output value or an old safety
threshold after changing retained parameters.

## A change that cannot descend to this view

Consider the full-state operation:

```text
bad: a0 := a0 + a1
```

Choose the same in-domain input and zero retained parameters, with `a1=0`
in one state and `a1=1` in another. Their original views agree. Their views
after `bad` differ because their retained `a0` values are 0 and 1.

Consequently no function `V -> V` can satisfy `q(bad(s))=f(q(s))` for every
full state. The observable subalgebra is not stable under this operation.

This operation still changes only the output head, so the hidden-neuron
certificate remains valid. The counterexample separates certificate
preservation from autonomous reduced-state updating. It does not assert
that manually synchronized full and reduced heads stop computing the same
real function.

## Verification and boundaries

Run from the repository root with the existing pinned Lean/mathlib setup:

```sh
python3 -B contribution/network_reduction/output_updates/verify.py
```

The runner builds a fresh local dependency chain into a new attempt directory
under `contribution/.build/output_updates/`, audits the declared theorem roots
and preserves the attempt's source snapshots and logs. Its separate summary
is `contribution/results/output_update_verification.json`. It checks that
the existing network-reduction sources and receipt remain unchanged.

Only `propext`, `Classical.choice` and `Quot.sound` are permitted in accepted
axiom reports. A successful Lean check is not a separate Nanoda replay.
The summary distinguishes a fresh proof build from historical evidence.

The completed [verification receipt](../../results/output_update_verification.json)
reports **PASS** for fresh attempt `attempt-002`: seven local modules rebuilt,
no warnings or errors, and 36 audited roots (31 new public theorem roots,
the local setoid, and four existing results). The axiom union is exactly
`propext`, `Classical.choice`, `Quot.sound`. Two positive and 18 negative
synthetic audit-reader controls also passed. Original reduction source
bindings, receipt and PDF were unchanged during that recorded build.

The main PDF has subsequently been expanded to describe this extension.
The earlier PDF remains preserved in the `attempt-002` source snapshot;
the recorded PDF hash refers to that edition. Proof sources, compiled
artifacts and verification receipts retain their original identities.
The expanded PDF is a documentation revision, not a new proof run.

The first fresh attempt compiled every Lean module successfully but failed
in the report reader on a legitimate multiline axiom list. Its separate
FAIL receipt and logs are preserved. The reader was corrected to accept
complete wrapped lists while rejecting every unconsumed or malformed
fragment; the successful fresh attempt uses that corrected reader. Earlier
development proof attempts are retained separately under `dev/`.

The main declarations in [OutputUpdates.lean](OutputUpdates.lean) are:

| Obligation | Declaration |
| --- | --- |
| The input domain is inhabited | `input_nonempty` |
| Output heads leave the certificate valid | `head_certificate` |
| Updated actual network definitions agree | `all_output_heads` |
| Each allowed update descends | `operation_factors` |
| Every compatible update family descends through finite words | `compatible_run_factors` |
| Full/reduced evaluation agrees after the sequence | `sequence_agreement` |
| The local relation RR survives the sequence | `RR_preserved` |
| The actual subalgebra is stable and proper | `view_algebra_stable`, `view_algebra_proper` |
| The bad update has no exact reduced implementation | `bad_no_reduced_step` |
| The same bad update still preserves the hidden certificate | `bad_preserves_certificate` |
| The bad update breaks algebra stability | `view_algebra_not_stable_bad` |
| Stability is distinct from fixedness | `view_algebra_not_fixed`, `erased_updates_fixed` |
| The actual network output can change from 0 to 1 | `zero_head_output`, `output_can_change` |

No hidden-weight updates, optimizer equivalence, training guarantee,
universal float32 equality, physically reachable input characterization,
speedup, MT process, runtime bound or scientific priority is established.
Existing float32 counterexamples and the ONNX adapter boundary remain as
documented in the original reduction report.
