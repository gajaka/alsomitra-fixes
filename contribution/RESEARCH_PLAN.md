# Research direction after the first executable contract

This is a working plan, not a claim that the
following stages have been implemented or proved.

## Current direction — 2026-11-05

The user explicitly excluded PPGraph from this research direction and asked
for a bounded feasibility check of a universal specification formalization.
The active artifact is [spec_compiler/](spec_compiler/README.md), with the
decision and prior-work comparison in
[RESEARCH_ASSESSMENT.md](spec_compiler/RESEARCH_ASSESSMENT.md).

This prototype generalizes the input contract from one fixed property to
Boolean combinations of axis comparisons, with exact open/closed boundaries,
positive affine normalization, an executable rational checker, and semantic
transport for arbitrary output functions/execution relations. Its dedicated
result file records completed checks. It does not depend on a neural network
or on Apple Accelerate. Previously checked network/rounding studies remain
separate, with their original implementation limitations unchanged.

The novelty gate found that Vehicle already reports Agda soundness proofs for
training and verifier compilation; LDL already formalizes logical loss
semantics. Therefore a general "one specification, several equivalent views"
claim is not a new contribution. The prototype is useful checked groundwork,
but a further substantial phase needs a concrete, reproduced distinction from
existing work. No such distinction or practical superiority has been established.

The sections below describe earlier milestones and their boundaries. The
previous proposed PPGraph continuation is no longer part of this plan.

## Present milestone

Establish a small contract whose specification, region compiler, generator,
and checker share executable Lean definitions. Retain the framework's actual
anchor-relative geometry and the code's `vy` coordinate, with explicit empty
regions and normalization units. Reproduce the two observed implementation
failures as negative cases.

The initial implementation is an exact-rational reference backend. Its
theorems apply to that backend. The earlier `lean/` package remains a separate
real-number model and must not be confused with the new executable core.

## Implemented next step: observed PyTorch / float32 values

[FLOAT32_BRIDGE.md](FLOAT32_BRIDGE.md) documents the implementation and its
trust boundary. Eight additional Lean roots specify exact decoding and
pointwise verdicts for observed binary32 values. A Python adapter captures
actual CPU tensor bits, checks proposed candidates through Lean, and binds
inference observations to model/specification/normalization identities.
An optional integration executes the pinned original AlsomitraNet and its
denormalizers, using deterministic untrained weights.

The bridge keeps exact affine interpretation separate from the physical
values already rounded by PyTorch. Tests reproduce a disagreement at the
output boundary. This resolves how these two observations are interpreted;
it does not identify the underlying arithmetic or certify the whole network.

## Universal verification of a fixed network

[universal/](universal/README.md) adds a real affine/ReLU interpretation of the
same frozen, untrained AlsomitraNet parameters. Its certificate covers all
inputs in the fixed anchor-10 Property2 region with 99 leaves. The proof
connects exact parameter decoding, interval inequalities, cover completeness,
and the original input predicate. See the verification report for completed
kernel checks, source hashes and axiom dependencies.

An explicit bounded-error trace relation additionally allows up to `1/1024`
absolute error at every affine neuron result and propagates it through the
network. Applying this theorem unconditionally to every PyTorch execution
requires a universal backend error/refinement proof. The current replay
measures errors at sampled inputs and does not supply that missing proof.

The model is intentionally the unchanged preceding integration artifact.
This result establishes no property of the earlier trained seed-0 checkpoint,
other weights, other anchors, or a model after retraining.

## Remaining numeric implementation work

Choose and document the intended boundary before claiming a refinement:

- An exact-rational checker of observed finite machine values can interpret
  their bit patterns exactly, but does not prove that floating-point network
  execution equals real-number network evaluation.
- A floating-point implementation of the region generator needs a rounding
  analysis. Boundary points, clipping, and normalization cannot be treated as
  exact equalities merely because ordinary tests agree.
- A C interface needs an explicit input/output representation, ownership,
  errors, and semantic binding to the proved functions. Lean-emitted C alone
  is not an independently verified C runtime or a generic PPG monitor.

The first integration now distinguishes pointwise checked input/output pairs
from a universally certified model. Its provenance binding is tested Python
infrastructure, not a machine-checked refinement of arbitrary PyTorch code.
Formalizing the capture/ABI or the floating-point operations would require
additional models and proof obligations.

## Generalization now prototyped

The original `Spec` record is deliberately small. The new `spec_compiler/`
provides typed syntax for axis comparisons and Boolean connectives, exact
union-of-cells semantics and a proved compilation theorem. It retains
inconsistent cells and uses an acceptance gate; it does not yet provide an
automatic sampler/projection algorithm for the general language.

Disjunctions and negations generally do not denote one closed box. Any extension
must represent unions, strict boundaries, and empty regions correctly, or
state and prove the direction of an approximation. Replacing such a region
with its bounding box is not an equivalence.

Existing work on differentiable-logic semantics and Vehicle must be reviewed
before describing novelty. A zero-loss equivalence must be proved for the
selected logical fragment and arithmetic; it cannot be assumed for every
fuzzy logic or approximate optimizer.

## Separate future question, not activated: model updates

The authors explicitly list preserving desired properties under retraining
as future work in [Comparing differentiable logics, Section 5.2](https://arxiv.org/html/2407.03847v2#S5.SS2).
A future experiment must begin with an actually justified initial certificate
for a fixed model and contract. The previously closed seed-0 training run did
not provide such an anchor; this contribution does not restart that run.

This question is not activated by the current specification-compiler gate.
It is not a justification for bringing PPGraph back into this contribution.
Any further research decision must be based on an identified technical gap
and demonstrated initial evidence, rather than assumed training success.
