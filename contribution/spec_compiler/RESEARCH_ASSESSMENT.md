# Feasibility and novelty gate — 2026-11-05

**Decision: the narrow verified component is technically feasible and useful
as a local contribution; a standalone novel research contribution is NOT
ESTABLISHED.** This experiment does not justify starting a large new framework.
It has no PPGraph dependency or objective. Numerical backend refinement is
outside this experiment.

## What was tested

Can one executable implementation preserve the meaning of a bounded-comparison
specification through Boolean region compilation, positive affine coordinate
normalization, and membership checking, for an entire explicitly defined
language rather than only one frozen neural network?

The Lean prototype proves this for Boolean combinations of axis comparisons
with constant bounds. Its core theorem is polymorphic over coordinate types
and ordered fields. Its rational instance is executed. The Alsomitra bridge
proves equality with the existing Property2 input contract for all rational
anchors, thresholds, positive normalizers and input points. The proof does not
depend on a trained model, network architecture or arithmetic kernel.

The test deliberately retains disjoint components and strict endpoints.
Replacing a union by its bounding hull, dropping a component, closing a strict
boundary, or normalizing twice changes membership on checked witnesses. These
are constructed regression controls, not newly discovered upstream bugs.

## Prior work changes the novelty assessment

| Primary source | Relevant existing result | Implication for this experiment |
| --- | --- | --- |
| Flinkow et al., [A General Framework for Property-Driven Machine Learning](https://arxiv.org/html/2505.00466v2), Sections 3 and 5.2 | Combines input-region specifications with logical losses. Discusses geometric limitations, formal guarantees and supported logical fragments. | Our prototype is a narrow executable formalization around this interface; it does not introduce property-driven training. |
| Daggitt et al., [Vehicle: Bridging the Embedding Gap](https://drops.dagstuhl.de/storage/00lipics/lipics-vol337-fscd2025/html/LIPIcs.FSCD.2025.2/LIPIcs.FSCD.2025.2.html), Sections 2 and 4.2.4 | Handles problem/input-space translation. Section 4.2.4 explicitly reports Agda proofs of soundness for training and verifier compilation and their logical correspondence. | It would be incorrect to present semantic preservation between one specification, loss and verification as an unaddressed idea. Merely doing a smaller version in Lean does not establish research novelty. |
| Affeldt et al., [Taming Differentiable Logics with Coq Formalisation](https://arxiv.org/html/2403.13700v2), Sections 3–4 | Formalizes differentiable-logic syntax, interpretation and soundness, including difficulties with negation and choices of truth criteria. | Our closed-fragment loss theorem and strict-boundary observation should not be advertised as the first sound treatment of logical loss semantics. |
| [Vehicle official tutorial](https://vehicle-lang.github.io/tutorial/chapters/introduction/) | Describes the workflow from one specification through training, verification and ITP integration. | A proposal to provide that workflow alone substantially overlaps existing infrastructure. |

These are primary-source claims checked on 2026-11-05. This is a bounded
literature review, not an exhaustive novelty search. We have not audited the
current Vehicle compiler or replayed its Agda proofs. In particular, this
experiment establishes no missing feature, defect or performance disadvantage
in Vehicle. Statements about its formalization above are attributed to the
2025 paper, not inferred from absence of a feature in a documentation search.

## A precise boundary exposed by the prototype

The exact Boolean checker handles strict and non-strict bounds. A separate
positive fragment with non-strict bounds has a nonnegative continuous loss
whose zeros coincide exactly with satisfaction. Its normalization and checker
agree on that truth criterion.

The theorem `strict_boundary_obstruction` proves that no continuous
real-valued function can have exactly `{x | x < 0}` as its zero set. The reason
is the standard closedness of continuous zero sets. This is a restriction on
**continuous loss plus exact zero-as-truth**, not on every possible loss
semantics, discontinuous penalty, margin convention or verifier. It is not
presented as a new topological theorem or a refutation of differentiable-logics
research. It helps prevent an overbroad claim for our own compiler.

## What would justify another research phase

A further phase should begin with one demonstrable difference, for example
a specific required specification/translation that an existing implementation
cannot handle, or independently checkable evidence for an actual translation
that its current proof interface does not cover. The difference must be
established from source and a reproducible case. A fair existing-tool baseline
must receive the same specification and assumptions.

We have not found such a distinguishing case in this gate. Therefore the
present outcome is a checked reference component and an explicit scope result,
not a new general theory or a demonstrated advantage over Vehicle/LDL. The
existing two Alsomitra implementation corrections retain their separate value.

## Work deliberately not claimed

- No automatic general sampler, projection algorithm, or efficient canonical
  interval representation has been implemented. There is an exact candidate
  gate; its soundness does not imply efficient generation of satisfying points.
- No nonlinear or coupled-coordinate constraint support, alternating
  quantifiers, negative/zero normalization scales, or approximate arithmetic.
- No optimizer convergence, trained-network guarantee, or statistical sampling
  result follows from pointwise loss/checker equivalence.
- No benchmark against Vehicle, independent second-kernel replay, upstream
  integration, publication, or author endorsement.
