# Exact specification compilation experiment

This experiment implements specification compilation and reference checking
in Lean, independently of inference backends.

Detailed reference-checker guide with the worked example:
[PDF](docs/REFERENCE_CHECKER.pdf),
[editable source](docs/REFERENCE_CHECKER.md),
[runnable Lean example](docs/Example.lean).

An example taken directly from the paper is available in
[ACAS Xu input-region checking](acas/README.md)
([PDF guide](acas/ACAS_CHECKER.pdf)). It compares Equations (7)
and (8), exhibits two counterexamples, and proves that corrected bounds
agree with the source predicate for every rational input. Its standalone
runner needs only the pinned Lean/Mathlib setup and Python's standard library:

```sh
python3 -B contribution/spec_compiler/acas/verify.py
```

**Technical result:** an executable rational compiler/checker with general
Lean proofs of semantic preservation. **Research result:** methodology strongly
overlaps Vehicle/LDL; novelty remains unestablished. Read
[RESEARCH_ASSESSMENT.md](RESEARCH_ASSESSMENT.md) before extending the project.
The actual check status and source hashes are in
[region_compiler_verification.json](../results/region_compiler_verification.json).

## Objects and supported language

For a coordinate type `i` and scalar type `K`, inputs are functions `i -> K`.
The syntax permits four axis comparisons with constant thresholds:

```text
x[i] <= k    x[i] < k    x[i] >= k    x[i] > k
TRUE, FALSE, AND, OR, NOT
```

The semantic compilation theorem holds over any linearly ordered scalar
type. Affine-normalization and loss theorems use an ordered field; this
includes mathematical reals and exact rationals. Executed examples use `Rat`.
There are no assumed network weights, dimensions, inference backends, or
per-neuron error budgets in this theorem.

`RegionSyntax.lean` compiles a formula to a finite union of cells. A cell is
stored as a list of axis-bound literals interpreted conjunctively. It is an
exact box description, possibly unbounded or empty. It is not a canonical
lower/upper array. Redundant cells and overlaps remain representable. The
compiler distributes conjunction over unions and pushes negation using
polarity and strict complements. In the worst case this DNF construction
grows exponentially; no scalability theorem is claimed.

For every formula and valuation, the proved statement is:

```text
membership(compile(formula), x) <-> meaning(formula, x).
```

An enclosing physical domain can be supplied as another conjunct. A hull
cannot silently replace a nonconvex union while retaining this equivalence.

## Normalization, checking and transport

`RegionNormalization.lean` defines positive coordinate-wise affine changes:

```text
z[i] = (x[i] - offset[i]) / scale[i],       scale[i] > 0
x[i] = z[i] * scale[i] + offset[i]
```

`Physical`/`Normalized` and `PhysicalSpec`/`NormalizedSpec` are different types.
The public `normalizeSpec` accepts a physical specification, so its output
cannot simply be passed back into that same function. Explicitly rewrapping
the contents can circumvent this distinction; a counterexample documents that
limit. Scale positivity is an explicit proof obligation, not a hidden runtime
assumption.

Thresholds transform algebraically; logical structure and strictness are
preserved. `normalization_compilation_commute` proves semantic agreement of
compiling before or after normalization. `pipeline_correct` connects the
compiled normalized region directly to the original physical predicate.

`RegionCheck.lean` provides the Boolean membership algorithm and proves:

```text
checkNormalized(n, specification, z) = true
    <-> specification.holds(denormalize(n,z)).
```

`acceptCandidate` is a gate for externally proposed candidates, with an exact
acceptance theorem. It does not generate candidates or establish a probability
distribution. `universal_transport` and `execution_transport` transport a
whole-domain contract between coordinate systems for any output function or
execution relation. They do not assume or prove that an arbitrary neural
network satisfies that contract: they prove equivalence of its formulations.

## Relation to the actual Alsomitra contract

`RegionAlsomitra.lean` expresses the original anchor-relative Property2 in
this language and proves agreement with `Property2.lean`. Quantification is
over all rational anchors and thresholds, all positive normalizers and all
normalized points, including infeasible specifications. It retains the
original six-decimal domain and `vy` coordinate. Candidate-coupled geometry
is not substituted for the framework's anchor-relative geometry.

## The loss boundary

`RegionLoss.lean` defines a separate positive fragment with non-strict upper
and lower bounds. Hinge penalties interpret atoms, addition interprets AND,
and multiplication interprets OR. It proves nonnegativity, continuity over
reals, and exact zero-loss equivalence with the logical predicate. After
normalization the zero-loss test agrees with the same compiled checker.
No claim of differentiability everywhere, desirable gradients, floating-point
evaluation accuracy or training convergence is made.

Strict bounds remain supported by the checker but are not silently compiled
into the same zero-loss promise. `strict_boundary_obstruction` proves the
standard fact that a continuous real-valued loss cannot vanish exactly when
`x < 0`: its zero set would have to be both that open half-line and closed.
This is a scope theorem, not a newly discovered limitation of all loss methods.
The closed fragment is sufficient; no maximality claim is made.

## Concrete example and negative controls

The constructed scalar contract is:

```text
physical region:   [10,12] UNION (18,20]
normalization:    z = (x-10)/10
normalized region:[0,1/5] UNION (4/5,1]

physical x       normalized z       accepted
10               0                  yes
11               1/10               yes
12               1/5                yes
15               1/2                no  (gap)
18               4/5                no  (strict boundary)
19               9/10               yes
20               1                  yes
```

`RegionExamples.lean` proves these decisions in the kernel. Additional
theorems expose membership changes from taking the hull, closing the strict
boundary, dropping a component and normalizing twice. An inconsistent region
is proved to reject every point. These deliberate mutants are not reported
as additional defects in Rosemary's code or in Vehicle.

## Reproduce and inspect

Use the existing Lean 4.35.0 / pinned Mathlib installation in `../../lean/`:

```sh
# From the alsomitra-fixes repository root:
python3 -B contribution/spec_compiler/verify.py
```

For a fresh checkout, first follow [Section 10 of the guide](docs/REFERENCE_CHECKER.md#10-reproduction-and-verification-status):
prepare the pinned Lean/Mathlib dependencies and run `contribution/verify_float32.py`
in a Python environment with PyTorch. The current runner needs that script's
local `Property2` artifact and verification receipt. This setup dependency does
not make the compiler's mathematical theorems depend on PyTorch.

The verifier checks the prior Property2 source/object binding, rebuilds six
Lean modules, audits 42 theorem roots, and runs the actual rational compiler
and checker through `RegionMain.lean`. The replay compares 812 source formulas
under three normalizers and nine probes with an independent Python `Fraction`
interpreter, plus the seven disconnected-region probes: 21,931 comparisons.
These finite execution checks supplement, rather than replace, the universal
Lean theorems. They do not constitute a formal proof of Lean's runtime/compiler
or of the JSON encoder and Python checker.

The audit accepts only `propext`, `Classical.choice`, and `Quot.sound`; no
`sorry`, unchecked native-decision axiom or external solver assertion is
accepted. Four malformed-audit controls test missing, duplicate and untrusted
results. Raw finite replay is under ignored `.build/`; its digest, example
output, sources, artifacts and theorem dependencies are retained in the result.
