# Lean real-number model and axiom audit

Toolchain: Lean 4.35.0, Mathlib `v4.35.0`, pinned by `lean-toolchain` and
`lake-manifest.json`. This models selected formulas in upstream
`property-driven-ml` revision `616df1e` and the optional coupled-region variant.
The [main README](../README.md) distinguishes the two confirmed implementation
bugs from the separate specification choices and provides the paper references.

## Audited statements

These are the 12 public theorem roots required by `run_lean_audit.py`.
Names below are relative to namespace `AlsomitraFixes`.

| Theorem | Statement and interpretation |
| --- | --- |
| `upstream_defaults_swapped` | Positional binding stores velocity threshold `2` and band threshold `-0.3` from the defaults. |
| `defect1_y_interval_empty` | The resulting ordered Property2 `y` interval has upper bound strictly below lower bound for every anchor, including clipping and both normalizations. This does not say the upstream sampler stops returning points. |
| `defect2_hi_agrees_iff` | With the correct band threshold `2`, double normalization agrees with single normalization only at `xa = 2 - c`, where `c` is the normalization fixed point, under the theorem's domain hypothesis. |
| `exceptional_anchor_in_domain` | That exceptional anchor, about `1.0712`, lies in the declared `x` domain. |
| `defect2_wrong_at_xMin` | The two upper-bound formulas disagree at `xa = xMin`. |
| `upstream_box_escapes_band` | Every anchor's Property1 rectangle contains a candidate outside the candidate's own `x+y` band. This distinguishes two specifications; the framework explicitly uses anchor-relative rectangles. |
| `Coupled.decode_sound` | For a well-formed coupled region, the unit-square decode map lands in that region. This concerns the optional specification variant. |
| `Coupled.decode_complete` | Every point of a well-formed coupled region has a unit-square preimage. |
| `region1_wellFormed` | The declared candidate-coupled Property1 region meets the geometric hypotheses. |
| `region2_wellFormed` | The declared candidate-coupled Property2 region meets the geometric hypotheses. |
| `fixed_property1_candidates_in_band` | The optional Property1 decode map satisfies its candidate-coordinate band. The historical theorem name is retained. |
| `paper_theta_strictly_inside_upstream` | The paper interval `[-0.786,-0.747]` is strictly inside upstream's effectively clipped interval `[-0.786,-0.068003]`. Author intent is not inferred. |

All 12 roots currently use only `propext`, `Classical.choice`, and `Quot.sound`.
The audit allows a subset of those axioms, including an axiom-free theorem,
and rejects any other axiom, including `sorryAx`.

## Run the build and audit

From this directory, with `lake` on `PATH`:

```sh
lake exe cache get           # initial setup, if Mathlib's cache is absent
python run_lean_audit.py
```

The runner uses only Python's standard library. It checks the Lean version
command's exit status, builds the library, checks the explicit `#print axioms`
request list, and runs `Audit.lean`. A successful run requires:

- Successful version, build, and audit commands.
- No warnings or errors in build or audit output.
- No `sorry` or `admit` proof placeholders in the local library sources;
  comments and strings are ignored by this textual check.
- Exactly the 12 expected axiom reports, with no missing, duplicate, or
  unexpected theorem names.
- Only allowed axioms in every report.

It exits nonzero if any requirement fails. A successful build alone, partial
audit output, or valid-looking reports followed by an audit failure cannot
produce success. Regression controls for those cases are included in
`../tests/test_lean_audit_runner.py`.

Outputs are overwritten for each run:

- `results/lean_theorems.csv`: audited roots and their axiom sets.
- `results/lean_run_info.csv`: command exit codes, build/audit diagnostics,
  expected and observed coverage, missing/duplicate/unexpected roots, and
  forbidden-axiom totals.

Manual commands for inspecting Lean's output directly are:

```sh
lake build
lake env lean Audit.lean
```

The Python implementation tests are separate. From the package root, run
`python run_python_tests.py --upstream /path/to/property-driven-ml` as
documented in the main README.

## Scope and limits

**Model-to-code correspondence is not a theorem.** These Lean definitions were
written from selected Python formulas. The sampled correspondence tests use
another handwritten Python transcription of those formulas; they do not
execute, parse, or automatically authenticate the Lean definitions. Agreement
is supporting evidence, not a verified translation. A change confined to Lean
will not automatically invalidate the Python correspondence tests.

**Arithmetic is over the reals.** Float32/float64 rounding and the Python
membership tolerance are outside this formalization. The proof of an empty
ordered interval must not be confused with the behavior of
`rand*(hi-lo)+lo`, which still returns points when endpoints are reversed.

**The coupled sampling proofs concern `(x,y)` geometry.** They neither establish
that the framework should use this alternative specification nor formalize
the other four coordinate intervals, the attack algorithms, or the sampler's
probability distribution. Conditional `y` sampling after uniform `x` sampling
is not generally uniform by physical volume.

**The theta result is a discrepancy, not a diagnosis of intent.** Whether the
upstream positive bound is deliberate is a question for the authors.

**No training or network guarantees follow.** These proofs do not establish
property satisfaction by a trained network, convergence, an effect on reported
experiments, or Python runner/controller correctness. The axiom audit trusts
Lean and its pinned dependencies; no independent kernel replay is bundled.
