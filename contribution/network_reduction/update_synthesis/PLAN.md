# Update-aware coordinate retention: first experiment

The experiment extends the checked adversarial checkpoint reduction with
an executable synthesis procedure for a finite family of rational affine
parameter updates. Existing proofs, receipts, checkpoints and report PDFs
remain unchanged.

## Contract

- State coordinates range independently over the rationals. Operations are
  simultaneous affine maps, described by exact matrices and offsets.
- Start from the output-head coordinates needed for network evaluation:
  `a0`, `a2`, and `bias`. The input and certified hidden layers stay fixed.
- Close this set under nonzero matrix dependencies of all supplied operations.
- Generate the restricted affine maps and prove that projection commutes
  with each operation and every finite sequence.
- Prove leastness among coordinate projections containing the initial set.
  This is not minimality among all possible abstractions or neural networks.
- Transfer the actual checkpoint's output factorization and certificate,
  and prove stability of the generated observable subalgebra.

## Instances and falsification

1. Independent affine shifts: retain the three evaluation coordinates.
2. `a0 := a0 + a1`: automatically retain `a1` as well.
3. Add `a1 := a1 + a3`: retain all five coordinates through transitive closure.
4. A rational delta-rule calibration of the output head with frozen hidden
   features: retain three coordinates. Define the score before the final
   ReLU explicitly; do not claim this is the upstream training objective.
5. Reject deliberately incomplete masks. Exhibit equal-view states whose
   next retained values differ for the rejected coupling.

The algorithm and universal soundness results will be checked in Lean.
Finite exact-arithmetic replay supplements those proofs. Any practical
calibration example will identify its input, target and learning rate;
no improved accuracy, hidden-layer retraining, float32 equivalence or
methodological priority is assumed.

## Evidence

Use a separate fresh build and receipt. Audit exported theorem roots for
unapproved axioms. Retain failures and source snapshots. No changes to
the earlier verification receipts, no publication, commit or push.
