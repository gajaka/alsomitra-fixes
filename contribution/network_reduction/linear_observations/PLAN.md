# Linear observations and optimizer memory

This continuation tests whether linear combinations can retain strictly less
state than coordinate selection while preserving a specified optimizer.
All earlier experiments, sources, reports and receipts remain unchanged.

## Fixed scope

- Frozen certified hidden layers of the actual adversarial checkpoint.
- Rational output weights plus momentum: ten scalar state coordinates.
- Squared pre-final-ReLU score loss and an explicitly chosen coupled penalty
  `lambda * (a0 + a1 + a3)^2 / 2`. This is a new experiment objective, not the
  published training algorithm.
- Exact linear-observable closure with proof-carrying row derivations,
  reduced affine maps and a checked minimal invariant row space.
- A symbolic momentum quotient theorem for arbitrary rational features of
  the form `(h0,0,h2,0,1)` and arbitrary rational update parameters.
- A separate adaptive-normalization counterexample, if it can be checked,
  to test the boundary of the same aggregate observation.

## Comparison and falsification

Use the previous exact coordinate-retention algorithm as the baseline on
the identical affine system. Compare retained scalar dimensions, not runtime
or bit-level memory usage. Test both ordinary momentum and the coupled case.
Bind a concrete operation to checkpoint-derived features and verify that
the generated rows/matrices implement it. Run exact finite replay separately
from universal proofs. Incorrect row derivations and reduced coefficients
must fail verification.

After the fixed-operation instances, replay the first eight published CSV
rows in their original order, twice, from the actual head with zero momentum.
This choice is fixed before that replay; it is not an accuracy benchmark.
Compare the affine implementation with an independent direct momentum formula
and the aggregate-state update, using exact fractions.

## Interpretation

Invariant row-space closure and linear lumping are established methods;
CLUE (arXiv:2004.11961) is a relevant broader direction for polynomial ODEs.
This experiment concerns discrete optimizer updates and their mechanized
connection to a pruned neural network. A positive result would strengthen
the case study; it would not establish a new general reduction theory,
an accuracy improvement, full-network retraining or universal float32 safety.

## Follow-up prompted by the aggregate update

After obtaining the symbolic momentum quotient, test the general transport
rule for arbitrary factored rational gradient functions. A projection `u=B*a`
requires the Gram factor `B*B^T` in the reduced gradient update. Prove this
correspondence and its extension to finite varying-update sequences; bind
the concrete checkpoint head's gradient to that factorization. Include a
counterexample to using the uncorrected reduced gradient. This follow-up was
chosen after the earlier result, not preregistered as part of the first test.
