# Reproducing the selected fitted core

The proof package fixes one successful controller: a `6-4-2-1` fitted core
and the continuous output-repair block with slope 64. This document records
that selected configuration. It is not a claim that every initialization or
optimizer setting succeeds.

## Inputs and initialization

- Start from the exact Adversarial reduced parameters in
  `../../network_reduction/Adversarial.lean`.
- Use the pinned 360-row normalized CSV and all original target labels.
- Keep ReLU after each of the three affine layers.
- Use `split_units` in [train.py](train.py). It copies the third first-layer
  neuron into the fourth with a bias offset of 0.02 and zeros its outgoing
  weights. It copies the second second-layer neuron into the first with a
  bias offset of 0.02 and splits its output weight equally. These changes
  expose capacity during fitting; this initialization is not asserted to
  preserve the original function.

Optimization minimizes MSE of the COMPLETE repaired output against the
original labels. The output block is fixed throughout training. No data
labels are changed for this fit.

## Optimizer settings

The recorded environment used Python 3.11.18, PyTorch 2.15.0 and NumPy 2.4.6,
CPU execution, float64 tensors, one PyTorch thread and seed 0.

1. Run 16,000 full-batch Adam updates with initial learning rate 0.002.
2. Halve the rate after each 4,000 updates and retain the best evaluated core.
3. Starting from that core, run PyTorch L-BFGS with learning rate 1,
   at most 1,000 iterations, history size 50 and strong-Wolfe line search.
   Gradient tolerance is 1e-12 and change tolerance is 1e-15.
4. Retain the better evaluated fit, then round each parameter to the nearest
   multiple of `1/65536`, using ties-to-even rounding.

The historical selected fit is [FIT.json](FIT.json). Its `scope` field says
exact proof was pending when the fit was recorded; it is an unchanged
fitting record. Current formal verification is in [RESULT.json](RESULT.json).
[CANDIDATE.json](CANDIDATE.json) contains the frozen rational parameters and
binds the selected fit by SHA-256.

## Commands

From the repository root, prepare the reference data:

```sh
python3 contribution/model_repair/prepare_inputs.py --reference-only
```

With the numerical packages installed in a separate environment:

```sh
python3 -B contribution/model_repair/directed_repair/train.py \
  --out contribution/model_repair/results/training-replay
```

The output path must be new. `REPLAY.json` reports package versions, source
and data identities, and whether quantized parameters match the frozen
candidate. The recorded replay reproduced them exactly; see
[TRAINING_REPLAY.json](TRAINING_REPLAY.json).

Optimizer reproducibility across package versions or hardware is separate
from proof replay. To check the published model directly, numerical training
packages are unnecessary:

```sh
python3 -B contribution/model_repair/directed_repair/freeze.py --check
python3 -B contribution/model_repair/directed_repair/verify.py
```

Reference MSE is a fit-set measurement. This experiment does not establish
generalization to unseen trajectories or closed-loop flight performance.
