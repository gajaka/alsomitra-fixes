# Verified repair of an Alsomitra controller

Start with the [worked repair walkthrough](directed_repair/README.md).
It follows the published controller, a concrete violation, an explicit
output-repair block, and the Lean proofs of the final construction.
Each step links its code, mathematical definitions and checks.

```text
INITIAL: published Adversarial controller

6 inputs --> 6 ReLU --> 4 ReLU --> 1 ReLU --> original output

FINAL: fitted smaller core plus continuous output correction

6 inputs --> 4 ReLU --> 2 ReLU --> 1 ReLU --> proposed output --+
    |                                                        |
    +--> d = X+Y --> allowed output interval -----------------+
                                                             |
                                                             v
                                             6-ReLU repair block
                                                             |
                                                             v
                                                   repaired output
```

The complete repaired controller satisfies Above(2) and Below(2) for every
real input in `[0,1]^6`. Its exact reference MSE is approximately 0.001475236,
compared with 0.001532418 for the original checkpoint, on the same 360 rows
used for fitting. A new pruning certificate establishes equality between
the full and reduced fitted cores, including their common repair block.

The added block provides the directional guarantee. The fit provides the
reference-quality result. This changes the architecture and is not a proof
that the fitted core alone satisfies the two requirements. Exact-real,
reference-data, floating-execution and flight guarantees are distinguished
in the walkthrough.

## Reproduce the published result

From the repository root:

```sh
python3 contribution/model_repair/prepare_inputs.py --reference-only
python3 -B contribution/model_repair/directed_repair/freeze.py --check
python3 -B contribution/model_repair/directed_repair/verify.py
```

The first command acquires only the pinned CSV. The second checks frozen
weights, reference inputs and generated Lean definitions. The third rebuilds
the proof using the repository's pinned Lean/Mathlib environment, audits
its axioms and checks deliberate negative controls. Training is unnecessary
for proof replay. Optional training instructions are in
[TRAINING.md](directed_repair/TRAINING.md).

Exact reference execution uses Python's standard library:

```sh
python3 -B contribution/model_repair/directed_repair/runtime.py 0 0 0 0 0 0
```

## Source provenance

The controller and CSV come from
[SAIV_2025_Alsomitra](https://github.com/ckessler2/SAIV_2025_Alsomitra/tree/e9f6f1c52e0e5349455d2b4f69c2015567d3037f),
revision `e9f6f1c52e0e5349455d2b4f69c2015567d3037f`.
The CSV SHA-256 is
`d0b84c0e372a25f7934953ae8adac8db08b7a3b241892a1aa697834f583acbf7`.
Original checkpoint bindings and the underlying reduction theorem are in
[network_reduction](../network_reduction/README.md).

For broader source inspection, the optional full acquisition command remains:

```sh
python3 contribution/model_repair/prepare_inputs.py
```

It obtains hash-checked snapshots of SAIV and
[property-driven-ml](https://github.com/property-driven-ml/property-driven-ml/tree/616df1e5baaabf7b42dc26320c00fb297903c87a),
using [SOURCES.lock.json](SOURCES.lock.json). Existing work copies are preserved.
Original source trees, archives, reference CSV and generated run folders
remain excluded from Git. The full download is not needed for proof replay.

Upstream notices are retained. The framework snapshot includes its original
MIT license; the separate pinned SAIV snapshot has no LICENSE/COPYING file.
The framework's license is not relabeled as applying to that separate tree.
