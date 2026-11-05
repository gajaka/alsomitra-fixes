# Executable Property2 contract: first specification

Author: Dragan Stosic. Implementation and proofs developed with Codex assistance.

## 1. Objects and arithmetic

The scalar domain is the exact rational numbers, `Q` / Lean `Rat`. Integers
are arbitrary precision. Arithmetic in the formal functions does not use
IEEE floating-point values, tolerances, NaN sentinels, or infinite endpoints.

`Coord` is a six-element type: `vx`, `vy`, `omega`, `theta`, `x`, `y`.
A `Vector` maps these coordinate names to rationals.

`Physical` and `Normalized` are different wrapper types. `normalize` accepts
only a `Physical` point and returns a `Normalized` point. Consequently,
`normalize n (normalize n p)` is ill-typed. A caller can explicitly rewrap raw
coordinates under another type; the type distinction is not a guarantee
against deliberate mislabelling or an incorrect sensor adapter.

The physical domain `D` is the product of these closed intervals:

| Coordinate | Lower | Upper |
| --- | ---: | ---: |
| vx | 0.967568 | 3.489893 |
| vy | -0.607397 | -0.043021 |
| omega | -0.356973 | 0.049180 |
| theta | -0.968479 | -0.068003 |
| x | 0.482421 | 41.714717 |
| y | -41.681405 | 4.197234 |

Every decimal in this table denotes its exact rational value. These are the
six-decimal constants in the pinned code, not the longer-precision paper table.

## 2. Property and normalized representation

`Spec` contains four named rational fields:

| Field | Meaning | Default |
| --- | --- | --- |
| anchorX | Horizontal coordinate of the fixed original anchor | Required |
| bandUpper | Upper end of the anchor-relative `anchorX + y` band | 2 |
| velocityUpper | Upper cap on local `vy` | -3/10 |
| angularUpper | Upper cap on `omega` | -3/25 |

For a specification `s` and a physical point `p`, the predicate is:

```text
Pre(s,p) =
    p in D
    AND 0 <= s.anchorX + p.y <= s.bandUpper
    AND p.vy <= s.velocityUpper
    AND p.omega <= s.angularUpper
```

The candidate's `p.x` remains independent of the anchor. This is the framework's
local region, not the optional candidate-coupled specification. Arbitrary
anchors and thresholds, including infeasible ones, are allowed; empty regions
are handled explicitly. Named fields prevent positional ambiguity at the API,
but do not establish that a human chose the correct numerical specification.

A `Normalizer` has a vector `offset`, a vector `scale`, and a proof that every
scale is positive. It is distinct from `D`: fitted statistics may differ from
the physical domain bounds. For every coordinate `c`:

```text
normalize(n,p)[c]   = (p[c] - n.offset[c]) / n.scale[c]
denormalize(n,z)[c] = z[c] * n.scale[c] + n.offset[c]
```

Both round trips are proved exactly. The default normalizer uses `domainLo`
as offset and `domainHi - domainLo` as scale.

## 3. Compilation and generation

`compile(s)` returns a physical box with bounds clipped against `D`:

```text
lo.y     = max(domainLo.y, -s.anchorX)
hi.y     = min(domainHi.y, s.bandUpper - s.anchorX)
hi.vy    = min(domainHi.vy, s.velocityUpper)
hi.omega = min(domainHi.omega, s.angularUpper)
```

All unspecified bounds equal the corresponding domain bound. `compile_correct`
proves, for every specification and every physical rational point:

```text
point belongs to compile(s)  IFF  Pre(s,point).
```

`Box.Ordered` means `lo[c] <= hi[c]` for every coordinate.
`compile_nonempty_iff` proves this is equivalent to existence of a point
satisfying `Pre`. This is a witnessed nonemptiness result, not an assumption
that every supplied configuration is feasible.

`Unit(t)` means every component of `t` lies in `[0,1]`. `sample(s,n,t)`:

1. Rejects an unordered compiled box.
2. Rejects a point outside the unit cube.
3. Computes `p[c] = lo[c] + t[c] * (hi[c] - lo[c])` in physical units.
4. Normalizes `p` once and returns it.

`sample_sound` proves that every returned point denormalizes to a point meeting
`Pre`. `sample_none_iff` characterizes rejection exactly. `sample_complete`
proves that every normalized rational point whose denormalization satisfies
`Pre` has a valid unit-cube preimage. `encodeUnit` constructs that preimage,
choosing zero on collapsed intervals.

This is a deterministic parametrization. There is no theorem here about a
random-number generator, uniformity, continuous probability, or optimization.

`normalized_compile_correct` proves that normalized box membership is
equivalent to `Pre` after denormalization, for any permitted normalizer.

## 4. Output and monitor

The scalar `output` supplied to the monitor is normalized network output:

```text
physicalOutput(output) = 181/1000 + (12/1000) * output
OutputOK(output)       = physicalOutput(output) <= 187/1000
loss(output)           = max(0, physicalOutput(output) - 187/1000)
```

Theorems prove `OutputOK(output) IFF output <= 1/2` and
`loss(output) = 0 IFF OutputOK(output)`.

For the supplied input `z` and output `o`, `monitor(s,n,z,o)` returns:

| Verdict | Exact meaning |
| --- | --- |
| outside | `NOT Pre(s, denormalize(n,z))` |
| satisfied | `Pre(s, denormalize(n,z)) AND OutputOK(o)` |
| violated | `Pre(s, denormalize(n,z)) AND NOT OutputOK(o)` |

Each row is proved as an equivalence. No output is calculated by a network in
this module. The caller must bind the supplied output to the corresponding
input and model execution. `satisfied` certifies the checked pair under these
definitions; it is not a proof about every input or an autonomous drone.

## 5. JSON-lines interface

One JSON object is read per line and one reply is written. Rational values
must be integer or `numerator/positive-denominator` strings. Vectors contain
exactly six entries in the coordinate order given above.

All actions require `action` and `anchor`. Optional fields are `band_upper`,
`velocity_upper`, `angular_upper`, and `output` (default `1/2`). A
`normalization` object may supply six-element `offset` and `scale` arrays;
all scales must be positive. Unknown fields are rejected.

| Action | Additional required field | Result |
| --- | --- | --- |
| bounds | None | Physical/normalized bounds and `nonempty` or `empty` |
| sample | unit | Candidate and observation, or rejection |
| encode | physical | Unit coordinates, or rejection for a point outside `Pre` |
| monitor | normalized | Physical point, precondition result, output, loss, verdict |

Malformed input produces an `error` reply. Empty regions and out-of-cube
sampling requests produce `rejected`. Parser correctness, IO behavior, and
resource bounds are not included in the Lean theorems.

## 6. Trust and relation to earlier work

The proof checker validates statements about the actual definitions in
`Property2.lean`. The source is executable: it contains no noncomputable core,
unchecked proof placeholder, custom axiom, or foreign implementation override.
The audit allows only Lean's usual `propext`, `Classical.choice`, and `Quot.sound`.

Execution additionally trusts Lean's evaluator/compiler/runtime, the imported
dependencies, and the host environment. The JSON adapter is independently
tested with Python `Fraction` predicates. This is not a second-kernel audit.

The result is a specialized compiler for the `Spec` record, not a compiler for
arbitrary first-order formulas. It does not establish equality with PyTorch's
float32 behavior, trained-network correctness, loss convergence, or preservation
under retraining. Those require separate definitions and evidence.
