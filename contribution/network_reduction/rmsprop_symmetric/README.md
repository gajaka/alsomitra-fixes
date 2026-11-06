# RMSProp on equal histories

[SymmetricRMSProp.lean](SymmetricRMSProp.lean) uses the existing full
RMSProp definitions from
[AdaptiveBoundary.lean](../linear_observations/AdaptiveBoundary.lean).
The original obstruction on arbitrary nonnegative histories remains unchanged.

The full real state is `(a0,a1,a2,a3,b,r0,r1,r2,r3,rb)`.
The retained state is `(a0,a1+a3,a2,b,r0,r1+r3,r2,rb)`.
The loss and optimizer are the original boundary example: squared score
loss with features `(0,0,z,0,1)`, target zero, penalty
`(a0+a1+a3)^2/2`, decay `1/2`, rate `1`, epsilon `1`, with neither
centering nor momentum. Each step may receive a different real `z`.

## Invariant and reduced execution

The paired gradients are equal. Consequently:

```text
r1' - r3' = (r1-r3)/2

I(s) := r1 = r3
Valid(s) := every second moment is nonnegative

I(s) ==> I(step(z,s))
Valid(s) ==> Valid(step(z,s))
```

Zero initialization establishes both conditions for every real head.
On the invariant subset, with `u=a1+a3`, `R=r1+r3`, and `g=a0+u`:

```text
R' = (R + 2*g^2)/2
u' = u - 2*g/(sqrt(R'/2)+1)

I(s) ==> q(step(z,s)) = smallStep(z,q(s))
I(s) ==> q(run(word,s)) = smallRun(word,q(s))
```

`word` is any finite list of real inputs. Thus every finite prefix is
covered. The factor two in the numerator and the halving inside the
square root are both required. Reduced moments remain nonnegative.
`lift` supplies a symmetric valid representative for every valid retained
state; it does not recover the forgotten difference between `a1` and `a3`.

`GoodState` is the subtype satisfying `Valid` and `I`. On this subtype,
`RR(s,t) := q(s)=q(t)` is an equivalence relation preserved by the runs.
The range of the pullback algebra homomorphism is a proper subalgebra,
stable under every such run. The proof explicitly exhibits two distinct
heads with the same retained view. Stability does not make outputs fixed.

The earlier asymmetric `(1,97)` witness is proved unreachable from zero
history initialization. It still proves the global impossibility result
when asymmetric valid states are admitted. The positive and negative
results have different state-space hypotheses and are audited together.

## Verification

From the repository root:

```sh
python3 -B contribution/network_reduction/rmsprop_symmetric/verify.py
```

This command also checks the separately scoped
[property-transfer module](../property_transfer/README.md). It rebuilds all
needed local proof dependencies into a fresh attempt, checks their existing
source bindings, audits every new theorem and the old global obstruction,
and rejects a mutated reduced update missing the aggregate factor two.
Only pinned Lake dependencies are reused. No prior local proof binaries
are needed. The standard Python library suffices.

The latest result is
[rmsprop_and_property_transfer_verification.json](../../results/rmsprop_and_property_transfer_verification.json).
Earlier receipts and source snapshots are preserved; revised prose is
not treated as a change to historical proof sources. Inspect the receipt
for actual status, roots, hashes, logs and mutation outcome.

This is exact real optimizer-state correspondence. The square root can
produce irrational heads, whereas the existing checkpoint update model
uses rational heads. No direct RMSProp-to-checkpoint evaluation theorem,
Adam theorem, convergence result, floating-point implementation refinement,
optimizer timing, or new second-kernel replay is claimed here.
