# Transferring controller specifications

[PropertyTransfer.lean](PropertyTransfer.lean) connects the certified
reductions to properties of the original trained controllers. Inputs are
typed by the certified real cube `[0,1]^6`, retaining all six coordinates
in order `[vx,vy,omega,theta,x,y]`.

For any input predicate `P` and input/output predicate `Q`, it proves:

```text
(forall x in D, P(x) -> Q(x,N_original(x)))
    iff
(forall x in D, P(x) -> Q(x,N_reduced(x)))
```

There is also a pointwise equivalence of counterexamples. Both directions
are instantiated for the actual baseline and adversarial checkpoint
definitions. These are transfer theorems: they do not assume or establish
that either trained controller satisfies an arbitrary property.

## Two concrete upstream requirements

The source is the companion repository at
`e9f6f1c52e0e5349455d2b4f69c2015567d3037f`, file
[`vehicle_verification/property_verification/Alsomitra.vcl`](https://github.com/ckessler2/SAIV_2025_Alsomitra/blob/e9f6f1c52e0e5349455d2b4f69c2015567d3037f/vehicle_verification/property_verification/Alsomitra.vcl).
Its executable inequalities, including inclusive boundaries, are followed.
Decimal constants are represented exactly over the reals:

```text
X(x) = 41.232296222734604*x[4] + 0.482420778264618
Y(x) = 45.878638794593570*x[5] - 41.681405266088724

Above(m): Y(x) >= -X(x)+m  ==>  N(x) >= 1/2
Below(m): Y(x) <= -X(x)-m  ==>  N(x) <= 1/2
```

`N(x)` is the normalized command, with the checkpoint's final ReLU.
The source calls these `property1` and `property2`. The latter is **not**
the framework repository's different anchor-relative `Property2`.
No claim is made that all paper versions or specifications use identical
predicates. Matching this selected Vehicle source is a reviewed translation
boundary, not a verified Vehicle parser.

Transfer is proved for every real margin `m`, for each checkpoint.
At margin `2`, explicit inputs prove that both antecedent regions are
nonempty. Nonemptiness is not a network-output proof. In particular, this
module does not claim either universal `Above(2)` or `Below(2)` for the
original checkpoint. Establishing or refuting them is a separate task.

## Subsequent updates

For the existing rational momentum model, the same arbitrary specification
and each counterexample transfer after every finite update sequence.
This uses `MomentumQuotient.network_sequence`, already tied to the actual
certified adversarial hidden layers. It compares the two networks **at the
same current step**. It does not assert that a property of the initial
network is invariant under training.

The real equal-history RMSProp development is a separate theorem. No
connection from its potentially irrational updated heads to the rational
checkpoint-head definitions is assumed. Floating-point correspondence
and closed-loop flight safety are also outside these transfer results.

## Reproduce

```sh
python3 -B contribution/network_reduction/rmsprop_symmetric/verify.py
```

The [combined receipt](../../results/rmsprop_and_property_transfer_verification.json)
records a fresh Lean build, all new theorem audits, historical dependency
bindings, and a reduced-update mutation control. The mathematical transfer
uses equality substitution; no novelty claim is made for this rule.
