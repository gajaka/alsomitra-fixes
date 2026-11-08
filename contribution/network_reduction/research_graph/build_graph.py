"""Render a source-bound, document-specific research-graph extraction.

The records below are a structured reading of REPORT.md, not the output of
a general PDF parser. Validation checks references, source identities and
recorded evidence; it does not re-prove the mathematical interpretation.
Run with the Python interpreter in contribution/.build/document-tools.
"""
from pathlib import Path
import copy
import hashlib
import json
import re
from pdf_preview import build_pdf_preview

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
REPORT = HERE.parent / 'REPORT.md'
PDF = HERE.parent / 'NETWORK_REDUCTION.pdf'
EXPECTED_SOURCE_HASHES = {
    'REPORT.md': '4ca2c67c02bb0cef9bc5710d64fb67905557b3a91839550ff4be0438da34c878',
    'NETWORK_REDUCTION.pdf': '41e019f788ff478bd5ba48bf13905559edc8e3e541a467a584f2ef57c4e9478d',
}

CASES = {
    'overview': 'Research purpose and document boundaries',
    'robustness': 'Positive robustness on DL2 / Godel',
    'pruning': 'Certified deletion and property transfer',
    'head': 'Output heads, views, RR and stable observables',
    'momentum': 'Linear observations and optimizer memory',
    'rmsprop': 'An obstruction and an invariant restriction',
    'refutation': 'Directional counterexamples survive reduction',
    'repair': 'Construction, fitting and certified repair',
    'boundaries': 'Execution limits and open collaboration questions',
}

# id | kind | case | status | source lines | title | exact scope / content
RECORDS = r'''
G0|goal|overview|partially_addressed|13-44|Preserve, understand and repair controller guarantees|The guide connects certified reduction, information retention during updates, and a separate directional repair. These are several scoped studies, not one universal controller theorem.
Q0|question|overview|composite_partial|13-44|Can useful guarantees survive reduction and adaptation?|A reconstructed organizing question. Its children concern different artifacts; answers must keep those contexts separate.
M0|assumption|overview|declared_model_scope|784-801|Four distinct published checkpoints|DL2 and Godel have linear outputs and widths 6-64-32-1. Baseline and Adversarial have final ReLU and widths 6-6-4-1. All source artifacts use the pinned upstream revision.
A0|assumption|overview|declared_model_scope|720-731|Exact mathematical evaluation|Saved finite binary32 parameters are interpreted as exact rationals; network evaluation uses real arithmetic. The repaired core uses newly frozen rational parameters.
A1|assumption|overview|declared_model_scope|1046-1069|Input domain D = [0,1]^6|Six normalized inputs in order vx, vy, omega, theta, x, y. This cube is a mathematical input domain; physical reachability is a separate issue.
Q1|question|robustness|answered_yes|47-89|Does every permitted input pair satisfy the robustness promise?|For the named DL2 and Godel checkpoints, every pair in D with coordinate differences at most 0.001 must have output difference at most 0.1.
A2|assumption|robustness|declared_contract|57-73|The exact nearby-input contract|P(x,y): x,y in D and every abs(x_i-y_i)<=0.001. Q_N(x,y): abs(N(x)-N(y))<=0.1. This contract concerns two inputs.
C1|construction|robustness|defined|112-133|Absolute-weight sensitivity bound|Propagate unit coordinate-difference bounds through elementwise absolute weight matrices and ReLU nonexpansiveness.
U1|insight|robustness|reported_proved|112-139|Checked bounds cover every permitted pair|DL2 admits multiplier 31 and Godel 26, hence output differences at most 0.031 and 0.026 under P. These are conservative bounds, not optimal constants.
U2|insight|robustness|reported_proved|76-110|The input premise is nonvacuous|Distinct in-domain vectors with all coordinates 0.5 and 0.5005 satisfy the premise.
E1|evidence|robustness|recorded_lean_audit|913-944|Positive-property Lean sources and receipt|Lipschitz.lean and both checkpoint modules; recorded audit with 53 roots. No new Lean run is performed by this graph extraction.
Q2|question|pruning|answered_yes|144-195|Can computation be deleted while keeping the promise?|Composite obligation: show a neuron is inactive, prove output equality, then transfer the property for the same model and domain.
Q2a|question|pruning|answered_yes|149-164|Is the selected neuron inactive throughout D?|For both positive checkpoints, hidden neuron 58 has an exact strictly negative upper bound throughout D.
Q2b|question|pruning|answered_yes|166-181|Does certified deletion preserve every output on D?|Use the checked interval mask and a pruning theorem matching the network's output activation.
Q2c|question|pruning|answered_yes|183-195|Does the reduced network inherit the proved promise?|Substitute equal outputs at both inputs of the already established robustness implication.
C2|construction|pruning|defined|166-176|Pruning certificate and keep mask|A certificate supplies interval bounds and Boolean keep/delete masks. Acceptance is checked; certificate data alone is not proof.
U3|insight|pruning|reported_proved|149-164|Neuron 58 is always inactive|Its preactivation is at most -9057167/134217728, so its ReLU activation is zero on D for both DL2 and Godel.
I1|invariant|pruning|reported_proved|172-195|Output equality under certified deletion|For all x in D, N_small(x)=N_original(x), for the specified fixed checkpoints and accepted pruning transformation.
U4|insight|pruning|reported_proved|183-195|Robustness transfers to the smaller network|The reduced DL2 and Godel networks satisfy the same promise, including the stronger 0.031 and 0.026 bounds.
U5|insight|pruning|reported_structural_count|178-181|Each positive checkpoint loses 39 parameters|Widths change from 6-64-32-1 to 6-63-32-1; parameter count changes from 2561 to 2522. This is not a measured hardware speedup.
E2|evidence|pruning|recorded_lean_audit|913-921|Linear-output pruning and equality proofs|LinearPruning.certified_linear_prune and the checkpoint same_output / reduced_property5 results.
U6|insight|head|reported_proved|198-213|Pruning and sensitivity certificates read different parameters|Pruning inspects hidden-layer bounds and masks. Sensitivity also depends on output weights. Preservation of deletion validity does not preserve robustness after arbitrary weight updates.
A3|assumption|head|declared_model_scope|254-269|Fixed Adversarial hidden layers and rational head|This study uses the certified Adversarial hidden layers, real inputs in D and arbitrary rational output weights. It is a separate context from DL2/Godel.
Q3|question|head|answered_conditionally|254-277|Can irrelevant head weights be forgotten while updates continue?|Evaluate from retained coordinates and require allowed updates, including operation selection, to depend on retained information.
Q3a|question|head|answered_yes|265-310|Can the current output be computed from the view?|The last hidden activations are (h0,0,h2,0); only a0,a2,b affect the output.
Q3b|question|head|answered_conditionally|313-373|Can the next view be computed from the current view?|It can for compatible operations; an operation reading forgotten a1 to change retained a0 supplies a counterexample.
C3|construction|head|defined|270-277|Retained head view|s=(x,a0,a1,a2,a3,b); q(s)=(x,a0,a2,b).
C4|construction|head|defined|293-310|RR is equality of views|RR(s,t) iff q(s)=q(t). This is an equivalence relation on the specified common state space.
C5|construction|head|defined|390-407|Observable subalgebra Obs(q)|All real-valued functions f composed with q. Closed under the algebra operations; this mathematical definition does not make every member executable.
A4|assumption|head|declared_transition_contract|335-362|Allowed updates factor through the retained view|For every permitted T, supply Tbar such that q(T(s))=Tbar(q(s)). Any state-based operation selection must also use retained information.
U7|insight|head|reported_proved|279-310|Different full states have the same view and output|For the two displayed heads, forgotten values differ while the retained head is (2,3,1). RR is stronger than accidental equality of one output.
U8|insight|head|reported_proved|335-362|Compatibility composes through finite update sequences|A compatible step preserves view correspondence. Induction gives full/reduced agreement for every finite sequence of the specified operations.
I2|invariant|head|reported_proved|354-362|RR is preserved by compatible update sequences|RR-related states remain RR-related under the same permitted sequence. Output values themselves may change.
U9|insight|head|reported_proved|417-431|Stable observables remain computable after updates|Stability preserves dependence on the view, not the numeric value of every observable and not a robustness bound.
X1|counterexample|head|reported_proved|319-333|Forgotten a1 changes retained a0|Heads with a1=7 and a1=-4 have the same old view, but a0:=a0+a1 yields 9 and -2. The Lean witnesses use the same pattern with smaller values.
H1|hypothesis|head|refuted_candidate_reconstruction|319-333|Preserving pruning is enough to update using the old view|A candidate claim reconstructed to expose the obstruction: every head operation retaining zero features could be implemented on the old view. The document's bad update refutes it; this is not attributed as an actual historical belief.
U10|insight|head|reported_proved|319-373|A proposed view can be insufficient for an update|No deterministic reduced implementation of the bad update works on all states with this view. The pruning certificate remains valid.
U11|insight|head|reported_proved|364-373|Permitting more updates may require a larger view|The displayed coordinate-retention cases require three, then four, then five head coordinates. Remembering a weight does not require restoring its zero neuron.
E3|evidence|head|recorded_lean_audit|919-933|Head-update and coordinate-retention evidence|OutputUpdates supplies RR, factorization, stable algebra and the bad-update obstruction. The coordinate-retention development checks the enlarged views.
Q4|question|momentum|answered_conditionally|436-494|Can optimizer state be reduced as well?|Use the specified coupled momentum rule, not an assertion about arbitrary optimizers or the authors' original training.
A5|assumption|momentum|declared_model_scope|456-484|Specified rational coupled momentum model|Five head parameters and five momentum values; fixed Adversarial features and the explicitly stated coupled loss. The general correspondence allows rational configurations along a finite sequence.
C6|construction|momentum|defined|456-471|Eight-observation momentum view|Keep a0,a1+a3,a2,b and v0,v1+v3,v2,vb from the ten-dimensional full state.
U12|insight|momentum|reported_mathematical_example|438-454|Optimizer memory affects the next state|Equal current parameters and gradients can have different next parameters when the stored momentum differs.
U13|insight|momentum|reported_proved|473-484|Eight linear observations suffice and meet a scoped minimum|For the concrete coupled instance, eight is minimal among invariant linear observation spaces retaining the required output coordinates. This is not a minimum among arbitrary encodings.
U14|insight|momentum|reported_proved|486-494|Aggregation changes the reduced update rule|If each of two coordinates decreases by one, their retained sum decreases by two. The transport rule includes this factor.
E4|evidence|momentum|recorded_lean_audit|921-934|Momentum correspondence and synthesis evidence|MomentumQuotient and LinearObservations, with the recorded linear-observation audit.
Q5|question|rmsprop|answered_no|496-525|Does the summed-history view work for every valid RMSProp state?|Original scope: all states with nonnegative histories under the specified exact-real RMSProp update.
A6|assumption|rmsprop|declared_model_scope|496-512|Specified real RMSProp rule|Decay 1/2, step size 1, stabilizer 1 outside the square root, specified coupled gradient, nonnegative histories. This is a separate real-valued model.
C7|construction|rmsprop|defined|513-516|Summed-history candidate view|Retain head observations and r0,r1+r3,r2,rb. Only the sum of the paired histories is retained.
X2|counterexample|rmsprop|reported_proved|517-525|Equal history sums yield different next weight sums|Histories (1,97) and (49,49) both sum to 98, but the next retained weight sums are -5/8 and -1/3.
H2|hypothesis|rmsprop|refuted_candidate_reconstruction|513-525|Summed histories determine the next retained state for all valid histories|This is the candidate positive answer to Q5, refuted by X2. It is kept separate from the invariant-restricted answer to Q6.
U15|insight|rmsprop|reported_proved|517-525|No reduced step exists on the proposed view for all valid histories|A formal impossibility for this view and this full-state class, not a claim that every RMSProp reduction is impossible.
I3|invariant|rmsprop|reported_proved|527-535|Equal paired histories are initialized and preserved|r1=r3 holds under zero initialization. Equal paired gradients preserve it through every permitted step.
Q6|question|rmsprop|answered_yes|527-550|Does the view work on equal-history states?|A new, explicitly restricted question. Its positive answer leaves the all-state obstruction intact.
C8|construction|rmsprop|defined|533-542|Restricted state and corrected reduced rule|On r1=r3, each history equals half their retained sum; the reduced update uses that half inside the square root.
U16|insight|rmsprop|reported_proved|544-550|Exact reduced execution holds on the invariant state space|Finite-sequence correspondence, RR preservation and stable observables hold on valid equal-history states. The asymmetric witness is unreachable from the stated initialization.
L1|limitation|rmsprop|not_established|552-554|The real RMSProp example is not connected to the rational checkpoints|Square-root updates may produce irrational parameters; the guide does not assert this bridge.
E5|evidence|rmsprop|recorded_lean_audit|923-935|RMSProp obstruction and invariant-restriction evidence|AdaptiveBoundary.no_reduced_step and SymmetricRMSProp.initialized_run_factors / algebra_stable.
Q7|question|refutation|answered_no|232-251|Do the original Baseline and Adversarial models satisfy both directional requirements at margin 2?|Each selected universal requirement is refuted for each named original model, and the witnesses transfer to their exact reductions.
A7|assumption|refutation|declared_contract|825-837|Physical normalization and margin-2 directional contract|Use the exact position conversions and the source definitions Above(2), Below(2). A directional property concerns one input, unlike robustness.
X3|counterexample|refutation|reported_proved|238-247|Baseline Above(2) interior witness|Input [1/4,1/2,1/2,1/4,1/4,3/4] has physical X+Y about 3.518069 and output about 0.399148, below the required 0.5.
U17|insight|refutation|reported_proved|232-251|Exact reduction preserves an existing failure|Equal outputs at the same violating input transfer the counterexample. The underlying refutation remains a valid mathematical result.
U18|insight|refutation|logical_consequence_extracted|249-252|Repairing that output failure requires changing the output behavior|Exact equality to the violating original cannot remove that same output violation under unchanged predicates and domain.
E6|evidence|refutation|recorded_lean_audit|923-936|Original and reduced directional refutation evidence|Witnesses.lean verifies the four exact original-model violations and the corresponding reduced-model refutations.
Q8|question|repair|answered_with_scoped_quality|556-611|Can directional behavior be repaired while retaining useful predictions?|The composite answer requires universal directional satisfaction plus the explicitly finite reference-quality gate; it does not assert flight safety.
Q8a|question|repair|answered_yes|574-611|Can correction enforce the contract for any core proposal?|Construct a nonempty allowed interval and prove projection membership for every real proposal.
Q8b|question|repair|answered_yes_on_reference|613-642|Does a fitted corrected candidate pass the reference-quality gate?|Compare the frozen controller with the original and constant 0.5 using the unchanged 360 fitting rows.
Q8c|question|repair|answered_yes|644-666|Can the fitted core be reduced again without losing the repair result?|Check a new pruning certificate; compare the full fitted core and its smaller version under the same correction block.
A8|assumption|repair|declared_contract|1046-1120|The repair uses the same stated input interpretation|D=[0,1]^6 and exact physical displacement d(x)=X(x)+Y(x); Above(2) and Below(2), real evaluation.
A9|assumption|repair|declared_model_scope|1123-1136|Nonnegative correction slope; selected value k=64|The generic argument assumes k>=0. The frozen fitted candidate uses k=64.
A10|assumption|repair|declared_data_scope|1229-1239|All 360 reference rows are also fitting rows|Quality is evaluated on the unchanged supplied labels. This is not held-out generalization evidence.
A11|assumption|repair|declared_artifact_scope|1260-1273|Frozen dyadic candidate|The selected fitted parameters are rounded to multiples of 1/65536, ties to even. Proofs and exact reference checks concern this frozen object.
C9|construction|repair|defined|1071-1120|Allowed output set A(x)|For d>=2 require z>=1/2; for d<=-2 require z<=1/2; in the open gap all real outputs satisfy these directional implications.
C10|construction|repair|defined|1123-1155|Nonempty interval I_k(x) inside A(x)|Endpoints stay between 0 and 1 and bracket 1/2. This interval is a sufficient subfamily, not all admissible outputs.
C11|construction|repair|defined|1157-1204|Projection R_k(x,z) and six-ReLU implementation|Clamp the proposed scalar to the input-dependent interval; the explicit neural expression is proved equal to the projection.
U19|insight|repair|reported_proved|1176-1204|Correction has membership, identity-on-interval and idempotence laws|For k>=0 it produces an admissible directional output. Identity applies to proposals already in I_k, not every member of the larger A(x).
C12|construction|repair|defined|1206-1227|Composed controller F_theta(x)=R_k(x,N_theta(x))|The block uses the input displacement as well as the core proposal; the core's scalar output alone is not the full interface.
U20|insight|repair|reported_proved|1206-1227|Every core yields a directionally compliant composed controller|The operator theorem quantifies over every real proposal, so the directional contract holds for arbitrary core parameters with the same block and input interpretation.
I4|invariant|repair|reported_proved|1218-1227|Directional requirements survive core-parameter changes|This preservation is for the stated exact-real composed controller. It does not preserve reference quality, pruning validity or a global sensitivity bound.
X4|counterexample|repair|documented_trivial_solution|1117-1120|Constant 0.5 satisfies the directional clauses|This is a witness that the two clauses alone do not enforce useful reference behavior; it is not a violation of those clauses.
C13|construction|repair|defined|1229-1273|Fit through the fixed block, then freeze|Training proposes a core using complete-controller MSE; freezing fixes exact parameters before the formal quality check.
C14|construction|repair|defined|1277-1291|Reference-quality gate|MSE_T(F)<=MSE_T(original) and MSE_T(F)<MSE_T(constant 0.5), on the named reference collection.
U21|insight|repair|reported_exact_finite_proof|1293-1316|The frozen candidate passes both reference comparisons|Exact bounds separate repaired MSE<=0.001476 from original MSE>=0.001532 and constant MSE>=0.109. The approximate 3.73 percent improvement concerns these fitting rows.
C15|construction|repair|defined|1318-1331|New pruning certificate for the fitted core|The small fitted core is embedded into a full fitted core and four inactive neurons are recertified. Neither core is the unchanged original checkpoint.
U22|insight|repair|reported_proved|1318-1348|Full and small repaired controllers agree throughout D|New core equality is preserved by composition with the same input-dependent correction block.
U23|insight|repair|reported_proved|1365-1386|The final frozen small controller meets the combined contract|Both universal directional clauses and both finite reference-MSE comparisons hold, with their different quantifier scopes preserved.
E7|evidence|repair|recorded_lean_audit|1388-1403|Projection and arbitrary-core contract evidence|ProjectionRepair and RepairNetwork, bound to the saved repair receipt.
E8|evidence|repair|recorded_lean_audit|1398-1409|Frozen quality, recertification and final-contract evidence|RepairReference, RepairedCore, RepairNetwork and RepairResult; recorded 39-root repair audit. Current source hashes can be checked without re-running Lean.
L2|limitation|repair|documented_boundary|1150-1155|Projection adds restrictions beyond the original two clauses|The chosen interval also enforces [0,1] and narrows part of the otherwise unconstrained gap.
L3|limitation|repair|documented_boundary|1357-1361|Repair changes architecture and is not smaller than the old graph|The full repaired graph uses 17 ReLUs, reduced repaired graph 13, old unrepaired graph 11. Core parameters decrease from 75 to 41 only in the stated full/small fitted comparison.
L4|limitation|repair|not_established|690-702|Old view certificates do not automatically cover the repaired core|Earlier update proofs fixed hidden layers. The repair fit changes them; no combined theorem for that adaptation has been established here.
Q9|question|boundaries|open|704-717|Which additional requirement should survive repaired-core adaptation?|The guide proposes a next collaboration: select a requirement and allowed updates, then derive a sufficient view and prove correspondence and preservation.
Q10|question|boundaries|open|720-753|What universal guarantee holds for floating-point execution?|The real-arithmetic theorems and finite runtime comparisons do not establish a universal float32 correspondence or robustness theorem.
Q11|question|boundaries|open|755-778|Does the controller provide acceptable physical flight behavior?|Flight, sensing, normalization, actuators, reachability and unseen-data performance require separate arguments and evaluation.
U24|insight|boundaries|reported_finite_observation|733-753|Runtime observations distinguish the semantics|Baseline batch-one differs on 337 of 8616 tested inputs, max about 4.77e-7. DL2/Godel are bit-identical on 4520 inputs per model in the two tested layouts. Neither observation is a universal theorem.
E9|evidence|boundaries|recorded_finite_execution|733-753|Saved finite runtime comparisons|Runtime sections of the pruning and positive-property receipts; scope is the particular tested models, inputs and execution layouts.
L5|limitation|boundaries|documented_boundary|720-731|Exact-real equality does not guarantee equal rounded executions|Changes in matrix shape may change addition order and intermediate rounding.
L6|limitation|boundaries|not_established|755-778|Reference fit and parameter counts do not establish deployment quality|No held-out repair evaluation, universal float32 guarantee, processor latency improvement or closed-loop flight result is claimed.
L7|limitation|overview|documented_boundary|986-998|Application evidence is distinct from priority or novelty|The guide calls equality transfer, exact reduction and linear observation spaces existing mathematical ideas and makes no priority claim.
'''

# Direction and meaning are explicit. A question-to-insight link is not itself
# a proof; checked derivations are represented by the joint-premise records.
LINKS = r'''
G0|motivates|Q0|Organizing purpose reconstructed from the guide.
Q0|has_subquestion|Q1|One scoped obligation concerns robustness of the positive checkpoints.
Q0|has_subquestion|Q2|One obligation concerns certified deletion.
Q0|has_subquestion|Q3|One obligation concerns future updates using retained information.
Q0|has_subquestion|Q8|A separate obligation concerns useful directional repair.
Q0|has_open_extension|Q9|Adaptation of the repaired architecture is explicitly proposed work.
Q1|assumes|A0|Real evaluation.
Q1|assumes|A1|Unit cube.
Q1|assumes|A2|Specified input/output thresholds.
Q1|uses_construction|C1|Use a conservative bound to discharge the universal property.
Q2|has_subquestion|Q2a|Inactive-neuron obligation.
Q2|has_subquestion|Q2b|Equality obligation.
Q2|has_subquestion|Q2c|Transfer obligation.
Q2a|uses_construction|C2|Intervals and masks encode the candidate deletion.
U3|enables_construction|C2|A nonpositive bound justifies selecting a deletion.
I1|also_yields|U5|The same deletion has an explicit structural count.
U6|motivates|Q3|Inspecting certificate dependencies opens an update question.
Q3|has_subquestion|Q3a|Current evaluation from the view.
Q3|has_subquestion|Q3b|Future evaluation of retained state.
Q3|assumes|A3|Fixed Adversarial hidden-layer context.
Q3a|uses_construction|C3|The view omits zero-feature head weights.
C3|defines|C4|Equality of views defines RR.
C3|defines|C5|Pullback along the view defines the observable algebra.
Q3b|assumes|A4|Compatible operations and compatible operation selection.
Q3b|challenged_by|X1|A particular operation reads forgotten information.
X1|refutes_candidate|H1|Preservation of the pruning certificate does not imply factorization of an arbitrary head update.
H1|candidate_answer_to|Q3b|The candidate unrestricted positive answer is refuted; compatible updates remain valid.
U10|motivates|U11|Enlarging the view is one response to a missing dependency.
U9|motivates|Q4|Learning requires identifying the full optimizer state.
Q4|assumes|A5|Specified momentum model.
Q4|uses_construction|C6|Retain sums of parameters and memories.
U12|motivates|C6|Current parameters alone are not sufficient state.
U13|motivates|Q5|Success for a linear rule motivates testing an adaptive rule; it does not entail success there.
Q5|assumes|A6|Specified real RMSProp update.
Q5|uses_construction|C7|Candidate sum view.
Q5|challenged_by|X2|Identical old views have different next views.
X2|refutes_candidate|H2|The candidate universal summed-history update is impossible on this full state class.
H2|candidate_answer_to|Q5|The candidate positive answer is refuted, while Q5 remains a well-defined answered question.
U15|motivates|Q6|The obstruction motivates an explicitly restricted question.
Q6|refines_domain_of|Q5|Restricts valid histories to the preserved equal-history subset. Does not replace the negative all-state result.
Q6|assumes|I3|Equality must be initialized and preserved.
Q6|uses_construction|C8|The missing individual history can now be recovered from the sum.
U16|bounded_by|L1|No rational-checkpoint bridge is silently inferred.
Q7|assumes|A7|Directional requirements use exact physical normalization.
Q7|challenged_by|X3|One exact Baseline violation; the cited evidence also covers the other three original-model cases.
U17|implies|U18|Preserving the same violating output cannot fix that same contract failure.
U18|opens|Q8|Repair must change behavior on the violating inputs.
Q8|has_subquestion|Q8a|Universal directional correctness.
Q8|has_subquestion|Q8b|Finite reference usefulness.
Q8|has_subquestion|Q8c|Equality of full/small repaired constructions.
Q8|assumes|A8|Domain and input semantics remain explicit.
Q8a|uses_construction|C9|Rewrite the implications as allowed outputs.
C9|refined_by|C10|Construct a nonempty sufficient interval inside the allowed set.
C10|implemented_by|C11|Projection and six-ReLU implementation.
C11|used_in|C12|Compose the operator with a core and the input.
Q8a|assumes|A9|Nonnegative slope, selected value 64.
U20|has_preservation_law|I4|Core changes preserve only the stated directional contract with fixed operator and interpretation.
U20|also_exposes|X4|Directional correctness alone allows the constant solution.
X4|motivates|C14|A separate usefulness gate is required.
Q8b|uses_construction|C13|Fit through the operator and freeze the candidate.
Q8b|uses_construction|C14|Compare unchanged reference labels.
Q8b|assumes|A10|Same 360 rows used for fitting and quality checking.
Q8b|assumes|A11|Exact frozen candidate.
Q8c|uses_construction|C15|Changed hidden parameters require recertification.
U19|bounded_by|L2|Identity is guaranteed only inside the chosen interval.
U22|bounded_by|L3|Use the correct full-repaired comparison baseline.
U23|bounded_by|L6|Universal directional clauses and finite reference quality have different scope.
U23|opens|Q9|The guide asks about preserving additional requirements during adaptation.
Q9|blocked_by_missing_bridge|L4|The old fixed-hidden-layer proof does not cover this new architecture.
U24|motivates|Q10|Actual execution needs its own numerical argument.
Q10|has_boundary|L5|The real and float32 interpretations are separate.
Q11|has_boundary|L6|Deployment evaluation remains open.
Q0|has_open_extension|Q10|Numerical implementation is outside the established mathematical result.
Q0|has_open_extension|Q11|Physical usefulness is not settled by the network theorem.
G0|bounded_by|L7|No priority claim is extracted from a successful formalization.
'''

DERIVATIONS = [
    ('J01', ['A0','A1','A2','C1'], ['U1','U2'], ['E1'], 'robustness', 'Checked bound and a distinct-input witness establish robustness and nonvacuity.'),
    ('J02', ['A0','A1','C2','U3'], ['I1'], ['E2'], 'pruning', 'A checked nonpositive upper bound and mask imply exact pruning equality for the stated output semantics.'),
    ('J03', ['U1','I1','A2'], ['U4'], ['E1','E2'], 'pruning', 'Substitute equal outputs at both in-domain inputs of the same checkpoint contract.'),
    ('J04', ['A3','C3'], ['U7'], ['E3'], 'head', 'Zero hidden features remove the forgotten weights from evaluation; view equality is sufficient.'),
    ('J05', ['A3','A4','C3','C4'], ['U8','I2'], ['E3'], 'head', 'Compose step factorization by induction through each finite permitted sequence.'),
    ('J06', ['U8','C5'], ['U9'], ['E3'], 'head', 'A pullback observable after an update is still a pullback through the reduced update.'),
    ('J07', ['X1','C3'], ['U10'], ['E3'], 'head', 'Two equal old views with different required next views preclude any deterministic reduced step for that bad operation.'),
    ('J08', ['A5','C6'], ['U13','U14'], ['E4'], 'momentum', 'Linear closure and the derived aggregate update establish the scoped reduction and its aggregation factor.'),
    ('J09', ['A6','C7','X2'], ['U15'], ['E5'], 'rmsprop', 'Same-view/different-next-view witnesses prove impossibility for all valid histories on this proposed view.'),
    ('J10', ['A6','I3','C8'], ['U16'], ['E5'], 'rmsprop', 'Initialization, invariant preservation and restricted factorization establish finite-sequence correspondence.'),
    ('J11', ['A7','X3'], ['U17'], ['E6'], 'refutation', 'Check the directional violation and transfer it using the equality theorem for that same Baseline/Adversarial model; do not use the DL2/Godel equality as its premise.'),
    ('J12', ['A8','A9','C9','C10','C11'], ['U19'], ['E7'], 'repair', 'Nonempty interval, inclusion in allowed outputs and projection laws provide membership and the stated operator laws.'),
    ('J13', ['U19','C12','A8','A9'], ['U20','I4'], ['E7'], 'repair', 'Instantiate the universally quantified proposal with any neural-core output.'),
    ('J14', ['C13','C14','A10','A11'], ['U21'], ['E8'], 'repair', 'Exact frozen-data computations establish the two finite reference comparisons; training success itself is not a proof.'),
    ('J15', ['C15','C12','A8','A11'], ['U22'], ['E8'], 'repair', 'New fitted-core equality passes through the same correction operator at the same input.'),
    ('J16', ['U20','U21','A8','A10','A11'], ['U23'], ['E8'], 'repair', 'Instantiate the arbitrary-core directional theorem at the frozen small core and conjoin it with that core\'s finite quality theorem.'),
    ('J17', ['A0','M0'], ['U24'], ['E9'], 'boundaries', 'Recorded finite execution comparisons, with each model and execution layout kept separate.'),
]

ANSWERS = {
    'Q0':['U4','U8','U16','U23'], 'Q1':['U1','U2'],
    'Q2':['I1','U4'], 'Q2a':['U3'], 'Q2b':['I1'], 'Q2c':['U4'],
    'Q3':['U7','U8','U10'], 'Q3a':['U7'], 'Q3b':['U8','U10'],
    'Q4':['U13','U14'], 'Q5':['U15'], 'Q6':['U16'],
    'Q7':['U17'], 'Q8':['U23','U22'], 'Q8a':['U20'],
    'Q8b':['U21'], 'Q8c':['U22'], 'Q9':[], 'Q10':[], 'Q11':[],
}

EVIDENCE = {
    'E1': ('contribution/results/positive_property_verification.json', [
        ('contribution/network_reduction/positive_property/Lipschitz.lean', ['checked_global','nonvacuous']),
        ('contribution/network_reduction/positive_property/DL2Checkpoint.lean', ['property5','reduced_property5']),
        ('contribution/network_reduction/positive_property/GodelCheckpoint.lean', ['property5','reduced_property5'])]),
    'E2': ('contribution/results/positive_property_verification.json', [
        ('contribution/network_reduction/positive_property/LinearPruning.lean', ['certified_linear_prune'])]),
    'E3': ('contribution/results/output_update_verification.json', [
        ('contribution/network_reduction/output_updates/OutputUpdates.lean', ['run_factors','bad_no_reduced_step','view_algebra_stable'])]),
    'E4': ('contribution/results/linear_observations_verification.json', [
        ('contribution/network_reduction/linear_observations/MomentumQuotient.lean', ['run_factors','network_sequence','algebra_stable'])]),
    'E5': ('contribution/results/rmsprop_and_property_transfer_verification.json', [
        ('contribution/network_reduction/linear_observations/AdaptiveBoundary.lean', ['no_reduced_step']),
        ('contribution/network_reduction/rmsprop_symmetric/SymmetricRMSProp.lean', ['initialized_run_factors','algebra_stable','left_unreachable_from_initialization'])]),
    'E6': ('contribution/results/property_decision_verification.json', [
        ('contribution/network_reduction/property_decision/Witnesses.lean', ['baseline_above_refuted','baseline_below_refuted','adversarial_above_refuted','adversarial_below_refuted','baseline_above_reduced_refuted','baseline_below_reduced_refuted','adversarial_above_reduced_refuted','adversarial_below_reduced_refuted'])]),
    'E7': ('contribution/model_repair/directed_repair/RESULT.json', [
        ('contribution/model_repair/directed_repair/ProjectionRepair.lean', ['project_in_interval','project_above','project_below','project_idempotent','reluBlock_eq_project']),
        ('contribution/model_repair/directed_repair/RepairNetwork.lean', ['repaired_above','repaired_below'])]),
    'E8': ('contribution/model_repair/directed_repair/RESULT.json', [
        ('contribution/model_repair/directed_repair/RepairedCore.lean', ['core_equal']),
        ('contribution/model_repair/directed_repair/RepairReference.lean', ['repaired_mse_bound']),
        ('contribution/model_repair/directed_repair/RepairResult.lean', ['reference_quality','repaired_controller_contract'])]),
    'E9': ('contribution/results/positive_property_verification.json', []),
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def build():
    for path in [REPORT,PDF]:
        assert sha(path)==EXPECTED_SOURCE_HASHES[path.name], 'Source edition changed; review the extraction anchors before rebuilding.'
    lines = REPORT.read_text().splitlines()
    pages, sections, page, section = [], [], 1, 'Opening narrative'
    for line in lines:
        if line.startswith('## '): section = line[3:]
        elif line.startswith('### '): section = line[4:]
        pages.append(page); sections.append(section)
        if '<!-- pagebreak -->' in line: page += 1
    nodes = []
    for row in RECORDS.strip().splitlines():
        ident, kind, case, status, span, title, content = row.split('|', 6)
        lo, hi = map(int, span.split('-'))
        assert 1 <= lo <= hi <= len(lines)
        nodes.append(dict(id=ident, kind=kind, case=case, status=status,
            title=title, content=content, extraction_origin='document_grounded',
            source=dict(document='report', line_start=lo,line_end=hi,
                pdf_pages=sorted(set(pages[lo-1:hi])),section=sections[lo-1],
                passage='\n'.join(lines[lo-1:hi])),
            novelty='not_assessed_against_literature'))
    byid = {n['id']:n for n in nodes}
    for ident in ['G0','Q0','U18']:
        byid[ident]['extraction_origin']='analytical_reconstruction_from_document'
    for ident in ['Q2a','Q2b','Q2c','Q3a','Q3b','Q6','Q7','Q8a','Q8b','Q8c','Q10','Q11']:
        byid[ident]['extraction_origin']='question_reconstructed_from_reported_obligation_or_boundary'
    for ident in ['H1','H2']:
        byid[ident]['extraction_origin']='candidate_claim_reconstructed_from_document_counterexample'
    edges=[]
    for i,row in enumerate(LINKS.strip().splitlines(),1):
        a,rel,b,why=row.split('|',3)
        edges.append(dict(id=f'R{i:03}',source=a,relation=rel,target=b,
            explanation=why, status='interpreted_document_relation'))
    for q,answers in ANSWERS.items():
        byid[q]['answer_nodes']=answers
        byid[q]['lifecycle']={
            'observed_document_status':byid[q]['status'],
            'historical_events':'Not reconstructed as an actual execution log.',
            'reopen_if':'A relevant artifact, domain, assumption or operation changes; recheck applicability before reusing the answer.',
        }
        byid[q]['interest']={
            'assessment':'open_research_obligation' if not answers else 'resolved_or_scoped_result_with_reuse_value',
            'basis':'Analytical classification of this document; no numeric ranking and no claim about researcher preferences.',
        }
        for a in answers:
            edges.append(dict(id=f'R{len(edges)+1:03}',source=a,relation='answers',target=q,
                explanation='Answer only within the source node\'s model, domain and evidence scope.',
                status='interpreted_document_relation'))
    for ident,(receipt,artifacts) in EVIDENCE.items():
        p=ROOT/receipt; data=json.loads(p.read_text()); bindings=data.get('sources_sha256',{})
        entries=[]
        for path,names in artifacts:
            f=ROOT/path; text=f.read_text(); actual=sha(f)
            found={name: bool(re.search(r'\b(?:theorem|lemma)\s+'+re.escape(name)+r'\b',text)) for name in names}
            entries.append(dict(path=path,sha256=actual,recorded_sha256=bindings.get(path),
                source_binding_matches=bindings.get(path)==actual,declarations=found))
        byid[ident]['evidence_record']=dict(receipt=receipt,receipt_sha256=sha(p),
            recorded_status=data.get('status'),artifacts=entries,
            recorded_audit_roots=data.get('audited_roots'),
            freshly_replayed=False,interpretation='Historical verification evidence; source identity checked during extraction.')
    for ident,rel in [('E3','contribution/results/update_synthesis_verification.json'),
                      ('E9','contribution/results/network_reduction_verification.json')]:
        d=json.loads((ROOT/rel).read_text())
        byid[ident]['evidence_record'].setdefault('additional_receipts',[]).append(dict(
            receipt=rel,sha256=sha(ROOT/rel),recorded_status=d.get('status'),
            scope='Coordinate retention' if ident=='E3' else 'Baseline finite runtime comparison',
            freshly_replayed=False))
    byid['E4']['evidence_record']['relevant_recorded_roots']=[
        'Contribution.Reduction.LinearObservations.rows_minimal',
        'Contribution.Reduction.LinearObservations.dimension_lower_bound',
        'Contribution.Reduction.LinearGenerated.Coupled.retained_dimension']
    for q,reason in {
        'Q1':'Provides a positive all-input-pair baseline whose property can be transported.',
        'Q2':'Determines which computation can be removed while retaining the same output contract.',
        'Q3':'Determines whether discarded parameters can affect later permitted operations.',
        'Q4':'Tests a smaller executable optimizer state and the exact price of aggregating coordinates.',
        'Q5':'A negative answer identifies the boundary of a plausible reduction and motivates checking a reachable invariant subset.',
        'Q6':'Tests whether a justified initial-state and transition invariant recovers a useful reduction.',
        'Q7':'Separates faithful preservation of existing behavior from satisfying the desired directional clauses.',
        'Q8':'Connects a universal directional guarantee with explicitly scoped nonconstant reference quality.',
        'Q9':'Open integration obligation: the changed core is outside the earlier fixed-hidden-layer update theorem.',
        'Q10':'Open numerical obligation: real proofs and finite float32 observations have different scopes.',
        'Q11':'Open application obligation: usefulness for physical flight is not entailed by the network-only guarantees.',
    }.items():byid[q]['interest']['reason']=reason
    # Other references explicitly used by individual insight nodes.
    for ident, ev in {'U3':['E1','E2'],'U6':['E3'],'U11':['E3'],
                     'I3':['E5'],'X1':['E3'],'X2':['E5'],'X3':['E6']}.items():
        byid[ident]['supporting_evidence']=ev
    derivations=[dict(id=i,kind='joint_inference',premises=p,conclusions=c,evidence=e,
        case=case,premise_mode='all',rule=rule,
        status='extracted_derivation_not_new_kernel_proof') for i,p,c,e,case,rule in DERIVATIONS]
    byid['X1']['contra_invariant_role']={
        'target':'Candidate factorization of badStep through C3',
        'violated_condition':'Equal retained states must have equal retained successors.',
        'preserved_result':'The inactive-neuron pruning certificate remains valid.',
        'terminology':'Working graph role, not a theorem named contra-invariant in the source.'}
    byid['X2']['contra_invariant_role']={
        'target':'Candidate all-valid-state factorization through C7',
        'violated_condition':'Same old view must determine a unique next view.',
        'preserved_result':'The restricted equal-history theorem is compatible with this obstruction.',
        'terminology':'Working graph role; it is not a failure of invariant I3 on its reachable states.'}
    byid['X3']['contra_invariant_role']={
        'target':'Candidate universal Above(2) property of the original Baseline',
        'violated_condition':'An in-domain input satisfying the premise must meet the output bound.',
        'preserved_result':'Exact equality can faithfully preserve this violation.',
        'terminology':'Counterexample to a proposed answer, not an invalidation of the question.'}
    byid['Q0']['resolution_rule']='The children establish several scoped results. They do not jointly prove physical flight safety or a single all-model adaptation theorem.'
    byid['Q2']['resolution_rule']='Require Q2a and Q2b for the accepted deletion and Q2c for the same checkpoint, domain and property.'
    byid['Q3']['resolution_rule']='Current-output sufficiency and future-step compatibility are separate obligations; the universal unrestricted-update answer is not positive.'
    byid['Q8']['resolution_rule']='Combine the frozen small-core directional theorem and its exact reference-quality theorem. Repaired full/small equality discharges the separate reduction child.'
    frameworks=[]
    for case,title in CASES.items():
        ns=[n for n in nodes if n['case']==case]
        frameworks.append(dict(id=case,title=title,
            question=[n['id'] for n in ns if n['kind']=='question'],
            assumptions=[n['id'] for n in ns if n['kind']=='assumption'],
            insights=[n['id'] for n in ns if n['kind']=='insight'],
            justification=[n['id'] for n in ns if n['kind']=='evidence'],
            invariants=[n['id'] for n in ns if n['kind']=='invariant'],
            counterexamples=[n['id'] for n in ns if n['kind']=='counterexample'],
            limits=[n['id'] for n in ns if n['kind']=='limitation']))
    graph=dict(schema_version=1,title='Research graph extracted from Can a Smaller Network Keep Its Promise?',
        extraction=dict(method='Document-specific structured extraction and explicit analytical links.',
            scope='Main narrative and mathematical appendices of the 26-page guide.',
            general_pdf_extractor=False,new_mathematical_proofs=False,
            source_hierarchy='The PDF and Markdown guide are the input; linked Lean declarations and saved receipts support source identity and reported proof status.'),
        documents=[dict(id='report',path=str(REPORT.relative_to(ROOT)),sha256=sha(REPORT),
            pdf_path=str(PDF.relative_to(ROOT)),pdf_sha256=sha(PDF),page_count=page)],
        nodes=nodes,edges=edges,joint_inferences=derivations,four_principles=frameworks,
        process_invariants=[
            'Every extracted node has a document location and an explicit scope/status.',
            'Analytical links and reconstructed questions are distinguished from quoted document claims.',
            'Joint premises remain joint; projections for display do not delete the underlying inference record.',
            'A failed all-state claim and a successful invariant-restricted claim remain different questions.',
            'Recorded proofs, finite observations and open obligations keep distinct statuses.',
            'Reduced graph displays retain IDs that resolve to the complete provenance and dependency record.'],
        limitations=[
            'This is an inspectable extraction of one document, not a trained or evaluated general mini-AI.',
            'The graph does not reconstruct the historical brainstorming order, abandoned attempts or exact discovery chronology.',
            'Structural validation and matching source hashes do not prove semantic completeness of extraction.',
            'Interestingness is a qualitative interpretation, not a learned or validated ranking.',
            'No new Lean or second-kernel proof run is performed.'])
    return graph

def validate(g):
    ids=[n['id'] for n in g['nodes']]; assert len(ids)==len(set(ids)),'Duplicate node ID'
    byid={n['id']:n for n in g['nodes']}
    for n in g['nodes']:
        assert n['source']['passage'].strip(),f'No passage: {n["id"]}'
        for ev in n.get('supporting_evidence',[]):assert byid[ev]['kind']=='evidence'
        if n['kind']=='question':
            assert all(x in byid for x in n['answer_nodes'])
            assert not(n['status'].startswith('answered') and not n['answer_nodes']), 'Answered question without answer'
        for a in n.get('evidence_record',{}).get('artifacts',[]):
            assert all(a['declarations'].values()), f'Missing declaration: {a["path"]}'
            assert a['source_binding_matches'], f'Source differs from recorded proof input: {a["path"]}'
        er=n.get('evidence_record',{})
        if er.get('relevant_recorded_roots'):
            receipt=json.loads((ROOT/er['receipt']).read_text())
            assert all(x in receipt['axiom_audit'] for x in er['relevant_recorded_roots'])
    for e in g['edges']:
        assert e['source'] in byid and e['target'] in byid,'Dangling edge'
        if e['relation']=='has_subquestion':
            assert byid[e['source']]['kind']==byid[e['target']]['kind']=='question'
    for j in g['joint_inferences']:
        assert j['premise_mode']=='all','Joint premises must remain joint'
        assert j['premises'] and j['conclusions'] and j['evidence']
        assert all(x in byid for x in j['premises']+j['conclusions']+j['evidence'])
        assert all(byid[x]['kind']=='evidence' for x in j['evidence'])
    assert byid['Q5']['status']=='answered_no' and byid['Q6']['status']=='answered_yes'
    assert byid['Q10']['status']=='open' and byid['Q11']['status']=='open'
    return dict(status='PASS',nodes=len(ids),relations=len(g['edges']),
        joint_inferences=len(g['joint_inferences']),document_pages=g['documents'][0]['page_count'],
        matched_lean_artifacts=sum(len(n.get('evidence_record',{}).get('artifacts',[])) for n in g['nodes']),
        checks=['Unique IDs','Source passages','Question answer references','Joint-premise integrity',
                'Linked theorem declarations','Lean source hashes against saved receipts',
                'Separate negative/restricted-positive question statuses'],
        scope='Structural and evidence-binding checks, not a semantic proof of the extracted graph.')

ASCII = r'''RESEARCH GRAPH: Can a Smaller Network Keep Its Promise?
Source: 26-page guide. Braces {a,b} mean JOINT premises, not alternatives.
IDs resolve to exact passages, assumptions, evidence and scope in GRAPH.json.

G0: useful controller guarantees
 |
 +-- Q1: robustness on DL2/Godel? --{A0,A1,A2,C1; E1}--> U1: YES
 |                                                       |
 +-- Q2: certified deletion?                              |
 |    +-- Q2a: inactive neuron? --> U3                    |
 |    +-- Q2b: output equality? --{U3,C2; E2}--> I1        |
 |    +-- Q2c: promise inherited? <--{U1,I1,A2; E1,E2}---+
 |                                          |
 |                                          +--> U4: smaller models keep P=>Q
 |
 +-- Q3: can irrelevant weights be forgotten during updates? [Adversarial]
 |    +-- Q3a: evaluate from q? --> C3:q --> C4:RR, C5:Obs(q) --> U7:YES
 |    +-- Q3b: update from q? --{A4; E3}--> U8:compatible finite sequences
 |         |                                  +--> I2:RR preserved
 |         |                                  +--> U9:stable observables
 |         +-- X1: read forgotten a1 --> U10:no reduced badStep
 |                                             +--> U11:enlarge the view
 |
 +-- Q4: retain less optimizer memory? [specified momentum]
 |    +-- U12: memory affects next step
 |    +-- {A5,C6; E4} --> U13:8 observations suffice, scoped minimum
 |                    +--> U14:aggregate update needs factor two
 |
 +-- Q5: same sum view for ALL valid RMSProp histories?
 |    +-- {A6,C7,X2; E5} --> U15:NO, equal views have different successors
 |                                      |
 |                               motivates a restricted question
 |                                      v
 |    Q6: on equal-history states? --{A6,I3,C8; E5}--> U16:YES
 |                                     |
 |                            I3: initialized and preserved
 |    Q5 remains answered NO. Q6 has a different, justified domain.
 |
 +-- Q7: directional clauses on Baseline/Adversarial?
 |    +-- {A7,X3; E6} --> U17:refutations survive exact reduction
 |                           |
 |                           v   (insight-to-insight)
 |                       U18:fixing that violation requires changed output
 |                           |
 |                           v
 +-- Q8: useful directional repair? [NEW fitted Adversarial core + block]
      +-- Q8a: any core proposal?
      |    C9:allowed set --> C10:interval --> C11:projection
      |       {A8,A9,C9,C10,C11; E7} --> U19:operator laws
      |       {U19,C12,A8,A9; E7} --> U20:any-core contract --> I4
      |                                  |
      |                                  +--> X4:constant also satisfies it
      +-- Q8b: useful reference fit?                  |
      |    C13:fit/freeze <-- A10:360 rows, A11:candidate
      |       {C13,C14,A10,A11; E8} --> U21:finite quality gate passes
      +-- Q8c: reduce the FITTED core?
           {C15,C12,A8,A11; E8} --> U22:full/small repaired equality

      {U20,U21,A8,A10,A11; E8} --> U23:combined scoped contract
                                       |
                                       +--> Q9:additional adaptation property?
                                              OPEN; L4:old view bridge absent

EXECUTION / DEPLOYMENT BOUNDARIES
 U24:finite float32 observations --> Q10:universal numerical guarantee? OPEN
 L6:reference data and network proofs --> Q11:physical flight behavior? OPEN

E1-E9: evidence nodes. I1-I4: object-level preservation / invariant nodes.
X1-X3: explicit counterexample roles; X4: trivial-solution witness.
L1-L7: boundaries that remain attached to the relevant results.
This display is a projection of the full graph; it is not a deletion of evidence.
'''

def text_inventory(g):
    out=[ASCII,'\nCOMPLETE NODE INVENTORY\n']
    for n in g['nodes']:
        s=n['source']; out += [f'{n["id"]} [{n["kind"]}; {n["status"]}] {n["title"]}',
            '  '+n['content'],f'  PDF page(s) {s["pdf_pages"]}; REPORT.md:{s["line_start"]}-{s["line_end"]}']
    out += ['\nALL JOINT INFERENCES\n']
    for j in g['joint_inferences']:
        out += [f'{j["id"]}: {{{", ".join(j["premises"])}}} + evidence {{{", ".join(j["evidence"])}}} -> {", ".join(j["conclusions"])}', '  '+j['rule']]
    out += ['\nALL TYPED RELATIONS\n']
    out += [f'{e["id"]}: {e["source"]} --{e["relation"]}--> {e["target"]}: {e["explanation"]}' for e in g['edges']]
    return '\n'.join(out)+'\n'

def main():
    g=build(); result=validate(g)
    # These are corruption controls on the export contract, not math tests.
    controls=[]
    for name,mutate in [
        ('dangling relation',lambda x:x['edges'][0].update(target='ABSENT')),
        ('joint premises changed to alternatives',lambda x:x['joint_inferences'][0].update(premise_mode='any')),
        ('positive answer without an answer artifact',lambda x:next(n for n in x['nodes'] if n['id']=='Q1').update(answer_nodes=[])),
    ]:
        bad=copy.deepcopy(g); mutate(bad)
        try:validate(bad)
        except (AssertionError,KeyError):controls.append(dict(control=name,result='REJECTED'))
        else:raise AssertionError('Bad graph accepted: '+name)
    result['negative_controls']=controls
    (HERE/'GRAPH.json').write_text(json.dumps(g,ensure_ascii=False,indent=2)+'\n')
    (HERE/'GRAPH.txt').write_text(text_inventory(g))
    (HERE/'VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
    template=(HERE/'viewer_template.html').read_text()
    payload=json.dumps(g,ensure_ascii=False).replace('<', r'\u003c')
    preview=build_pdf_preview(PDF,g,HERE)
    preview_payload=json.dumps(preview,ensure_ascii=False).replace('<', r'\u003c')
    viewer=(HERE/'viewer.js').read_text()
    (HERE/'GRAPH.html').write_text(template.replace('/*GRAPH_DATA*/',payload).replace('/*PDF_DATA*/',preview_payload).replace('/*VIEWER_CODE*/',viewer))
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
