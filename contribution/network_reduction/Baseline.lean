import Pruning
import Float32

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace Contribution.Reduction.Baseline
open Contribution.Universal Contribution.Reduction
def original : Network := ⟨
  [⟨[(mkRat (14733301) 33554432), (mkRat (-5417951) 4194304), (mkRat (2121463) 4194304), (mkRat (9802591) 2097152), (mkRat (4357281) 4194304), (mkRat (-7256115) 4194304)], (mkRat (9888299) 16777216)⟩, ⟨[(mkRat (9316565) 8388608), (mkRat (-5597229) 4194304), (mkRat (-5584769) 2097152), (mkRat (-9358439) 2097152), (mkRat (-12897041) 33554432), (mkRat (10886459) 4194304)], (mkRat (4607961) 4194304)⟩, ⟨[(mkRat (9280929) 33554432), (mkRat (-2704801) 2097152), (mkRat (-323387) 131072), (mkRat (-5242521) 2097152), (mkRat (-14525825) 33554432), (mkRat (13386907) 4194304)], (mkRat (7115377) 33554432)⟩, ⟨[(mkRat (-7648579) 8388608), (mkRat (-226945) 262144), (mkRat (10935373) 67108864), (mkRat (1549345) 134217728), (mkRat (9031439) 67108864), (mkRat (296829) 1048576)], (mkRat (-9432419) 67108864)⟩, ⟨[(mkRat (-7880759) 8388608), (mkRat (11699083) 33554432), (mkRat (-8486229) 33554432), (mkRat (16385491) 268435456), (mkRat (-3501047) 4194304), (mkRat (-2050715) 4194304)], (mkRat (-7899969) 33554432)⟩, ⟨[(mkRat (-11214845) 67108864), (mkRat (-6048531) 8388608), (mkRat (-13669937) 16777216), (mkRat (-4014109) 16777216), (mkRat (-12774529) 67108864), (mkRat (-5879319) 67108864)], (mkRat (-2750849) 8388608)⟩],
  [⟨[(mkRat (-5654813) 16777216), (mkRat (-684545) 1048576), (mkRat (-4825093) 8388608), (mkRat (-583721) 16777216), (mkRat (959357) 16777216), (mkRat (-1509771) 2097152)], (mkRat (0) 1)⟩, ⟨[(mkRat (11086709) 8388608), (mkRat (-1308815) 524288), (mkRat (-8605583) 4194304), (mkRat (-6587325) 16777216), (mkRat (-538171) 1048576), (mkRat (-9732107) 33554432)], (mkRat (-6883909) 4194304)⟩, ⟨[(mkRat (9747125) 8388608), (mkRat (9346111) 4194304), (mkRat (-10270991) 8388608), (mkRat (4756749) 16777216), (mkRat (-15333977) 67108864), (mkRat (2840417) 8388608)], (mkRat (-11396301) 536870912)⟩, ⟨[(mkRat (-6235251) 8388608), (mkRat (-2123439) 4194304), (mkRat (-14011729) 33554432), (mkRat (1748333) 4194304), (mkRat (-3899419) 8388608), (mkRat (97141) 1048576)], (mkRat (0) 1)⟩],
  [⟨[(mkRat (-7997113) 16777216), (mkRat (-3918413) 8388608), (mkRat (8577401) 16777216), (mkRat (-1102247) 1048576)], (mkRat (8308971) 134217728)⟩]
⟩
def reduced : Network := ⟨
  [⟨[(mkRat (14733301) 33554432), (mkRat (-5417951) 4194304), (mkRat (2121463) 4194304), (mkRat (9802591) 2097152), (mkRat (4357281) 4194304), (mkRat (-7256115) 4194304)], (mkRat (9888299) 16777216)⟩, ⟨[(mkRat (9316565) 8388608), (mkRat (-5597229) 4194304), (mkRat (-5584769) 2097152), (mkRat (-9358439) 2097152), (mkRat (-12897041) 33554432), (mkRat (10886459) 4194304)], (mkRat (4607961) 4194304)⟩, ⟨[(mkRat (9280929) 33554432), (mkRat (-2704801) 2097152), (mkRat (-323387) 131072), (mkRat (-5242521) 2097152), (mkRat (-14525825) 33554432), (mkRat (13386907) 4194304)], (mkRat (7115377) 33554432)⟩, ⟨[(mkRat (-7648579) 8388608), (mkRat (-226945) 262144), (mkRat (10935373) 67108864), (mkRat (1549345) 134217728), (mkRat (9031439) 67108864), (mkRat (296829) 1048576)], (mkRat (-9432419) 67108864)⟩, ⟨[(mkRat (-7880759) 8388608), (mkRat (11699083) 33554432), (mkRat (-8486229) 33554432), (mkRat (16385491) 268435456), (mkRat (-3501047) 4194304), (mkRat (-2050715) 4194304)], (mkRat (-7899969) 33554432)⟩],
  [⟨[(mkRat (-5654813) 16777216), (mkRat (-684545) 1048576), (mkRat (-4825093) 8388608), (mkRat (-583721) 16777216), (mkRat (959357) 16777216)], (mkRat (0) 1)⟩, ⟨[(mkRat (11086709) 8388608), (mkRat (-1308815) 524288), (mkRat (-8605583) 4194304), (mkRat (-6587325) 16777216), (mkRat (-538171) 1048576)], (mkRat (-6883909) 4194304)⟩, ⟨[(mkRat (9747125) 8388608), (mkRat (9346111) 4194304), (mkRat (-10270991) 8388608), (mkRat (4756749) 16777216), (mkRat (-15333977) 67108864)], (mkRat (-11396301) 536870912)⟩, ⟨[(mkRat (-6235251) 8388608), (mkRat (-2123439) 4194304), (mkRat (-14011729) 33554432), (mkRat (1748333) 4194304), (mkRat (-3899419) 8388608)], (mkRat (0) 1)⟩],
  [⟨[(mkRat (-7997113) 16777216), (mkRat (-3918413) 8388608), (mkRat (8577401) 16777216), (mkRat (-1102247) 1048576)], (mkRat (8308971) 134217728)⟩]
⟩
def domain : List Interval := List.replicate 6 ⟨0, 1⟩
def certificate : Certificate := {
  firstBounds := [⟨(mkRat (-40807965) 16777216), (mkRat (243181307) 33554432)⟩, ⟨(mkRat (-259902513) 33554432), (mkRat (40305405) 8388608)⟩, ⟨(mkRat (-13584667) 2097152), (mkRat (61745781) 16777216)⟩, ⟨(mkRat (-128718971) 67108864), (mkRat (60612243) 134217728)⟩, ⟨(mkRat (-46161665) 16777216), (mkRat (46778403) 268435456)⟩, ⟨(mkRat (-170999917) 67108864), (mkRat (-2750849) 8388608)⟩]
  secondBounds := [⟨(mkRat (-17366087121966295) 2251799813685248), (mkRat (44877188366871) 4503599627370496)⟩, ⟨(mkRat (-48309098617671023) 2251799813685248), (mkRat (2234109072079287) 281474976710656)⟩, ⟨(mkRat (-82276061562843051) 18014398509481984), (mkRat (43311788949264623) 2251799813685248)⟩, ⟨(mkRat (-21250949504552589) 2251799813685248), (mkRat (105970384640919) 562949953421312)⟩]
  firstKeep := [true, true, true, true, true, false]
  secondKeep := [true, true, true, true] }
def flat (n : Network) : List ℚ :=
  [n.first, n.second, n.third].flatMap
    (fun ns => ns.flatMap Neuron.weights ++ ns.map Neuron.bias)
def originalBits : List Nat := [1054920693, 3215284158, 1057061852, 1083544415, 1065679170, 3218960486, 1066281173, 3215642714, 3224006402, 3230583911, 3200568081, 1076239675, 1049468321, 3215267460, 3223185248, 3223321906, 3202196865, 1078740123, 3211356806, 3210584128, 1042734157, 1010639112, 1040830223, 1049685920, 3211821166, 1051886475, 3196157269, 1031407059, 3210063836, 3204076760, 3190497277, 3208156710, 3209729585, 3195338868, 3192056961, 3182652462, 1058464299, 1066180530, 1046029538, 3188714851, 3195082370, 3198674436, 3198980666, 3207012368, 3205709834, 3171844752, 1030371280, 3208137816, 1068051317, 3223307384, 3221442447, 3200845690, 3204670384, 3197403147, 1066711733, 1074699327, 3214719247, 1049700890, 3194616409, 1051549060, 3208530150, 3204553404, 3201682769, 1054174056, 3203268716, 1035844224, 0, 3218216074, 3165512909, 0, 3203665266, 3203344692, 1057153401, 3213266232, 1031639510]
def originalRationals : List ℚ := [(mkRat (14733301) 33554432), (mkRat (-5417951) 4194304), (mkRat (2121463) 4194304), (mkRat (9802591) 2097152), (mkRat (4357281) 4194304), (mkRat (-7256115) 4194304), (mkRat (9316565) 8388608), (mkRat (-5597229) 4194304), (mkRat (-5584769) 2097152), (mkRat (-9358439) 2097152), (mkRat (-12897041) 33554432), (mkRat (10886459) 4194304), (mkRat (9280929) 33554432), (mkRat (-2704801) 2097152), (mkRat (-323387) 131072), (mkRat (-5242521) 2097152), (mkRat (-14525825) 33554432), (mkRat (13386907) 4194304), (mkRat (-7648579) 8388608), (mkRat (-226945) 262144), (mkRat (10935373) 67108864), (mkRat (1549345) 134217728), (mkRat (9031439) 67108864), (mkRat (296829) 1048576), (mkRat (-7880759) 8388608), (mkRat (11699083) 33554432), (mkRat (-8486229) 33554432), (mkRat (16385491) 268435456), (mkRat (-3501047) 4194304), (mkRat (-2050715) 4194304), (mkRat (-11214845) 67108864), (mkRat (-6048531) 8388608), (mkRat (-13669937) 16777216), (mkRat (-4014109) 16777216), (mkRat (-12774529) 67108864), (mkRat (-5879319) 67108864), (mkRat (9888299) 16777216), (mkRat (4607961) 4194304), (mkRat (7115377) 33554432), (mkRat (-9432419) 67108864), (mkRat (-7899969) 33554432), (mkRat (-2750849) 8388608), (mkRat (-5654813) 16777216), (mkRat (-684545) 1048576), (mkRat (-4825093) 8388608), (mkRat (-583721) 16777216), (mkRat (959357) 16777216), (mkRat (-1509771) 2097152), (mkRat (11086709) 8388608), (mkRat (-1308815) 524288), (mkRat (-8605583) 4194304), (mkRat (-6587325) 16777216), (mkRat (-538171) 1048576), (mkRat (-9732107) 33554432), (mkRat (9747125) 8388608), (mkRat (9346111) 4194304), (mkRat (-10270991) 8388608), (mkRat (4756749) 16777216), (mkRat (-15333977) 67108864), (mkRat (2840417) 8388608), (mkRat (-6235251) 8388608), (mkRat (-2123439) 4194304), (mkRat (-14011729) 33554432), (mkRat (1748333) 4194304), (mkRat (-3899419) 8388608), (mkRat (97141) 1048576), (mkRat (0) 1), (mkRat (-6883909) 4194304), (mkRat (-11396301) 536870912), (mkRat (0) 1), (mkRat (-7997113) 16777216), (mkRat (-3918413) 8388608), (mkRat (8577401) 16777216), (mkRat (-1102247) 1048576), (mkRat (8308971) 134217728)]
theorem original_decoded : originalBits.map Contribution.Float32.decode =
    originalRationals.map some := by decide +kernel
theorem original_parameters : flat original = originalRationals := by rfl
theorem original_shape :
    (original.first.map (fun n => n.weights.length),
     original.second.map (fun n => n.weights.length),
     original.third.map (fun n => n.weights.length)) =
    (List.replicate 6 6, List.replicate 4 6, List.replicate 1 4) := by rfl
def reducedBits : List Nat := [1054920693, 3215284158, 1057061852, 1083544415, 1065679170, 3218960486, 1066281173, 3215642714, 3224006402, 3230583911, 3200568081, 1076239675, 1049468321, 3215267460, 3223185248, 3223321906, 3202196865, 1078740123, 3211356806, 3210584128, 1042734157, 1010639112, 1040830223, 1049685920, 3211821166, 1051886475, 3196157269, 1031407059, 3210063836, 3204076760, 1058464299, 1066180530, 1046029538, 3188714851, 3195082370, 3198980666, 3207012368, 3205709834, 3171844752, 1030371280, 1068051317, 3223307384, 3221442447, 3200845690, 3204670384, 1066711733, 1074699327, 3214719247, 1049700890, 3194616409, 3208530150, 3204553404, 3201682769, 1054174056, 3203268716, 0, 3218216074, 3165512909, 0, 3203665266, 3203344692, 1057153401, 3213266232, 1031639510]
def reducedRationals : List ℚ := [(mkRat (14733301) 33554432), (mkRat (-5417951) 4194304), (mkRat (2121463) 4194304), (mkRat (9802591) 2097152), (mkRat (4357281) 4194304), (mkRat (-7256115) 4194304), (mkRat (9316565) 8388608), (mkRat (-5597229) 4194304), (mkRat (-5584769) 2097152), (mkRat (-9358439) 2097152), (mkRat (-12897041) 33554432), (mkRat (10886459) 4194304), (mkRat (9280929) 33554432), (mkRat (-2704801) 2097152), (mkRat (-323387) 131072), (mkRat (-5242521) 2097152), (mkRat (-14525825) 33554432), (mkRat (13386907) 4194304), (mkRat (-7648579) 8388608), (mkRat (-226945) 262144), (mkRat (10935373) 67108864), (mkRat (1549345) 134217728), (mkRat (9031439) 67108864), (mkRat (296829) 1048576), (mkRat (-7880759) 8388608), (mkRat (11699083) 33554432), (mkRat (-8486229) 33554432), (mkRat (16385491) 268435456), (mkRat (-3501047) 4194304), (mkRat (-2050715) 4194304), (mkRat (9888299) 16777216), (mkRat (4607961) 4194304), (mkRat (7115377) 33554432), (mkRat (-9432419) 67108864), (mkRat (-7899969) 33554432), (mkRat (-5654813) 16777216), (mkRat (-684545) 1048576), (mkRat (-4825093) 8388608), (mkRat (-583721) 16777216), (mkRat (959357) 16777216), (mkRat (11086709) 8388608), (mkRat (-1308815) 524288), (mkRat (-8605583) 4194304), (mkRat (-6587325) 16777216), (mkRat (-538171) 1048576), (mkRat (9747125) 8388608), (mkRat (9346111) 4194304), (mkRat (-10270991) 8388608), (mkRat (4756749) 16777216), (mkRat (-15333977) 67108864), (mkRat (-6235251) 8388608), (mkRat (-2123439) 4194304), (mkRat (-14011729) 33554432), (mkRat (1748333) 4194304), (mkRat (-3899419) 8388608), (mkRat (0) 1), (mkRat (-6883909) 4194304), (mkRat (-11396301) 536870912), (mkRat (0) 1), (mkRat (-7997113) 16777216), (mkRat (-3918413) 8388608), (mkRat (8577401) 16777216), (mkRat (-1102247) 1048576), (mkRat (8308971) 134217728)]
theorem reduced_decoded : reducedBits.map Contribution.Float32.decode =
    reducedRationals.map some := by decide +kernel
theorem reduced_parameters : flat reduced = reducedRationals := by rfl
theorem reduced_shape :
    (reduced.first.map (fun n => n.weights.length),
     reduced.second.map (fun n => n.weights.length),
     reduced.third.map (fun n => n.weights.length)) =
    (List.replicate 5 6, List.replicate 4 5, List.replicate 1 4) := by rfl
theorem checked : Check original domain certificate := by decide +kernel
theorem export_matches_prune : reduced =
    prune original certificate.firstKeep certificate.secondKeep := by decide +kernel
theorem all_real_inputs (xs : List ℝ) (hx : InBox domain xs) :
    eval reduced xs = eval original xs := by
  rw [export_matches_prune]
  exact certified_prune original domain certificate checked xs hx
theorem equivalent_on_cube : EquivalentOn domain reduced original := all_real_inputs
theorem output_predicate (P : List ℝ → Prop) (xs : List ℝ) (hx : InBox domain xs) :
    P (eval reduced xs) ↔ P (eval original xs) := by rw [all_real_inputs xs hx]
theorem domain_nonempty : InBox domain [0,0,0,0,0,0] := by
  norm_num [domain, InBox, Interval.Mem, List.replicate_succ, List.forall₂_cons]
theorem reject_active_neuron : ¬ Check original domain
    { certificate with firstKeep := [false,true,true,true,true,false] } := by decide +kernel
theorem reject_bad_bound : ¬ Check original domain
    { certificate with firstBounds := List.replicate 6 ⟨0,0⟩ } := by decide +kernel
theorem reject_short_mask : ¬ Check original domain
    { certificate with firstKeep := [] } := by decide +kernel
end Contribution.Reduction.Baseline
