import Pruning
import Float32

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace Contribution.Reduction.Adversarial
open Contribution.Universal Contribution.Reduction
def original : Network := ⟨
  [⟨[(mkRat (-5416629) 8589934592), (mkRat (12939497) 2147483648), (mkRat (-9193769) 4194304), (mkRat (12927823) 2097152), (mkRat (15427919) 67108864), (mkRat (852601) 33554432)], (mkRat (2996767) 2097152)⟩, ⟨[(mkRat (15675475) 33554432), (mkRat (4328115) 134217728), (mkRat (-4039437) 1048576), (mkRat (-12392035) 4194304), (mkRat (5600465) 8388608), (mkRat (12643335) 4194304)], (mkRat (3901627) 4194304)⟩, ⟨[(mkRat (4090865) 8388608), (mkRat (5992491) 16777216), (mkRat (-10736957) 2097152), (mkRat (7526319) 4194304), (mkRat (444963) 524288), (mkRat (12394223) 4194304)], (mkRat (2052441) 4194304)⟩, ⟨[(mkRat (-8707469) 8388608), (mkRat (-16649413) 16777216), (mkRat (11265627) 536870912), (mkRat (-10485985) 16777216), (mkRat (134837) 8388608), (mkRat (2184307) 268435456)], (mkRat (-12088307) 33554432)⟩, ⟨[(mkRat (-15355407) 16777216), (mkRat (13663371) 33554432), (mkRat (-6024507) 33554432), (mkRat (10215757) 1073741824), (mkRat (-14343771) 16777216), (mkRat (-15455091) 33554432)], (mkRat (-6959053) 33554432)⟩, ⟨[(mkRat (-11818759) 67108864), (mkRat (-12336265) 16777216), (mkRat (-1708065) 2097152), (mkRat (-8804945) 33554432), (mkRat (-7081575) 33554432), (mkRat (-7308593) 67108864)], (mkRat (-11703883) 33554432)⟩],
  [⟨[(mkRat (-5654813) 16777216), (mkRat (-684545) 1048576), (mkRat (-4825093) 8388608), (mkRat (-583721) 16777216), (mkRat (959357) 16777216), (mkRat (-1509771) 2097152)], (mkRat (0) 1)⟩, ⟨[(mkRat (-41147) 16777216), (mkRat (-8418405) 33554432), (mkRat (-15108991) 16777216), (mkRat (-6587325) 16777216), (mkRat (-538171) 1048576), (mkRat (-9732107) 33554432)], (mkRat (-8393689) 16777216)⟩, ⟨[(mkRat (6463455) 4194304), (mkRat (9318363) 4194304), (mkRat (-4750907) 2097152), (mkRat (11859255) 16777216), (mkRat (-5378937) 67108864), (mkRat (11269563) 33554432)], (mkRat (-1149657) 268435456)⟩, ⟨[(mkRat (-6235251) 8388608), (mkRat (-1816011) 2097152), (mkRat (-13042057) 16777216), (mkRat (7667005) 134217728), (mkRat (-3899419) 8388608), (mkRat (-4489693) 16777216)], (mkRat (-6045025) 16777216)⟩],
  [⟨[(mkRat (-7997113) 16777216), (mkRat (-15367511) 134217728), (mkRat (13762365) 33554432), (mkRat (-11658517) 16777216)], (mkRat (8913047) 134217728)⟩]
⟩
def reduced : Network := ⟨
  [⟨[(mkRat (-5416629) 8589934592), (mkRat (12939497) 2147483648), (mkRat (-9193769) 4194304), (mkRat (12927823) 2097152), (mkRat (15427919) 67108864), (mkRat (852601) 33554432)], (mkRat (2996767) 2097152)⟩, ⟨[(mkRat (15675475) 33554432), (mkRat (4328115) 134217728), (mkRat (-4039437) 1048576), (mkRat (-12392035) 4194304), (mkRat (5600465) 8388608), (mkRat (12643335) 4194304)], (mkRat (3901627) 4194304)⟩, ⟨[(mkRat (4090865) 8388608), (mkRat (5992491) 16777216), (mkRat (-10736957) 2097152), (mkRat (7526319) 4194304), (mkRat (444963) 524288), (mkRat (12394223) 4194304)], (mkRat (2052441) 4194304)⟩, ⟨[(mkRat (-15355407) 16777216), (mkRat (13663371) 33554432), (mkRat (-6024507) 33554432), (mkRat (10215757) 1073741824), (mkRat (-14343771) 16777216), (mkRat (-15455091) 33554432)], (mkRat (-6959053) 33554432)⟩],
  [⟨[(mkRat (-5654813) 16777216), (mkRat (-684545) 1048576), (mkRat (-4825093) 8388608), (mkRat (959357) 16777216)], (mkRat (0) 1)⟩, ⟨[(mkRat (6463455) 4194304), (mkRat (9318363) 4194304), (mkRat (-4750907) 2097152), (mkRat (-5378937) 67108864)], (mkRat (-1149657) 268435456)⟩],
  [⟨[(mkRat (-7997113) 16777216), (mkRat (13762365) 33554432)], (mkRat (8913047) 134217728)⟩]
⟩
def domain : List Interval := List.replicate 6 ⟨0, 1⟩
def certificate : Certificate := {
  firstBounds := [⟨(mkRat (-6559497909) 8589934592), (mkRat (16867979529) 2147483648)⟩, ⟨(mkRat (-6162039) 1048576), (mkRat (686076239) 134217728)⟩, ⟨(mkRat (-19421473) 4194304), (mkRat (116304969) 16777216)⟩, ⟨(mkRat (-101188979) 33554432), (mkRat (-169149103) 536870912)⟩, ⟨(mkRat (-87837007) 33554432), (mkRat (224753933) 1073741824)⟩, ⟨(mkRat (-89155649) 33554432), (mkRat (-11703883) 33554432)⟩]
  secondBounds := [⟨(mkRat (-359278351732546309) 36028797018963968), (mkRat (215619258901081) 18014398509481984)⟩, ⟨(mkRat (-293723404742020683) 36028797018963968), (mkRat (-8393689) 16777216)⟩, ⟨(mkRat (-1133148325046044197) 72057594037927936), (mkRat (211276569589810983) 9007199254740992)⟩, ⟨(mkRat (-290237495953539401) 18014398509481984), (mkRat (-6045025) 16777216)⟩]
  firstKeep := [true, true, true, false, true, false]
  secondKeep := [true, false, true, false] }
def flat (n : Network) : List ℚ :=
  [n.first, n.second, n.third].flatMap
    (fun ns => ns.flatMap Neuron.weights ++ ns.map Neuron.bias)
def originalBits : List Nat := [3123006826, 1002795241, 3222030633, 1086669647, 1047226703, 1020274576, 1055862867, 1023677798, 3228994612, 3225228899, 1059776930, 1077996551, 1056550852, 1052172374, 3231962429, 1072017246, 1062814816, 1077747439, 3213155725, 3212709061, 1017898587, 3206545633, 1015262528, 1006981580, 3211415055, 1053850763, 3191331446, 1008460109, 3210403419, 3203126131, 3191101191, 3208395913, 3209724168, 3196475985, 3193445582, 3185511010, 1068951676, 1064182508, 1056606920, 3199759347, 3193200538, 3199374923, 3198980666, 3207012368, 3205709834, 3171844752, 1030371280, 3208137816, 3139484416, 3196089445, 3211168639, 3200845690, 3204670384, 3197403147, 1069891518, 1074671579, 3222338678, 1060435255, 3181651698, 1051456955, 3208530150, 3210587736, 3209101705, 1030355578, 3203268716, 3196650426, 0, 3204453337, 3146536648, 3199761090, 3203665266, 3186261335, 1053949757, 3207718165, 1032323223]
def originalRationals : List ℚ := [(mkRat (-5416629) 8589934592), (mkRat (12939497) 2147483648), (mkRat (-9193769) 4194304), (mkRat (12927823) 2097152), (mkRat (15427919) 67108864), (mkRat (852601) 33554432), (mkRat (15675475) 33554432), (mkRat (4328115) 134217728), (mkRat (-4039437) 1048576), (mkRat (-12392035) 4194304), (mkRat (5600465) 8388608), (mkRat (12643335) 4194304), (mkRat (4090865) 8388608), (mkRat (5992491) 16777216), (mkRat (-10736957) 2097152), (mkRat (7526319) 4194304), (mkRat (444963) 524288), (mkRat (12394223) 4194304), (mkRat (-8707469) 8388608), (mkRat (-16649413) 16777216), (mkRat (11265627) 536870912), (mkRat (-10485985) 16777216), (mkRat (134837) 8388608), (mkRat (2184307) 268435456), (mkRat (-15355407) 16777216), (mkRat (13663371) 33554432), (mkRat (-6024507) 33554432), (mkRat (10215757) 1073741824), (mkRat (-14343771) 16777216), (mkRat (-15455091) 33554432), (mkRat (-11818759) 67108864), (mkRat (-12336265) 16777216), (mkRat (-1708065) 2097152), (mkRat (-8804945) 33554432), (mkRat (-7081575) 33554432), (mkRat (-7308593) 67108864), (mkRat (2996767) 2097152), (mkRat (3901627) 4194304), (mkRat (2052441) 4194304), (mkRat (-12088307) 33554432), (mkRat (-6959053) 33554432), (mkRat (-11703883) 33554432), (mkRat (-5654813) 16777216), (mkRat (-684545) 1048576), (mkRat (-4825093) 8388608), (mkRat (-583721) 16777216), (mkRat (959357) 16777216), (mkRat (-1509771) 2097152), (mkRat (-41147) 16777216), (mkRat (-8418405) 33554432), (mkRat (-15108991) 16777216), (mkRat (-6587325) 16777216), (mkRat (-538171) 1048576), (mkRat (-9732107) 33554432), (mkRat (6463455) 4194304), (mkRat (9318363) 4194304), (mkRat (-4750907) 2097152), (mkRat (11859255) 16777216), (mkRat (-5378937) 67108864), (mkRat (11269563) 33554432), (mkRat (-6235251) 8388608), (mkRat (-1816011) 2097152), (mkRat (-13042057) 16777216), (mkRat (7667005) 134217728), (mkRat (-3899419) 8388608), (mkRat (-4489693) 16777216), (mkRat (0) 1), (mkRat (-8393689) 16777216), (mkRat (-1149657) 268435456), (mkRat (-6045025) 16777216), (mkRat (-7997113) 16777216), (mkRat (-15367511) 134217728), (mkRat (13762365) 33554432), (mkRat (-11658517) 16777216), (mkRat (8913047) 134217728)]
theorem original_decoded : originalBits.map Contribution.Float32.decode =
    originalRationals.map some := by decide +kernel
theorem original_parameters : flat original = originalRationals := by rfl
theorem original_shape :
    (original.first.map (fun n => n.weights.length),
     original.second.map (fun n => n.weights.length),
     original.third.map (fun n => n.weights.length)) =
    (List.replicate 6 6, List.replicate 4 6, List.replicate 1 4) := by rfl
def reducedBits : List Nat := [3123006826, 1002795241, 3222030633, 1086669647, 1047226703, 1020274576, 1055862867, 1023677798, 3228994612, 3225228899, 1059776930, 1077996551, 1056550852, 1052172374, 3231962429, 1072017246, 1062814816, 1077747439, 3211415055, 1053850763, 3191331446, 1008460109, 3210403419, 3203126131, 1068951676, 1064182508, 1056606920, 3193200538, 3198980666, 3207012368, 3205709834, 1030371280, 1069891518, 1074671579, 3222338678, 3181651698, 0, 3146536648, 3203665266, 1053949757, 1032323223]
def reducedRationals : List ℚ := [(mkRat (-5416629) 8589934592), (mkRat (12939497) 2147483648), (mkRat (-9193769) 4194304), (mkRat (12927823) 2097152), (mkRat (15427919) 67108864), (mkRat (852601) 33554432), (mkRat (15675475) 33554432), (mkRat (4328115) 134217728), (mkRat (-4039437) 1048576), (mkRat (-12392035) 4194304), (mkRat (5600465) 8388608), (mkRat (12643335) 4194304), (mkRat (4090865) 8388608), (mkRat (5992491) 16777216), (mkRat (-10736957) 2097152), (mkRat (7526319) 4194304), (mkRat (444963) 524288), (mkRat (12394223) 4194304), (mkRat (-15355407) 16777216), (mkRat (13663371) 33554432), (mkRat (-6024507) 33554432), (mkRat (10215757) 1073741824), (mkRat (-14343771) 16777216), (mkRat (-15455091) 33554432), (mkRat (2996767) 2097152), (mkRat (3901627) 4194304), (mkRat (2052441) 4194304), (mkRat (-6959053) 33554432), (mkRat (-5654813) 16777216), (mkRat (-684545) 1048576), (mkRat (-4825093) 8388608), (mkRat (959357) 16777216), (mkRat (6463455) 4194304), (mkRat (9318363) 4194304), (mkRat (-4750907) 2097152), (mkRat (-5378937) 67108864), (mkRat (0) 1), (mkRat (-1149657) 268435456), (mkRat (-7997113) 16777216), (mkRat (13762365) 33554432), (mkRat (8913047) 134217728)]
theorem reduced_decoded : reducedBits.map Contribution.Float32.decode =
    reducedRationals.map some := by decide +kernel
theorem reduced_parameters : flat reduced = reducedRationals := by rfl
theorem reduced_shape :
    (reduced.first.map (fun n => n.weights.length),
     reduced.second.map (fun n => n.weights.length),
     reduced.third.map (fun n => n.weights.length)) =
    (List.replicate 4 6, List.replicate 2 4, List.replicate 1 2) := by rfl
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
end Contribution.Reduction.Adversarial
