import FrozenCertificate
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Contribution.Frozen
open Contribution.Universal

theorem reject_wrong_output_bound : ¬ (CheckLeaf network epsilon cap box6 { leaf0 with third := [⟨0,0⟩] }) := by decide +kernel

theorem reject_missing_neurons : ¬ (CheckLeaf network epsilon cap box6 { leaf0 with second := [] }) := by decide +kernel

theorem reject_false_cover : ¬ (Encloses (rootBox.take 5 ++ [⟨0,0⟩]) exactBox) := by decide +kernel

end Contribution.Frozen
