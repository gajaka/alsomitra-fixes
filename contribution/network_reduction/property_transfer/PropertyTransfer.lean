import Baseline
import MomentumQuotient

/-! Specifications on the certified cube transfer between the actual trained
controllers and their reductions. No satisfaction premise is manufactured.
The two concrete predicates follow the pinned companion Vehicle file,
not the different anchor-relative framework Property2. -/
set_option autoImplicit false
namespace Contribution.Reduction.PropertyTransfer
open Contribution.Universal

abbrev Input := OutputUpdates.Input

structure Specification where
  pre : Input → Prop
  post : Input → ℝ → Prop

def Satisfies (spec : Specification) (f : Input → ℝ) : Prop :=
  ∀ x, spec.pre x → spec.post x (f x)

def ViolatesAt (spec : Specification) (f : Input → ℝ) (x : Input) : Prop :=
  spec.pre x ∧ ¬ spec.post x (f x)

theorem satisfies_transfer (spec : Specification) (f g : Input → ℝ)
    (h : ∀ x, f x = g x) : Satisfies spec f ↔ Satisfies spec g := by
  simp only [Satisfies, h]

theorem violation_transfer (spec : Specification) (f g : Input → ℝ)
    (h : ∀ x, f x = g x) (x : Input) : ViolatesAt spec f x ↔ ViolatesAt spec g x := by
  simp only [ViolatesAt, h]

def output (n : Network) (x : Input) : ℝ := (eval n x.val).headD 0

theorem baseline_outputs (x : Input) : output Baseline.reduced x = output Baseline.original x :=
  congrArg (fun ys : List ℝ => ys.headD 0) (Baseline.all_real_inputs x.val x.property)

theorem adversarial_outputs (x : Input) :
    output Adversarial.reduced x = output Adversarial.original x :=
  congrArg (fun ys : List ℝ => ys.headD 0) (Adversarial.all_real_inputs x.val x.property)

theorem baseline_specification (spec : Specification) :
    Satisfies spec (output Baseline.reduced) ↔ Satisfies spec (output Baseline.original) :=
  satisfies_transfer spec _ _ baseline_outputs

theorem adversarial_specification (spec : Specification) :
    Satisfies spec (output Adversarial.reduced) ↔ Satisfies spec (output Adversarial.original) :=
  satisfies_transfer spec _ _ adversarial_outputs

theorem baseline_counterexample (spec : Specification) (x : Input) :
    ViolatesAt spec (output Baseline.reduced) x ↔ ViolatesAt spec (output Baseline.original) x :=
  violation_transfer spec _ _ baseline_outputs x

theorem adversarial_counterexample (spec : Specification) (x : Input) :
    ViolatesAt spec (output Adversarial.reduced) x ↔
      ViolatesAt spec (output Adversarial.original) x :=
  violation_transfer spec _ _ adversarial_outputs x

/-- Exact decimal constants and coordinate order from Alsomitra.vcl.
Input membership guarantees six coordinates. Output is the normalized command. -/
noncomputable def physicalX (x : Input) : ℝ :=
  x.val.getD 4 0 * (41232296222734604 / 1000000000000000 : ℝ) +
    (482420778264618 / 1000000000000000 : ℝ)

noncomputable def physicalY (x : Input) : ℝ :=
  x.val.getD 5 0 * (45878638794593570 / 1000000000000000 : ℝ) -
    (41681405266088724 / 1000000000000000 : ℝ)

def farAbove (margin : ℝ) : Specification where
  pre x := physicalY x ≥ -physicalX x + margin
  post _ y := y ≥ 1/2

def farBelow (margin : ℝ) : Specification where
  pre x := physicalY x ≤ -physicalX x - margin
  post _ y := y ≤ 1/2

theorem baseline_above (margin : ℝ) :
    Satisfies (farAbove margin) (output Baseline.reduced) ↔
      Satisfies (farAbove margin) (output Baseline.original) := baseline_specification _

theorem baseline_below (margin : ℝ) :
    Satisfies (farBelow margin) (output Baseline.reduced) ↔
      Satisfies (farBelow margin) (output Baseline.original) := baseline_specification _

theorem adversarial_above (margin : ℝ) :
    Satisfies (farAbove margin) (output Adversarial.reduced) ↔
      Satisfies (farAbove margin) (output Adversarial.original) := adversarial_specification _

theorem adversarial_below (margin : ℝ) :
    Satisfies (farBelow margin) (output Adversarial.reduced) ↔
      Satisfies (farBelow margin) (output Adversarial.original) := adversarial_specification _

def aboveInput : Input := ⟨[0,0,0,0,1,1], by
  norm_num [Adversarial.domain, InBox, Interval.Mem, List.replicate_succ,
    List.forall₂_cons]⟩

theorem above_region_nonempty : ∃ x, (farAbove 2).pre x := by
  refine ⟨aboveInput, ?_⟩
  norm_num [farAbove, physicalX, physicalY, aboveInput]

theorem below_region_nonempty : ∃ x, (farBelow 2).pre x := by
  refine ⟨OutputUpdates.zeroInput, ?_⟩
  norm_num [farBelow, physicalX, physicalY, OutputUpdates.zeroInput]

/-- At each finite prefix, transfer the property of the *current* full network.
This does not assert preservation of a property of its initial head. -/
theorem momentum_sequence_specification (spec : Specification)
    (word : List MomentumQuotient.Config) (s : AffineRetention.Vector 10) :
    Satisfies spec (fun x => MomentumQuotient.output x (MomentumQuotient.run word s)) ↔
      Satisfies spec (fun x => MomentumQuotient.smallOutput x
        (MomentumQuotient.smallRun word (MomentumQuotient.view s))) :=
  satisfies_transfer spec _ _ (fun x => MomentumQuotient.network_sequence x word s)

theorem momentum_sequence_counterexample (spec : Specification)
    (word : List MomentumQuotient.Config) (s : AffineRetention.Vector 10) (x : Input) :
    ViolatesAt spec (fun x => MomentumQuotient.output x (MomentumQuotient.run word s)) x ↔
      ViolatesAt spec (fun x => MomentumQuotient.smallOutput x
        (MomentumQuotient.smallRun word (MomentumQuotient.view s))) x :=
  violation_transfer spec _ _ (fun x => MomentumQuotient.network_sequence x word s) x

end Contribution.Reduction.PropertyTransfer
