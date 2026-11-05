import Mathlib

/-!
Executable, exact-rational Property2 contract by Dragan Stosic.

The definitions in this file are both executed and proved about. This is a
new reference implementation, not a formal verification of upstream PyTorch.
The coordinate order matches upstream 616df1e: vx, vy, omega, theta, x, y.
The contract is anchor-relative and deliberately retains the code's vy choice.
-/

set_option autoImplicit false

namespace Contribution.Property2

inductive Coord where
  | vx | vy | omega | theta | x | y
  deriving DecidableEq, Repr

instance : Fintype Coord where
  elems := {.vx, .vy, .omega, .theta, .x, .y}
  complete c := by cases c <;> simp

abbrev Vector := Coord → ℚ

@[ext] structure Physical where
  val : Vector

@[ext] structure Normalized where
  val : Vector

def domainLo : Vector
  | .vx => 967568 / 1000000
  | .vy => -607397 / 1000000
  | .omega => -356973 / 1000000
  | .theta => -968479 / 1000000
  | .x => 482421 / 1000000
  | .y => -41681405 / 1000000

def domainHi : Vector
  | .vx => 3489893 / 1000000
  | .vy => -43021 / 1000000
  | .omega => 49180 / 1000000
  | .theta => -68003 / 1000000
  | .x => 41714717 / 1000000
  | .y => 4197234 / 1000000

structure Normalizer where
  offset : Vector
  scale : Vector
  positive : ∀ c, 0 < scale c

def domainNormalizer : Normalizer where
  offset := domainLo
  scale c := domainHi c - domainLo c
  positive c := by cases c <;> norm_num [domainLo, domainHi]

def normalize (n : Normalizer) (p : Physical) : Normalized :=
  ⟨fun c => (p.val c - n.offset c) / n.scale c⟩

def denormalize (n : Normalizer) (z : Normalized) : Physical :=
  ⟨fun c => z.val c * n.scale c + n.offset c⟩

theorem denormalize_normalize (n : Normalizer) (p : Physical) :
    denormalize n (normalize n p) = p := by
  apply Physical.ext
  funext c
  simp [denormalize, normalize, ne_of_gt (n.positive c)]

theorem normalize_denormalize (n : Normalizer) (z : Normalized) :
    normalize n (denormalize n z) = z := by
  apply Normalized.ext
  funext c
  simp [denormalize, normalize, ne_of_gt (n.positive c)]

/-- Named physical thresholds. Negative/infeasible thresholds remain representable
so that compilation can report an empty region rather than sample reversed bounds. -/
structure Spec where
  anchorX : ℚ
  bandUpper : ℚ := 2
  velocityUpper : ℚ := -3 / 10
  angularUpper : ℚ := -12 / 100

def InDomain (p : Physical) : Prop :=
  ∀ c, domainLo c ≤ p.val c ∧ p.val c ≤ domainHi c

def Pre (s : Spec) (p : Physical) : Prop :=
  InDomain p ∧
  0 ≤ s.anchorX + p.val .y ∧ s.anchorX + p.val .y ≤ s.bandUpper ∧
  p.val .vy ≤ s.velocityUpper ∧ p.val .omega ≤ s.angularUpper

instance (p : Physical) : Decidable (InDomain p) := inferInstanceAs
  (Decidable (∀ c, domainLo c ≤ p.val c ∧ p.val c ≤ domainHi c))

instance (s : Spec) (p : Physical) : Decidable (Pre s p) := inferInstanceAs
  (Decidable (InDomain p ∧
  0 ≤ s.anchorX + p.val .y ∧ s.anchorX + p.val .y ≤ s.bandUpper ∧
  p.val .vy ≤ s.velocityUpper ∧ p.val .omega ≤ s.angularUpper))

structure Box where
  lo : Vector
  hi : Vector

def Box.Mem (b : Box) (p : Physical) : Prop :=
  ∀ c, b.lo c ≤ p.val c ∧ p.val c ≤ b.hi c

def Box.Ordered (b : Box) : Prop := ∀ c, b.lo c ≤ b.hi c

instance (b : Box) : Decidable b.Ordered := inferInstanceAs
  (Decidable (∀ c, b.lo c ≤ b.hi c))

def compile (s : Spec) : Box where
  lo c := match c with
    | .y => max (domainLo .y) (-s.anchorX)
    | _ => domainLo c
  hi c := match c with
    | .y => min (domainHi .y) (s.bandUpper - s.anchorX)
    | .vy => min (domainHi .vy) s.velocityUpper
    | .omega => min (domainHi .omega) s.angularUpper
    | _ => domainHi c

/-- All six coordinates, all rational anchors and thresholds, including empty boxes. -/
theorem compile_correct (s : Spec) (p : Physical) :
    (compile s).Mem p ↔ Pre s p := by
  constructor
  · intro h
    have hy := h .y
    have hv := h .vy
    have hw := h .omega
    simp only [compile, max_le_iff, le_min_iff] at hy hv hw
    refine ⟨?_, ?_, ?_, hv.2.2, hw.2.2⟩
    · intro c
      cases c with
      | vx => exact h .vx
      | vy => exact ⟨hv.1, hv.2.1⟩
      | omega => exact ⟨hw.1, hw.2.1⟩
      | theta => exact h .theta
      | x => exact h .x
      | y => exact ⟨hy.1.1, hy.2.1⟩
    · linarith [hy.1.2]
    · linarith [hy.2.2]
  · rintro ⟨hd, hyl, hyh, hv, hw⟩ c
    have hc := hd c
    cases c with
    | vx => exact hc
    | vy => exact ⟨hc.1, le_min hc.2 hv⟩
    | omega => exact ⟨hc.1, le_min hc.2 hw⟩
    | theta => exact hc
    | x => exact hc
    | y => exact ⟨max_le hc.1 (by linarith), le_min hc.2 (by linarith)⟩

theorem ordered_iff_exists (b : Box) : b.Ordered ↔ ∃ p, b.Mem p := by
  constructor
  · intro h
    exact ⟨⟨b.lo⟩, fun c => ⟨le_rfl, h c⟩⟩
  · rintro ⟨p, h⟩ c
    exact (h c).1.trans (h c).2

theorem compile_nonempty_iff (s : Spec) :
    (compile s).Ordered ↔ ∃ p, Pre s p := by
  rw [ordered_iff_exists]
  simp only [compile_correct]

structure NormalizedBox where
  lo : Normalized
  hi : Normalized

def normalizeBox (n : Normalizer) (b : Box) : NormalizedBox :=
  ⟨normalize n ⟨b.lo⟩, normalize n ⟨b.hi⟩⟩

def NormalizedBox.Mem (b : NormalizedBox) (z : Normalized) : Prop :=
  ∀ c, b.lo.val c ≤ z.val c ∧ z.val c ≤ b.hi.val c

theorem normalized_order (n : Normalizer) (c : Coord) (a b : ℚ) :
    (a - n.offset c) / n.scale c ≤ (b - n.offset c) / n.scale c ↔ a ≤ b := by
  rw [div_le_div_iff_of_pos_right (n.positive c)]
  exact sub_le_sub_iff_right _

theorem normalizeBox_correct (n : Normalizer) (b : Box) (p : Physical) :
    (normalizeBox n b).Mem (normalize n p) ↔ b.Mem p := by
  simp only [NormalizedBox.Mem, normalizeBox, normalize, Box.Mem, normalized_order]

theorem normalized_compile_correct (s : Spec) (n : Normalizer) (z : Normalized) :
    (normalizeBox n (compile s)).Mem z ↔ Pre s (denormalize n z) := by
  conv_lhs => rw [← normalize_denormalize n z]
  rw [normalizeBox_correct, compile_correct]

def Unit (t : Vector) : Prop := ∀ c, 0 ≤ t c ∧ t c ≤ 1

instance (t : Vector) : Decidable (Unit t) := inferInstanceAs
  (Decidable (∀ c, 0 ≤ t c ∧ t c ≤ 1))

def interpolate (b : Box) (t : Vector) : Physical :=
  ⟨fun c => b.lo c + t c * (b.hi c - b.lo c)⟩

theorem interpolate_mem (b : Box) (t : Vector) (hb : b.Ordered) (ht : Unit t) :
    b.Mem (interpolate b t) := by
  intro c
  have hbc := hb c
  have htc := ht c
  change b.lo c ≤ b.lo c + t c * (b.hi c - b.lo c) ∧
    b.lo c + t c * (b.hi c - b.lo c) ≤ b.hi c
  constructor <;> nlinarith

/-- A supplied unit-cube point, not a random distribution. All failure cases
are explicit; no arithmetic is performed on a reversed sampling interval. -/
def sample (s : Spec) (n : Normalizer) (t : Vector) : Option Normalized :=
  if (compile s).Ordered then
    if Unit t then some (normalize n (interpolate (compile s) t)) else none
  else none

theorem sample_sound (s : Spec) (n : Normalizer) (t : Vector) (z : Normalized)
    (h : sample s n t = some z) : Pre s (denormalize n z) := by
  unfold sample at h
  split at h
  next hb =>
    split at h
    next ht =>
      have hz := Option.some.inj h
      rw [← hz, denormalize_normalize]
      exact (compile_correct s _).mp (interpolate_mem _ _ hb ht)
    next => simp at h
  next => simp at h

theorem sample_none_iff (s : Spec) (n : Normalizer) (t : Vector) :
    sample s n t = none ↔ ¬ (∃ p, Pre s p) ∨ ¬ Unit t := by
  simp only [sample, ← compile_nonempty_iff]
  by_cases hb : (compile s).Ordered <;> by_cases ht : Unit t <;> simp [hb, ht]

/-- Inverse coordinates, choosing zero on a collapsed interval. -/
def encodeUnit (b : Box) (p : Physical) : Vector := fun c =>
  if b.hi c - b.lo c = 0 then 0 else (p.val c - b.lo c) / (b.hi c - b.lo c)

theorem encodeUnit_mem (b : Box) (p : Physical) (hp : b.Mem p) :
    Unit (encodeUnit b p) := by
  intro c
  have hc := hp c
  unfold encodeUnit
  split
  next => norm_num
  next hn =>
    have hw : 0 < b.hi c - b.lo c := by
      have := hc.1.trans hc.2
      exact lt_of_le_of_ne (sub_nonneg.mpr this) (Ne.symm hn)
    constructor
    · exact div_nonneg (sub_nonneg.mpr hc.1) hw.le
    · rw [div_le_iff₀ hw]
      linarith [hc.2]

theorem interpolate_encodeUnit (b : Box) (p : Physical) (hp : b.Mem p) :
    interpolate b (encodeUnit b p) = p := by
  apply Physical.ext
  funext c
  have hc := hp c
  change b.lo c + (if b.hi c - b.lo c = 0 then 0 else
    (p.val c - b.lo c) / (b.hi c - b.lo c)) * (b.hi c - b.lo c) = p.val c
  by_cases hw : b.hi c - b.lo c = 0
  · simp only [ite_eq_left hw, zero_mul, add_zero]
    linarith
  · simp [hw]

/-- Every rational point of the specified region is reachable by the generator.
This is coverage of a parametrization, not a claim about a sampling distribution. -/
theorem sample_complete (s : Spec) (n : Normalizer) (z : Normalized)
    (hp : Pre s (denormalize n z)) :
    ∃ t, Unit t ∧ sample s n t = some z := by
  have hm := (compile_correct s _).mpr hp
  have hb := (compile_nonempty_iff s).mpr ⟨_, hp⟩
  have ht := encodeUnit_mem _ _ hm
  refine ⟨encodeUnit (compile s) (denormalize n z), ht, ?_⟩
  simp only [sample, ite_eq_left hb, ite_eq_left ht,
    interpolate_encodeUnit _ _ hm, normalize_denormalize]

/-- Fixed upstream output scale, now exact. The scalar argument is normalized
network output. No theorem here asserts that a network always meets its cap. -/
def physicalOutput (y : ℚ) : ℚ := 181 / 1000 + (12 / 1000) * y
def outputCap : ℚ := 187 / 1000
def OutputOK (y : ℚ) : Prop := physicalOutput y ≤ outputCap

instance (y : ℚ) : Decidable (OutputOK y) := inferInstanceAs
  (Decidable (physicalOutput y ≤ outputCap))

theorem output_threshold_correct (y : ℚ) : OutputOK y ↔ y ≤ 1 / 2 := by
  unfold OutputOK physicalOutput outputCap
  constructor <;> intro h <;> linarith

def loss (y : ℚ) : ℚ := max 0 (physicalOutput y - outputCap)

theorem loss_zero_iff (y : ℚ) : loss y = 0 ↔ OutputOK y := by
  simp [loss, OutputOK]

inductive Verdict where
  | outside | satisfied | violated
  deriving DecidableEq, Repr

def monitor (s : Spec) (n : Normalizer) (z : Normalized) (y : ℚ) : Verdict :=
  if Pre s (denormalize n z) then
    if OutputOK y then .satisfied else .violated
  else .outside

theorem monitor_satisfied_iff (s : Spec) (n : Normalizer) (z : Normalized) (y : ℚ) :
    monitor s n z y = .satisfied ↔ Pre s (denormalize n z) ∧ OutputOK y := by
  unfold monitor
  by_cases hp : Pre s (denormalize n z) <;> by_cases hq : OutputOK y <;> simp [hp, hq]

theorem monitor_violated_iff (s : Spec) (n : Normalizer) (z : Normalized) (y : ℚ) :
    monitor s n z y = .violated ↔ Pre s (denormalize n z) ∧ ¬ OutputOK y := by
  unfold monitor
  by_cases hp : Pre s (denormalize n z) <;> by_cases hq : OutputOK y <;> simp [hp, hq]

theorem monitor_outside_iff (s : Spec) (n : Normalizer) (z : Normalized) (y : ℚ) :
    monitor s n z y = .outside ↔ ¬ Pre s (denormalize n z) := by
  unfold monitor
  by_cases hp : Pre s (denormalize n z) <;> by_cases hq : OutputOK y <;> simp [hp, hq]

end Contribution.Property2
