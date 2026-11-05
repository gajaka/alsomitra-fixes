import Property2

/-! Exact interpretation and checked observations of binary32 bit patterns.
This specifies the standard finite binary32 encoding; it does not model
PyTorch arithmetic, GEMM kernels, rounding modes, or hardware instructions. -/

set_option autoImplicit false

namespace Contribution.Float32
open Property2

def signed (bits : Nat) (magnitude : ℚ) : ℚ :=
  if bits / 2^31 = 0 then magnitude else -magnitude

/-- Reject out-of-range words and all NaN/infinity encodings. Both signed zeros
denote rational zero; their original bits remain available in the transcript. -/
def decode (bits : Nat) : Option ℚ :=
  if bits < 2^32 then
    let exponent : Nat := bits / 2^23 % 256
    let fraction : Nat := bits % 2^23
    if exponent = 255 then none
    else if exponent = 0 then some (signed bits ((fraction : ℚ) / 2^149))
    else some (signed bits (((2^23 + fraction : Nat) : ℚ) * (2:ℚ)^exponent / 2^150))
  else none

theorem decode_none_iff (bits : Nat) :
    decode bits = none ↔ 2^32 ≤ bits ∨ bits / 2^23 % 256 = 255 := by
  unfold decode
  split
  next hw =>
    dsimp only
    split
    next he =>
      constructor
      · intro _; exact Or.inr he
      · intro _; rfl
    next he =>
      split <;> simp only [Option.some_ne_none, false_iff, not_or] <;>
        exact ⟨Nat.not_le_of_gt hw, he⟩
  next hw =>
    constructor
    · intro _; exact Or.inl (Nat.le_of_not_gt hw)
    · intro _; rfl

def decodePoint (bits : Coord → Nat) : Option Normalized := do
  let vx ← decode (bits .vx)
  let vy ← decode (bits .vy)
  let omega ← decode (bits .omega)
  let theta ← decode (bits .theta)
  let x ← decode (bits .x)
  let y ← decode (bits .y)
  return ⟨fun c => match c with
    | .vx => vx | .vy => vy | .omega => omega | .theta => theta | .x => x | .y => y⟩

def admissible (s : Spec) (n : Normalizer) (bits : Coord → Nat) : Bool :=
  match decodePoint bits with
  | none => false
  | some z => decide (Pre s (denormalize n z))

/-- The acceptance gate for a proposed float32 input. This theorem does not
assume any correctness of the floating-point generator that proposed it. -/
theorem admissible_iff (s : Spec) (n : Normalizer) (bits : Coord → Nat) :
    admissible s n bits = true ↔
      ∃ z, decodePoint bits = some z ∧ Pre s (denormalize n z) := by
  cases hz : decodePoint bits <;> simp [admissible, hz]

def observe (s : Spec) (n : Normalizer) (bits : Coord → Nat) (out : Nat) : Option Verdict := do
  let z ← decodePoint bits
  let y ← decode out
  return monitor s n z y

theorem observe_satisfied_iff (s : Spec) (n : Normalizer) (bits : Coord → Nat) (out : Nat) :
    observe s n bits out = some .satisfied ↔
      ∃ z y, decodePoint bits = some z ∧ decode out = some y ∧
        Pre s (denormalize n z) ∧ OutputOK y := by
  cases hz : decodePoint bits <;> cases hy : decode out <;>
    simp [observe, hz, hy, monitor_satisfied_iff]

theorem observe_violated_iff (s : Spec) (n : Normalizer) (bits : Coord → Nat) (out : Nat) :
    observe s n bits out = some .violated ↔
      ∃ z y, decodePoint bits = some z ∧ decode out = some y ∧
        Pre s (denormalize n z) ∧ ¬ OutputOK y := by
  cases hz : decodePoint bits <;> cases hy : decode out <;>
    simp [observe, hz, hy, monitor_violated_iff]

theorem observe_outside_iff (s : Spec) (n : Normalizer) (bits : Coord → Nat) (out : Nat) :
    observe s n bits out = some .outside ↔
      ∃ z y, decodePoint bits = some z ∧ decode out = some y ∧
        ¬ Pre s (denormalize n z) := by
  cases hz : decodePoint bits <;> cases hy : decode out <;>
    simp [observe, hz, hy, monitor_outside_iff]

/-- A different observation: input and output have already been materialized
in physical units by float32 operations. No equality with exact affine
reconstruction is assumed. -/
def physicalMonitor (s : Spec) (p : Physical) (y : ℚ) : Verdict :=
  if Pre s p then if y ≤ outputCap then .satisfied else .violated else .outside

theorem physicalMonitor_satisfied_iff (s : Spec) (p : Physical) (y : ℚ) :
    physicalMonitor s p y = .satisfied ↔ Pre s p ∧ y ≤ outputCap := by
  unfold physicalMonitor
  by_cases hp : Pre s p <;> by_cases hy : y ≤ outputCap <;> simp [hp, hy]

theorem physicalMonitor_violated_iff (s : Spec) (p : Physical) (y : ℚ) :
    physicalMonitor s p y = .violated ↔ Pre s p ∧ ¬ y ≤ outputCap := by
  unfold physicalMonitor
  by_cases hp : Pre s p <;> by_cases hy : y ≤ outputCap <;> simp [hp, hy]

theorem physicalMonitor_outside_iff (s : Spec) (p : Physical) (y : ℚ) :
    physicalMonitor s p y = .outside ↔ ¬ Pre s p := by
  unfold physicalMonitor
  by_cases hp : Pre s p <;> by_cases hy : y ≤ outputCap <;> simp [hp, hy]

end Contribution.Float32
