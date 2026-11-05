import RegionCheck

/-! A sufficient closed fragment with exact zero-loss meaning, and a standard
topological obstruction for strict bounds. These are not novelty claims. -/
set_option autoImplicit false
namespace Contribution.RegionCompiler

inductive ClosedFormula (ι K : Type*) where
  | top | bot
  | upper : ι → K → ClosedFormula ι K
  | lower : ι → K → ClosedFormula ι K
  | conj : ClosedFormula ι K → ClosedFormula ι K → ClosedFormula ι K
  | disj : ClosedFormula ι K → ClosedFormula ι K → ClosedFormula ι K
  deriving Repr

def ClosedFormula.embed {ι K : Type*} : ClosedFormula ι K → Formula ι K
  | .top => .top
  | .bot => .bot
  | .upper i k => .atom ⟨i,.le,k⟩
  | .lower i k => .atom ⟨i,.ge,k⟩
  | .conj p q => .conj p.embed q.embed
  | .disj p q => .disj p.embed q.embed

def ClosedFormula.loss {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    ClosedFormula ι K → (ι → K) → K
  | .top, _ => 0
  | .bot, _ => 1
  | .upper i k, x => max 0 (x i-k)
  | .lower i k, x => max 0 (k-x i)
  | .conj p q, x => p.loss x + q.loss x
  | .disj p q, x => p.loss x * q.loss x

theorem loss_nonnegative {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : ClosedFormula ι K) (x : ι → K) : 0 ≤ p.loss x := by
  induction p with
  | top => exact le_rfl
  | bot => exact zero_le_one
  | upper i k => exact le_max_left _ _
  | lower i k => exact le_max_left _ _
  | conj p q hp hq => exact add_nonneg hp hq
  | disj p q hp hq => exact mul_nonneg hp hq

theorem loss_zero_correct {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : ClosedFormula ι K) (x : ι → K) : p.loss x = 0 ↔ p.embed.holds x := by
  induction p with
  | top => simp [ClosedFormula.loss,ClosedFormula.embed,Formula.holds]
  | bot => simp [ClosedFormula.loss,ClosedFormula.embed,Formula.holds]
  | upper i k => simp [ClosedFormula.loss,ClosedFormula.embed,Formula.holds,Atom.holds,Comparison.holds]
  | lower i k => simp [ClosedFormula.loss,ClosedFormula.embed,Formula.holds,Atom.holds,Comparison.holds]
  | conj p q hp hq =>
    change p.loss x + q.loss x = 0 ↔ p.embed.holds x ∧ q.embed.holds x
    rw [← hp,← hq]
    have hpn := loss_nonnegative p x
    have hqn := loss_nonnegative q x
    constructor
    · intro h; constructor <;> linarith
    · rintro ⟨h1,h2⟩; simp [h1,h2]
  | disj p q hp hq => simp [ClosedFormula.loss,ClosedFormula.embed,Formula.holds,mul_eq_zero,hp,hq]

theorem loss_continuous {ι : Type*} (p : ClosedFormula ι ℝ) : Continuous p.loss := by
  induction p with
  | top => exact continuous_const
  | bot => exact continuous_const
  | upper i k => exact continuous_const.max ((continuous_apply i).sub continuous_const)
  | lower i k => exact continuous_const.max (continuous_const.sub (continuous_apply i))
  | conj p q hp hq => exact hp.add hq
  | disj p q hp hq => exact hp.mul hq

def normalizeClosed {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : AffineCoordinates ι K) : ClosedFormula ι K → ClosedFormula ι K
  | .top => .top
  | .bot => .bot
  | .upper i k => .upper i ((k-n.offset i)/n.scale i)
  | .lower i k => .lower i ((k-n.offset i)/n.scale i)
  | .conj p q => .conj (normalizeClosed n p) (normalizeClosed n q)
  | .disj p q => .disj (normalizeClosed n p) (normalizeClosed n q)

theorem normalized_closed_embed {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : AffineCoordinates ι K) (p : ClosedFormula ι K) :
    (normalizeClosed n p).embed = mapAtoms (normalizeAtom n) p.embed := by
  induction p with
  | top => rfl
  | bot => rfl
  | upper i k => rfl
  | lower i k => rfl
  | conj p q hp hq => simp [normalizeClosed,ClosedFormula.embed,mapAtoms,hp,hq]
  | disj p q hp hq => simp [normalizeClosed,ClosedFormula.embed,mapAtoms,hp,hq]

theorem normalized_loss_correct {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : AffineCoordinates ι K) (p : ClosedFormula ι K) (z : Normalized ι K) :
    (normalizeClosed n p).loss z.val = 0 ↔ p.embed.holds (denormalizePoint n z).val := by
  rw [loss_zero_correct,normalized_closed_embed,normalized_formula]

theorem normalized_loss_checker_agree {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : AffineCoordinates ι K) (p : ClosedFormula ι K) (z : Normalized ι K) :
    checkNormalized n ⟨p.embed⟩ z = true ↔ (normalizeClosed n p).loss z.val = 0 :=
  (checkNormalized_correct n ⟨p.embed⟩ z).trans (normalized_loss_correct n p z).symm

/-- Even without demanding differentiability or nonnegativity, no continuous
real-valued loss can have exactly x<0 as its zero set. -/
theorem strict_boundary_obstruction :
    ¬ ∃ loss : ℝ → ℝ, Continuous loss ∧ ∀ x, loss x = 0 ↔ x < 0 := by
  rintro ⟨loss,hc,hz⟩
  have hclosed : IsClosed {x : ℝ | loss x = 0} := isClosed_eq hc continuous_const
  have heq : {x : ℝ | loss x = 0} = Set.Iio 0 := Set.ext hz
  rw [heq] at hclosed
  have hzero : (0 : ℝ) ∈ closure (Set.Iio (0 : ℝ)) := by
    rw [closure_Iio]
    exact (le_refl (0 : ℝ))
  rw [hclosed.closure_eq] at hzero
  exact lt_irrefl (0 : ℝ) hzero

end Contribution.RegionCompiler
