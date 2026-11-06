import AffineRetention

/-! Proof-carrying exact linear observations for discrete affine systems.
The certificate proves a least invariant row space containing specified seeds. -/
set_option autoImplicit false
namespace Contribution.Reduction.LinearObservations
open AffineRetention
open scoped Matrix

def observe {n r : ℕ} (rows : Matrix (Fin r) (Fin n) ℚ) (x : Vector n) : Vector r :=
  rows *ᵥ x

def matrix {n : ℕ} (op : Affine n) : Matrix (Fin n) (Fin n) ℚ := Matrix.of op.matrix
def pull {n : ℕ} (op : Affine n) (row : Vector n) : Vector n := row ᵥ* matrix op

def rowSpace {n r : ℕ} (rows : Matrix (Fin r) (Fin n) ℚ) : Submodule ℚ (Vector n) :=
  Submodule.span ℚ (Set.range rows)

def Invariant {n m : ℕ} (ops : Fin m → Affine n) (space : Submodule ℚ (Vector n)) : Prop :=
  ∀ k row, row ∈ space → pull (ops k) row ∈ space

inductive Derivation (p m : ℕ) where
  | seed : Fin p → Derivation p m
  | add : Derivation p m → Derivation p m → Derivation p m
  | scale : ℚ → Derivation p m → Derivation p m
  | next : Fin m → Derivation p m → Derivation p m

def interpret {n p m : ℕ} (seeds : Matrix (Fin p) (Fin n) ℚ)
    (ops : Fin m → Affine n) : Derivation p m → Vector n
  | .seed i => seeds i
  | .add a b => interpret seeds ops a + interpret seeds ops b
  | .scale c a => c • interpret seeds ops a
  | .next k a => pull (ops k) (interpret seeds ops a)

theorem interpret_mem {n p m : ℕ} (seeds : Matrix (Fin p) (Fin n) ℚ)
    (ops : Fin m → Affine n) (space : Submodule ℚ (Vector n))
    (hs : ∀ i, seeds i ∈ space) (hi : Invariant ops space) (d : Derivation p m) :
    interpret seeds ops d ∈ space := by
  induction d with
  | seed i => exact hs i
  | add a b ha hb => exact space.add_mem ha hb
  | scale c a ha => exact space.smul_mem c ha
  | next k a ha => exact hi k _ ha

theorem rows_minimal {n p m r : ℕ} (seeds : Matrix (Fin p) (Fin n) ℚ)
    (ops : Fin m → Affine n) (rows : Matrix (Fin r) (Fin n) ℚ)
    (derivations : Fin r → Derivation p m)
    (hd : ∀ i, rows i = interpret seeds ops (derivations i))
    (space : Submodule ℚ (Vector n)) (hs : ∀ i, seeds i ∈ space)
    (hi : Invariant ops space) : rowSpace rows ≤ space := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [hd]
  exact interpret_mem seeds ops space hs hi (derivations i)

theorem combination_mem {n r : ℕ} (rows : Matrix (Fin r) (Fin n) ℚ) (cs : Fin r → ℚ) :
    (∑ i, cs i • rows i) ∈ rowSpace rows := by
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

theorem invariant_of_rows {n m r : ℕ} (ops : Fin m → Affine n)
    (rows : Matrix (Fin r) (Fin n) ℚ)
    (coefficients : Fin m → Matrix (Fin r) (Fin r) ℚ)
    (hc : ∀ k i, pull (ops k) (rows i) = ∑ j, coefficients k i j • rows j) :
    Invariant ops (rowSpace rows) := by
  intro k row hr
  induction hr using Submodule.span_induction with
  | mem row hrow =>
    obtain ⟨i, rfl⟩ := hrow
    rw [hc]
    exact combination_mem rows _
  | zero => simp [pull]
  | add a b _ _ ha hb =>
    simpa [pull, Matrix.add_vecMul] using (rowSpace rows).add_mem ha hb
  | smul c a _ ha =>
    simpa [pull, Matrix.smul_vecMul] using (rowSpace rows).smul_mem c ha

theorem independent_of_pivots {n r : ℕ} (rows : Matrix (Fin r) (Fin n) ℚ)
    (pivots : Fin r → Fin n)
    (hp : ∀ i j, rows i (pivots j) = if i = j then 1 else 0) :
    LinearIndependent ℚ rows := by
  apply Fintype.linearIndependent_iff.mpr
  intro cs hc i
  have h := congrFun hc (pivots i)
  simpa [Finset.sum_apply, hp, smul_eq_mul] using h

theorem dimension_lower_bound {n p m r : ℕ} (seeds : Matrix (Fin p) (Fin n) ℚ)
    (ops : Fin m → Affine n) (rows : Matrix (Fin r) (Fin n) ℚ)
    (ds : Fin r → Derivation p m) (hd : ∀ i, rows i = interpret seeds ops (ds i))
    (hli : LinearIndependent ℚ rows) (space : Submodule ℚ (Vector n))
    (hs : ∀ i, seeds i ∈ space) (hi : Invariant ops space) :
    r ≤ Module.finrank ℚ space := by
  have hle := Submodule.finrank_mono (rows_minimal seeds ops rows ds hd space hs hi)
  have heq : Module.finrank ℚ (rowSpace rows) = r := by
    change Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i => rows i))) = r
    simpa only [Fintype.card_fin] using
      (finrank_span_eq_card (R := ℚ) (M := Vector n) (b := fun i => rows i) hli)
  omega

theorem affine_factors {n r : ℕ} (rows : Matrix (Fin r) (Fin n) ℚ)
    (op : Affine n) (small : Affine r)
    (hm : rows * matrix op = matrix small * rows)
    (hb : observe rows op.offset = small.offset) (x : Vector n) :
    observe rows (op.apply x) = small.apply (observe rows x) := by
  change rows *ᵥ (matrix op *ᵥ x + op.offset) =
    matrix small *ᵥ (rows *ᵥ x) + small.offset
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec]
  exact congrArg _ hb

theorem sequence_factors {n m r : ℕ} (rows : Matrix (Fin r) (Fin n) ℚ)
    (ops : Fin m → Affine n) (small : Fin m → Affine r)
    (hf : ∀ k x, observe rows ((ops k).apply x) = (small k).apply (observe rows x))
    (word : List (Fin m)) (x : Vector n) :
    observe rows (run ops word x) = run small word (observe rows x) := by
  induction word generalizing x with
  | nil => rfl
  | cons k ks ih => simp only [run, ih, hf]

def algebra {n r : ℕ} (rows : Matrix (Fin r) (Fin n) ℚ) : Subalgebra ℝ (Vector n → ℝ) :=
  (OutputUpdates.pullback (observe rows)).range

theorem algebra_stable {n r : ℕ} (rows : Matrix (Fin r) (Fin n) ℚ)
    (op : Affine n) (small : Affine r)
    (hf : ∀ x, observe rows (op.apply x) = small.apply (observe rows x)) :
    Stable op.apply (algebra rows) := by
  rintro f ⟨g,rfl⟩
  refine ⟨g ∘ small.apply, ?_⟩
  funext x
  exact congrArg g (hf x).symm

end Contribution.Reduction.LinearObservations
