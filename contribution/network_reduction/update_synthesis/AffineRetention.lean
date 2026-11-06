import OutputUpdates

/-! Exact retention synthesis for finite families of rational affine updates.
Minimality is among coordinate projections containing the supplied seed,
over all independent rational states. It is not arbitrary quotient minimality. -/
set_option autoImplicit false
namespace Contribution.Reduction.AffineRetention

abbrev Vector (n : ℕ) := Fin n → ℚ

structure Affine (n : ℕ) where
  matrix : Fin n → Fin n → ℚ
  offset : Vector n

def Affine.apply {n : ℕ} (a : Affine n) (x : Vector n) : Vector n :=
  fun i => (∑ j, a.matrix i j * x j) + a.offset i

def Closed {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n)) : Prop :=
  ∀ k i, i ∈ keep → ∀ j, (ops k).matrix i j ≠ 0 → j ∈ keep

instance {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n)) :
    Decidable (Closed ops keep) := by unfold Closed; infer_instance

def grow {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n)) : Finset (Fin n) :=
  keep ∪ Finset.univ.filter (fun j => ∃ k i, i ∈ keep ∧ (ops k).matrix i j ≠ 0)

theorem subset_grow {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n)) :
    keep ⊆ grow ops keep := Finset.subset_union_left

theorem grow_le {n m : ℕ} (ops : Fin m → Affine n) (a b : Finset (Fin n))
    (hab : a ⊆ b) (hb : Closed ops b) : grow ops a ⊆ b := by
  intro j hj
  rcases Finset.mem_union.mp hj with hj | hj
  · exact hab hj
  · obtain ⟨k, i, hi, hij⟩ := (Finset.mem_filter.mp hj).2
    exact hb k i (hab hi) j hij

theorem closed_of_grow_le {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n))
    (h : grow ops keep ⊆ keep) : Closed ops keep := by
  intro k i hi j hij
  exact h (Finset.mem_union_right _ (Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, k, i, hi, hij⟩))

theorem grow_card_lt {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n))
    (h : ¬ Closed ops keep) : keep.card < (grow ops keep).card := by
  apply Finset.card_lt_card
  exact ⟨subset_grow ops keep, fun hle => h (closed_of_grow_le ops keep hle)⟩

def synthesize {n m : ℕ} (ops : Fin m → Affine n) (seed : Finset (Fin n)) : Finset (Fin n) :=
  if _h : Closed ops seed then seed else synthesize ops (grow ops seed)
termination_by n - seed.card
decreasing_by
  have hlt := grow_card_lt ops seed _h
  have hbound : (grow ops seed).card ≤ n := by
    simpa using Finset.card_le_univ (grow ops seed)
  omega

theorem synthesize_spec {n m : ℕ} (ops : Fin m → Affine n) (seed : Finset (Fin n)) :
    seed ⊆ synthesize ops seed ∧ Closed ops (synthesize ops seed) ∧
    ∀ other, seed ⊆ other → Closed ops other → synthesize ops seed ⊆ other := by
  fun_induction synthesize ops seed with
  | case1 seed h => exact ⟨Finset.Subset.refl _, h, fun _ hsub _ => hsub⟩
  | case2 seed h ih =>
    exact ⟨Finset.Subset.trans (subset_grow ops seed) ih.1, ih.2.1,
      fun other hsub hclosed => ih.2.2 other (grow_le ops seed other hsub hclosed) hclosed⟩

abbrev Reduced {n : ℕ} (keep : Finset (Fin n)) := {i // i ∈ keep} → ℚ

def project {n : ℕ} (keep : Finset (Fin n)) (x : Vector n) : Reduced keep := fun i => x i.val
def extend {n : ℕ} (keep : Finset (Fin n)) (x : Reduced keep) : Vector n :=
  fun i => if h : i ∈ keep then x ⟨i,h⟩ else 0
def reducedApply {n : ℕ} (keep : Finset (Fin n)) (a : Affine n)
    (x : Reduced keep) : Reduced keep := project keep (a.apply (extend keep x))

theorem project_extend {n : ℕ} (keep : Finset (Fin n)) (x : Reduced keep) :
    project keep (extend keep x) = x := by funext i; simp [project, extend, i.property]

theorem apply_factors {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n))
    (hc : Closed ops keep) (k : Fin m) (x : Vector n) :
    project keep ((ops k).apply x) = reducedApply keep (ops k) (project keep x) := by
  funext i
  change (∑ j, (ops k).matrix i.val j * x j) + _ =
    (∑ j, (ops k).matrix i.val j * extend keep (project keep x) j) + _
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : (ops k).matrix i.val j = 0
  · simp [hz]
  · simp [extend, project, hc k i.val i.property j hz]

def basis {n : ℕ} (j : Fin n) : Vector n := fun i => if i = j then 1 else 0

theorem closed_of_factors {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n))
    (red : Fin m → Reduced keep → Reduced keep)
    (hf : ∀ k x, project keep ((ops k).apply x) = red k (project keep x)) :
    Closed ops keep := by
  intro k i hi j hcoeff
  by_contra hj
  have heq : project keep (basis j) = project keep (fun _ => 0) := by
    funext t
    have ht : t.val ≠ j := by intro he; exact hj (he ▸ t.property)
    simp [project, basis, ht]
  have hsame : project keep ((ops k).apply (basis j)) =
      project keep ((ops k).apply (fun _ => 0)) := by rw [hf, hf, heq]
  have he := congrFun hsame ⟨i, hi⟩
  simp [project, Affine.apply, basis, mul_ite] at he
  exact hcoeff he

theorem factorization_iff_closed {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n)) :
    (∃ red : Fin m → Reduced keep → Reduced keep,
      ∀ k x, project keep ((ops k).apply x) = red k (project keep x)) ↔ Closed ops keep := by
  constructor
  · rintro ⟨red, hf⟩; exact closed_of_factors ops keep red hf
  · intro hc; exact ⟨fun k => reducedApply keep (ops k), apply_factors ops keep hc⟩

theorem synthesis_minimal {n m : ℕ} (ops : Fin m → Affine n)
    (seed other : Finset (Fin n)) (hseed : seed ⊆ other)
    (red : Fin m → Reduced other → Reduced other)
    (hf : ∀ k x, project other ((ops k).apply x) = red k (project other x)) :
    synthesize ops seed ⊆ other :=
  (synthesize_spec ops seed).2.2 other hseed (closed_of_factors ops other red hf)

def run {n m : ℕ} (ops : Fin m → Affine n) : List (Fin m) → Vector n → Vector n
  | [], x => x
  | k :: ks, x => run ops ks ((ops k).apply x)

def reducedRun {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n)) :
    List (Fin m) → Reduced keep → Reduced keep
  | [], x => x
  | k :: ks, x => reducedRun ops keep ks (reducedApply keep (ops k) x)

theorem run_factors {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n))
    (hc : Closed ops keep) (word : List (Fin m)) (x : Vector n) :
    project keep (run ops word x) = reducedRun ops keep word (project keep x) := by
  induction word generalizing x with
  | nil => rfl
  | cons k ks ih => simp only [run, reducedRun, ih, apply_factors ops keep hc]

def RR {n : ℕ} (keep : Finset (Fin n)) (s t : Vector n) : Prop :=
  project keep s = project keep t

def stateSetoid {n : ℕ} (keep : Finset (Fin n)) : Setoid (Vector n) where
  r := RR keep
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem RR_preserved {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n))
    (hc : Closed ops keep) (word : List (Fin m)) {s t : Vector n} (h : RR keep s t) :
    RR keep (run ops word s) (run ops word t) := by
  change project keep (run ops word s) = project keep (run ops word t)
  rw [run_factors ops keep hc, run_factors ops keep hc, h]

def observableAlgebra {n : ℕ} (keep : Finset (Fin n)) : Subalgebra ℝ (Vector n → ℝ) :=
  (OutputUpdates.pullback (project keep)).range

def Stable {S : Type} (op : S → S) (algebra : Subalgebra ℝ (S → ℝ)) : Prop :=
  ∀ f ∈ algebra, f ∘ op ∈ algebra

theorem algebra_stable {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n))
    (hc : Closed ops keep) (k : Fin m) :
    Stable (ops k).apply (observableAlgebra keep) := by
  rintro f ⟨g, rfl⟩
  refine ⟨g ∘ reducedApply keep (ops k), ?_⟩
  funext x
  exact congrArg g (apply_factors ops keep hc k x).symm

theorem algebra_stable_run {n m : ℕ} (ops : Fin m → Affine n) (keep : Finset (Fin n))
    (hc : Closed ops keep) (word : List (Fin m)) :
    Stable (run ops word) (observableAlgebra keep) := by
  rintro f ⟨g, rfl⟩
  refine ⟨g ∘ reducedRun ops keep word, ?_⟩
  funext x
  exact congrArg g (run_factors ops keep hc word x).symm

end Contribution.Reduction.AffineRetention
