import Rounding

set_option autoImplicit false
noncomputable section
namespace Contribution.Binary32

theorem finite_values : Set.Finite {x : ℝ | Finite x} := by
  let ms : Set ℤ := Set.Icc (-(2^24)) (2^24)
  let es : Set ℤ := Set.Icc (-149) 104
  have h := (Set.finite_Icc (-(2^24) : ℤ) (2^24)).prod (Set.finite_Icc (-149 : ℤ) 104)
  apply (h.image (fun p : ℤ × ℤ => (p.1 : ℝ)*(2 : ℝ)^p.2)).subset
  intro x hx
  obtain ⟨m,e,hm,he1,he2,rfl⟩ := hx
  refine ⟨(m,e),?_,rfl⟩
  exact ⟨⟨(abs_lt.mp hm).1.le,(abs_lt.mp hm).2.le⟩,⟨he1,he2⟩⟩

theorem finite_zero : Finite 0 := by
  refine ⟨0,0,by norm_num,by norm_num,by norm_num,?_⟩
  norm_num

theorem nearest_exists (x : ℝ) : ∃ y, Nearest x y := by
  obtain ⟨y,hy,hmin⟩ := Set.exists_min_image {y : ℝ | Finite y}
    (fun y => |y-x|) finite_values ⟨0,finite_zero⟩
  exact ⟨y,hy,hmin⟩

/-- Noncomputable semantic witness; not an executable replacement for BLAS. -/
def nearestChoice (x : ℝ) : ℝ := Classical.choose (nearest_exists x)

theorem nearestChoice_correct : CorrectRounding nearestChoice := by
  intro x _
  exact Classical.choose_spec (nearest_exists x)

end Contribution.Binary32
