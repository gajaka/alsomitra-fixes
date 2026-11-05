import RegionSyntax

set_option autoImplicit false
namespace Contribution.RegionCompiler

variable {ι K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

@[ext] structure Physical (ι K : Type*) where
  val : ι → K

@[ext] structure Normalized (ι K : Type*) where
  val : ι → K

structure PhysicalSpec (ι K : Type*) where
  formula : Formula ι K

structure NormalizedSpec (ι K : Type*) where
  formula : Formula ι K

structure AffineCoordinates (ι K : Type*) [Zero K] [LT K] where
  offset : ι → K
  scale : ι → K
  positive : ∀ i, 0 < scale i

def normalizePoint (n : AffineCoordinates ι K) (x : Physical ι K) : Normalized ι K :=
  ⟨fun i => (x.val i - n.offset i) / n.scale i⟩

def denormalizePoint (n : AffineCoordinates ι K) (z : Normalized ι K) : Physical ι K :=
  ⟨fun i => z.val i * n.scale i + n.offset i⟩

omit [IsStrictOrderedRing K] in
theorem point_roundtrip (n : AffineCoordinates ι K) (x : Physical ι K) :
    denormalizePoint n (normalizePoint n x) = x := by
  apply Physical.ext
  funext i
  simp [normalizePoint,denormalizePoint,ne_of_gt (n.positive i)]

omit [IsStrictOrderedRing K] in
theorem normalized_roundtrip (n : AffineCoordinates ι K) (z : Normalized ι K) :
    normalizePoint n (denormalizePoint n z) = z := by
  apply Normalized.ext
  funext i
  simp [normalizePoint,denormalizePoint,ne_of_gt (n.positive i)]

def normalizeAtom (n : AffineCoordinates ι K) (a : Atom ι K) : Atom ι K :=
  {a with cut := (a.cut - n.offset a.axis) / n.scale a.axis}

theorem normalized_atom (n : AffineCoordinates ι K) (a : Atom ι K) (z : Normalized ι K) :
    (normalizeAtom n a).holds z.val ↔ a.holds (denormalizePoint n z).val := by
  cases a with
  | mk i cmp cut =>
    cases cmp <;> simp only [normalizeAtom,Atom.holds,Comparison.holds,denormalizePoint]
    · rw [le_div_iff₀ (n.positive i)]; exact le_sub_iff_add_le
    · rw [lt_div_iff₀ (n.positive i)]; exact lt_sub_iff_add_lt
    · rw [div_le_iff₀ (n.positive i)]; exact sub_le_iff_le_add
    · rw [div_lt_iff₀ (n.positive i)]; exact sub_lt_iff_lt_add

def mapAtoms {ι K L : Type*} (f : Atom ι K → Atom ι L) : Formula ι K → Formula ι L
  | .top => .top
  | .bot => .bot
  | .atom a => .atom (f a)
  | .conj p q => .conj (mapAtoms f p) (mapAtoms f q)
  | .disj p q => .disj (mapAtoms f p) (mapAtoms f q)
  | .neg p => .neg (mapAtoms f p)

def normalizeSpec (n : AffineCoordinates ι K) (s : PhysicalSpec ι K) : NormalizedSpec ι K :=
  ⟨mapAtoms (normalizeAtom n) s.formula⟩

theorem normalized_formula (n : AffineCoordinates ι K) (p : Formula ι K) (z : Normalized ι K) :
    (mapAtoms (normalizeAtom n) p).holds z.val ↔ p.holds (denormalizePoint n z).val := by
  induction p with
  | top => rfl
  | bot => rfl
  | atom a => exact normalized_atom n a z
  | conj p q hp hq => simp only [mapAtoms,Formula.holds,hp,hq]
  | disj p q hp hq => simp only [mapAtoms,Formula.holds,hp,hq]
  | neg p hp => simp only [mapAtoms,Formula.holds,hp]

def normalizeRegion (n : AffineCoordinates ι K) (r : Region ι K) : Region ι K :=
  r.map fun c => c.map (normalizeAtom n)

theorem normalized_region (n : AffineCoordinates ι K) (r : Region ι K) (z : Normalized ι K) :
    regionHolds (normalizeRegion n r) z.val ↔ regionHolds r (denormalizePoint n z).val := by
  simp [normalizeRegion,regionHolds,cellHolds,normalized_atom]

/-- Compilation and affine coordinate transformation agree semantically.
No claim that two source lists are syntactically equal is needed. -/
theorem normalization_compilation_commute (n : AffineCoordinates ι K)
    (s : PhysicalSpec ι K) (z : Normalized ι K) :
    regionHolds (compile (normalizeSpec n s).formula) z.val ↔
      regionHolds (normalizeRegion n (compile s.formula)) z.val := by
  rw [compile_correct,normalized_region,compile_correct]
  exact normalized_formula n s.formula z

theorem pipeline_correct (n : AffineCoordinates ι K) (s : PhysicalSpec ι K)
    (z : Normalized ι K) :
    regionHolds (compile (normalizeSpec n s).formula) z.val ↔
      s.formula.holds (denormalizePoint n z).val := by
  rw [compile_correct]
  exact normalized_formula n s.formula z

end Contribution.RegionCompiler
