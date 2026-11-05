import Mathlib

/-! Exact Boolean combinations of axis-aligned bounds. Target regions are
finite unions of cells, each stored as a conjunction of bound literals.
Cells may be unbounded, empty or redundant; no bounding hull is substituted.
All semantic theorems quantify over arbitrary coordinate types and ordered
fields. Rational instantiations are executable. -/
set_option autoImplicit false
namespace Contribution.RegionCompiler

inductive Comparison where
  | le | lt | ge | gt
  deriving DecidableEq, Repr

def Comparison.holds {K : Type*} [LinearOrder K] : Comparison → K → K → Prop
  | .le, x, k => x ≤ k
  | .lt, x, k => x < k
  | .ge, x, k => k ≤ x
  | .gt, x, k => k < x

def Comparison.flip : Comparison → Comparison
  | .le => .gt
  | .lt => .ge
  | .ge => .lt
  | .gt => .le

theorem flip_correct {K : Type*} [LinearOrder K] (c : Comparison) (x k : K) :
    c.flip.holds x k ↔ ¬ c.holds x k := by
  cases c <;> simp [Comparison.flip,Comparison.holds]

structure Atom (ι K : Type*) where
  axis : ι
  cmp : Comparison
  cut : K
  deriving Repr, DecidableEq

def Atom.holds {ι K : Type*} [LinearOrder K] (a : Atom ι K) (x : ι → K) : Prop :=
  a.cmp.holds (x a.axis) a.cut

def Atom.flip {ι K : Type*} (a : Atom ι K) : Atom ι K := {a with cmp := a.cmp.flip}

theorem atom_flip_correct {ι K : Type*} [LinearOrder K] (a : Atom ι K) (x : ι → K) :
    a.flip.holds x ↔ ¬ a.holds x := flip_correct a.cmp (x a.axis) a.cut

inductive Formula (ι K : Type*) where
  | top | bot
  | atom : Atom ι K → Formula ι K
  | conj : Formula ι K → Formula ι K → Formula ι K
  | disj : Formula ι K → Formula ι K → Formula ι K
  | neg : Formula ι K → Formula ι K
  deriving Repr, DecidableEq

def Formula.holds {ι K : Type*} [LinearOrder K] : Formula ι K → (ι → K) → Prop
  | .top, _ => True
  | .bot, _ => False
  | .atom a, x => a.holds x
  | .conj p q, x => p.holds x ∧ q.holds x
  | .disj p q, x => p.holds x ∨ q.holds x
  | .neg p, x => ¬ p.holds x

abbrev Cell (ι K : Type*) := List (Atom ι K)
abbrev Region (ι K : Type*) := List (Cell ι K)

def cellHolds {ι K : Type*} [LinearOrder K] (c : Cell ι K) (x : ι → K) : Prop :=
  ∀ a ∈ c, a.holds x

def regionHolds {ι K : Type*} [LinearOrder K] (r : Region ι K) (x : ι → K) : Prop :=
  ∃ c ∈ r, cellHolds c x

def meet {ι K : Type*} (r s : Region ι K) : Region ι K :=
  r.flatMap fun a => s.map fun b => a ++ b

theorem cell_append {ι K : Type*} [LinearOrder K] (a b : Cell ι K) (x : ι → K) :
    cellHolds (a++b) x ↔ cellHolds a x ∧ cellHolds b x := by
  simp [cellHolds,or_imp,forall_and]

theorem union_correct {ι K : Type*} [LinearOrder K] (r s : Region ι K) (x : ι → K) :
    regionHolds (r++s) x ↔ regionHolds r x ∨ regionHolds s x := by
  simp [regionHolds,or_and_right,exists_or]

theorem meet_correct {ι K : Type*} [LinearOrder K] (r s : Region ι K) (x : ι → K) :
    regionHolds (meet r s) x ↔ regionHolds r x ∧ regionHolds s x := by
  simp only [regionHolds,meet,List.mem_flatMap,List.mem_map]
  constructor
  · rintro ⟨c,⟨a,ha,b,hb,rfl⟩,hc⟩
    exact ⟨⟨a,ha,(cell_append a b x).mp hc |>.1⟩,⟨b,hb,(cell_append a b x).mp hc |>.2⟩⟩
  · rintro ⟨⟨a,ha,hax⟩,⟨b,hb,hbx⟩⟩
    exact ⟨a++b,⟨a,ha,b,hb,rfl⟩,(cell_append a b x).mpr ⟨hax,hbx⟩⟩

/-- The polarity is propagated structurally, so negation uses strict bounds
and De Morgan laws instead of complementing an enclosing closed box. -/
def lower {ι K : Type*} : Formula ι K → Bool → Region ι K
  | .top, true => [[]]
  | .top, false => []
  | .bot, true => []
  | .bot, false => [[]]
  | .atom a, true => [[a]]
  | .atom a, false => [[a.flip]]
  | .conj p q, true => meet (lower p true) (lower q true)
  | .conj p q, false => lower p false ++ lower q false
  | .disj p q, true => lower p true ++ lower q true
  | .disj p q, false => meet (lower p false) (lower q false)
  | .neg p, b => lower p (!b)

theorem lower_correct {ι K : Type*} [LinearOrder K] (p : Formula ι K)
    (x : ι → K) (b : Bool) :
    regionHolds (lower p b) x ↔ if b then p.holds x else ¬ p.holds x := by
  induction p generalizing b with
  | top => cases b <;> simp [lower,regionHolds,cellHolds,Formula.holds]
  | bot => cases b <;> simp [lower,regionHolds,cellHolds,Formula.holds]
  | atom a => cases b <;> simp [lower,regionHolds,cellHolds,Formula.holds,atom_flip_correct]
  | conj p q hp hq =>
    cases b with
    | false =>
      simp [lower,union_correct,hp,hq,Formula.holds]
      tauto
    | true => simp [lower,meet_correct,hp,hq,Formula.holds]
  | disj p q hp hq =>
    cases b <;> simp [lower,meet_correct,union_correct,hp,hq,Formula.holds,not_or]
  | neg p hp => cases b <;> simp [lower,hp,Formula.holds]

def compile {ι K : Type*} (p : Formula ι K) : Region ι K := lower p true

theorem compile_correct {ι K : Type*} [LinearOrder K] (p : Formula ι K) (x : ι → K) :
    regionHolds (compile p) x ↔ p.holds x := by simpa [compile] using lower_correct p x true

end Contribution.RegionCompiler
