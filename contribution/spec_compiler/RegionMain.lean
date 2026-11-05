import RegionExamples
import RegionAlsomitra
import Lean

set_option autoImplicit false
namespace Contribution.RegionCompiler.Runtime
open Lean

def ast : Formula Unit ℚ → Json
  | .top => toJson (["top"] : List String)
  | .bot => toJson (["bot"] : List String)
  | .atom a => Json.arr #[Json.str (match a.cmp with | .le => "le" | .lt => "lt" | .ge => "ge" | .gt => "gt"),Json.str (toString a.cut)]
  | .conj p q => Json.arr #[Json.str "and",ast p,ast q]
  | .disj p q => Json.arr #[Json.str "or",ast p,ast q]
  | .neg p => Json.arr #[Json.str "not",ast p]

def base : List (Formula Unit ℚ) := [.top,.bot] ++
  ([Comparison.le,.lt,.ge,.gt].flatMap fun cmp =>
    ([-1,0,1] : List ℚ).map fun k => .atom ⟨(),cmp,k⟩)

def combinations : List (Formula Unit ℚ) := base.flatMap fun p => base.flatMap fun q =>
  [.conj p q,.disj p q]

def corpus : List (Formula Unit ℚ) := base ++ base.map Formula.neg ++
  combinations ++ combinations.map Formula.neg

def normalizers : List (AffineCoordinates Unit ℚ) :=
  [⟨fun _ => 0,fun _ => 1,by intro i; norm_num⟩,
   ⟨fun _ => 10,fun _ => 10,by intro i; norm_num⟩,
   ⟨fun _ => -1,fun _ => 3/2,by intro i; norm_num⟩]

def probes : List ℚ := [-2,-1,-1/2,0,1/2,1,3/2,2,3]

def report (p : Formula Unit ℚ) : Json := Json.mkObj [
  ("formula",ast p),
  ("checks",toJson (normalizers.map fun n => probes.map fun q =>
    checkNormalized n ⟨p⟩ ⟨fun _ => q⟩)),
  ("cells",toJson (compile p).length)]

def exampleReport : Json := Json.mkObj [
  ("kind",Json.str "disconnected"),
  ("formula",ast Examples.disconnected.formula),
  ("probes",toJson (([0,1/10,1/5,1/2,4/5,9/10,1] : List ℚ).map toString)),
  ("checks",toJson (([0,1/10,1/5,1/2,4/5,9/10,1] : List ℚ).map fun v =>
    checkNormalized Examples.units Examples.disconnected (Examples.point v)))]

end Contribution.RegionCompiler.Runtime

def main : IO Unit := do
  let stdout ← IO.getStdout
  for p in Contribution.RegionCompiler.Runtime.corpus do
    stdout.putStrLn (Contribution.RegionCompiler.Runtime.report p).compress
  stdout.putStrLn Contribution.RegionCompiler.Runtime.exampleReport.compress
