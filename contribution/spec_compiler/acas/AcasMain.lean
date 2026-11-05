import AcasExample
import Lean

set_option autoImplicit false
namespace Contribution.RegionCompiler.Acas
open Lean

def coords : List Coord := [.rho, .theta, .psi, .ownSpeed, .intruderSpeed]

def probes : List (String × Physical Coord ℚ) := [
  ("valid_50", flight 50),
  ("invalid_100", flight 100),
  ("boundary_60", flight 60),
  ("zero_speed", flight 0),
  ("just_below_60", flight (59999/1000)),
  ("just_above_60", flight (60001/1000)),
  ("maximum_speed", flight 1200),
  ("negative_speed", flight (-1)),
  ("above_domain", flight 1201),
  ("exact_thresholds", point distanceThreshold 0 0 1145 60),
  ("distance_too_low", point (distanceThreshold-1/1000) 0 0 1200 50),
  ("own_speed_too_low", point 60000 0 0 1144 50),
  ("angle_outside", point 60000 2 0 1200 50),
  ("distance_outside", point 60001 0 0 1200 50)]

def report (name : String) (x : Physical Coord ℚ) : Json :=
  let z := normalizePoint units x
  Json.mkObj [
    ("case", Json.str name),
    ("physical", toJson (coords.map fun i => toString (x.val i))),
    ("normalized", toJson (coords.map fun i => toString (z.val i))),
    ("reference", toJson (referenceCheck units z)),
    ("printed", toJson (printedCheck units z)),
    ("corrected", toJson (correctedCheck units z))]

def parseRat (s : String) : Except String ℚ :=
  match s.splitOn "/" with
  | [num] => match num.toInt? with
    | some n => .ok (n : ℚ)
    | none => .error "Expected an integer or an exact fraction n/d."
  | [num, den] => match num.toInt?, den.toNat? with
    | some n, some d =>
      if d = 0 then .error "The denominator must be positive."
      else .ok ((n : ℚ) / (d : ℚ))
    | _, _ => .error "Expected an integer numerator and a positive denominator."
  | _ => .error "Expected an integer or an exact fraction n/d."

end Contribution.RegionCompiler.Acas

def main (args : List String) : IO UInt32 := do
  let stdout ← IO.getStdout
  let stderr ← IO.getStderr
  if args.isEmpty then
    for (name, x) in Contribution.RegionCompiler.Acas.probes do
      stdout.putStrLn (Contribution.RegionCompiler.Acas.report name x).compress
    return 0
  match args.mapM Contribution.RegionCompiler.Acas.parseRat with
  | .ok [rho, theta, psi, own, intruder] =>
    stdout.putStrLn (Contribution.RegionCompiler.Acas.report "custom"
      (Contribution.RegionCompiler.Acas.point rho theta psi own intruder)).compress
    return 0
  | .ok _ =>
    stderr.putStrLn "Expected five values: rho theta psi own_speed intruder_speed."
    return 2
  | .error message =>
    stderr.putStrLn message
    return 2
