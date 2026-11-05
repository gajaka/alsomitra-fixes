import Property2
import Lean.Data.Json

/-! JSON-lines adapter for the proved exact-rational functions.
The parser and IO adapter are tested, not formally verified. -/

open Lean Contribution.Property2

namespace Contribution.CLI

def coordinates : Array Coord := #[.vx, .vy, .omega, .theta, .x, .y]

def checkKeys (j : Json) (allowed : List String) : Except String Unit := do
  let obj ← j.getObj?
  for (key, _) in obj.toList do
    if !allowed.contains key then throw s!"unexpected field: {key}"

def parseRat (j : Json) : Except String ℚ := do
  let s ← j.getStr?
  match s.splitOn "/" with
  | [a] =>
    match a.toInt? with
    | some n => return (n : ℚ)
    | none => throw "expected an integer or numerator/positive-denominator string"
  | [a, b] =>
    match a.toInt?, b.toNat? with
    | some n, some d =>
      if d = 0 then throw "zero denominator" else return mkRat n d
    | _, _ => throw "expected integer numerator and positive natural denominator"
  | _ => throw "invalid rational string"

def parseVector (j : Json) : Except String Vector := do
  let a ← j.getArr?
  if a.size != 6 then throw "exactly six coordinates required: vx, vy, omega, theta, x, y"
  let vx ← parseRat (← j.getArrVal? 0)
  let vy ← parseRat (← j.getArrVal? 1)
  let omega ← parseRat (← j.getArrVal? 2)
  let theta ← parseRat (← j.getArrVal? 3)
  let x ← parseRat (← j.getArrVal? 4)
  let y ← parseRat (← j.getArrVal? 5)
  return fun c => match c with
    | .vx => vx | .vy => vy | .omega => omega | .theta => theta | .x => x | .y => y

def ratJson (q : ℚ) : Json := .str s!"{q.num}/{q.den}"
def vectorJson (v : Vector) : Json := .arr (coordinates.map (fun c => ratJson (v c)))

def optionalRat (j : Json) (key : String) (fallback : ℚ) : Except String ℚ := do
  match j.getObjVal? key with
  | .ok v => parseRat v
  | .error _ => return fallback

def parseSpec (j : Json) : Except String Spec := do
  return {
    anchorX := ← parseRat (← j.getObjVal? "anchor")
    bandUpper := ← optionalRat j "band_upper" 2
    velocityUpper := ← optionalRat j "velocity_upper" (-3 / 10)
    angularUpper := ← optionalRat j "angular_upper" (-12 / 100)
  }

def parseNormalizer (j : Json) : Except String Normalizer := do
  match j.getObjVal? "normalization" with
  | .error _ => return domainNormalizer
  | .ok obj =>
    checkKeys obj ["offset", "scale"]
    let offset ← parseVector (← obj.getObjVal? "offset")
    let scale ← parseVector (← obj.getObjVal? "scale")
    if h : ∀ c, 0 < scale c then
      return { offset, scale, positive := h }
    else throw "normalization scales must all be positive"

def verdictName : Verdict → String
  | .outside => "outside"
  | .satisfied => "satisfied"
  | .violated => "violated"

def observation (s : Spec) (n : Normalizer) (z : Normalized) (y : ℚ) : Json :=
  Json.mkObj [
    ("normalized", vectorJson z.val),
    ("physical", vectorJson (denormalize n z).val),
    ("precondition", .bool (decide (Pre s (denormalize n z)))),
    ("verdict", .str (verdictName (monitor s n z y))),
    ("physical_output", ratJson (physicalOutput y)),
    ("loss", ratJson (loss y))]

def handle (j : Json) : Except String Json := do
  checkKeys j ["action", "anchor", "band_upper", "velocity_upper", "angular_upper",
    "normalization", "output", "unit", "normalized", "physical"]
  let action ← (← j.getObjVal? "action").getStr?
  let s ← parseSpec j
  let n ← parseNormalizer j
  let y ← optionalRat j "output" (1 / 2)
  match action with
  | "bounds" =>
    let b := compile s
    let z := normalizeBox n b
    return Json.mkObj [
      ("status", .str (if b.Ordered then "nonempty" else "empty")),
      ("physical_lo", vectorJson b.lo), ("physical_hi", vectorJson b.hi),
      ("normalized_lo", vectorJson z.lo.val), ("normalized_hi", vectorJson z.hi.val)]
  | "sample" =>
    let t ← parseVector (← j.getObjVal? "unit")
    match sample s n t with
    | none => return Json.mkObj [("status", .str "rejected"),
        ("reason", .str (if (compile s).Ordered then "outside_unit_cube" else "empty_region"))]
    | some z => return (observation s n z y).mergeObj (Json.mkObj [("status", .str "sampled")])
  | "monitor" =>
    let z : Normalized := ⟨← parseVector (← j.getObjVal? "normalized")⟩
    return observation s n z y
  | "encode" =>
    let p : Physical := ⟨← parseVector (← j.getObjVal? "physical")⟩
    if Pre s p then
      return Json.mkObj [("status", .str "encoded"),
        ("unit", vectorJson (encodeUnit (compile s) p))]
    else return Json.mkObj [("status", .str "rejected"), ("reason", .str "outside_region")]
  | _ => throw "unknown action; expected bounds, sample, monitor, or encode"

def reply (line : String) : Json :=
  match Json.parse line >>= handle with
  | .ok response => response
  | .error error => Json.mkObj [("status", .str "error"), ("message", .str error)]

end Contribution.CLI

