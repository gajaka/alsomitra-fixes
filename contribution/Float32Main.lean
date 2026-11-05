import Float32
import Protocol

open Lean Contribution.Property2
namespace Contribution.Float32CLI
open Contribution.CLI Contribution.Float32

def parseBits (j : Json) : Except String (Coord → Nat) := do
  let a ← j.getArr?
  if a.size != 6 then throw "six binary32 words required"
  let vx ← (← j.getArrVal? 0).getNat?
  let vy ← (← j.getArrVal? 1).getNat?
  let omega ← (← j.getArrVal? 2).getNat?
  let theta ← (← j.getArrVal? 3).getNat?
  let x ← (← j.getArrVal? 4).getNat?
  let y ← (← j.getArrVal? 5).getNat?
  return fun c => match c with
    | .vx => vx | .vy => vy | .omega => omega | .theta => theta | .x => x | .y => y

def decoded (bits : Coord → Nat) : Except String Normalized :=
  match decodePoint bits with
  | some z => .ok z
  | none => .error "non-finite or out-of-range binary32 word"

def bitNormalizer (j : Json) : Except String Normalizer := do
  let offset ← decoded (← parseBits (← j.getObjVal? "offset_bits"))
  let scale ← decoded (← parseBits (← j.getObjVal? "scale_bits"))
  if h : ∀ c, 0 < scale.val c then
    return { offset := offset.val, scale := scale.val, positive := h }
  else throw "decoded scales must be positive"

def handle (j : Json) : Except String Json := do
  checkKeys j ["action", "words", "anchor", "band_upper", "velocity_upper", "angular_upper",
    "offset_bits", "scale_bits", "input_bits", "output_bits", "physical_bits", "physical_output_bits"]
  let action ← (← j.getObjVal? "action").getStr?
  if action = "decode" then
    let words ← (← j.getObjVal? "words").getArr?
    let values ← words.mapM fun word => do
      let bits ← word.getNat?
      return match decode bits with
        | none => Json.null
        | some q => ratJson q
    return Json.mkObj [("values", .arr values)]
  let s ← parseSpec j
  let n ← bitNormalizer j
  if action = "bounds" then
    let b := compile s
    let nb := normalizeBox n b
    return Json.mkObj [("nonempty", .bool (decide b.Ordered)),
      ("normalized_lo", vectorJson nb.lo.val), ("normalized_hi", vectorJson nb.hi.val)]
  let bits ← parseBits (← j.getObjVal? "input_bits")
  if action = "gate" then
    return Json.mkObj [("admissible", .bool (admissible s n bits))]
  if action != "observe" then throw "unknown float32 action"
  let out ← (← j.getObjVal? "output_bits").getNat?
  let z ← decoded bits
  let y ← match decode out with
    | some q => pure q
    | none => throw "non-finite or out-of-range output"
  let verdict ← match observe s n bits out with
    | some v => pure v
    | none => throw "invalid observation"
  let mut result := (observation s n z y).mergeObj (Json.mkObj [
    ("verdict", .str (verdictName verdict)), ("admissible", .bool (admissible s n bits))])
  match j.getObjVal? "physical_bits", j.getObjVal? "physical_output_bits" with
  | .error _, .error _ => pure ()
  | .ok pbits, .ok obits =>
    let p ← decoded (← parseBits pbits)
    let oword ← obits.getNat?
    let o ← match decode oword with
      | some value => pure value
      | none => throw "non-finite materialized output"
    let physical : Physical := ⟨p.val⟩
    result := result.mergeObj (Json.mkObj [
      ("rounded_physical", vectorJson p.val), ("rounded_physical_output", ratJson o),
      ("rounded_verdict", .str (verdictName (physicalMonitor s physical o))),
      ("rounded_precondition", .bool (decide (Pre s physical)))])
  | _, _ => throw "physical input and output words must be supplied together"
  return result

def reply (line : String) : Json :=
  match Json.parse line >>= handle with
  | .ok result => result
  | .error message => Json.mkObj [("status", .str "error"), ("message", .str message)]

end Contribution.Float32CLI

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (Contribution.Float32CLI.reply line).compress
    stdout.flush
