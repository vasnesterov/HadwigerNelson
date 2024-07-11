import Lean
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic

open Lean Elab Term

namespace ParseVtx

syntax:max "Sqrt[" withoutPosition(term) "]" : term
macro_rules | `(Sqrt[$x]) => `(Real.sqrt $x)

def parseCoord (s : String) : TermElabM Expr := do
  let .ok stx := Parser.runParserCategory (← getEnv) `term s |
    throwError s!"Failed to parse coordinate: {s}"
  return ← Term.elabTerm stx (mkConst ``Real)

def parseVertex (vtx : String) : TermElabM Expr := do
  assert! (vtx.front == '{')
  assert! (vtx.back = '}')

  let coords := ((vtx.toSubstring.drop 1).dropRight 1).toString.splitOn ", "
  assert! (coords.length == 2)
  let x := coords[0]!
  let y := coords[1]!

  let xExpr ← parseCoord x
  let yExpr ← parseCoord y
  return mkApp2 (mkConst ``Complex.mk) xExpr yExpr

def parseVtxFile (vtxPath : System.FilePath) : TermElabM (List Expr) := do
  let mut res := []
  for vtx in (← IO.FS.readFile vtxPath).splitOn "\n" do
    res := (← parseVertex vtx) :: res
  return res.reverse


def aux (li : List Expr) (type : Expr) : MetaM Expr := do match li with
| .nil => return ← Meta.mkAppOptM ``List.nil #[type]
| .cons head tail => return ← Meta.mkAppM ``List.cons #[head, (← aux tail type)]

elab "parse_vtx" s:str : term => do
  return ← aux (← parseVtxFile s.getString) (mkConst ``Complex)

end ParseVtx
