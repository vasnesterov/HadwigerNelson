/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Lean
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Basic

/-!
# Parsing .vtx

In this file we parse `.vtx` file.

## Main declarations

* `parseVtxFile`: creates `List Expr` representing vertexes from `.vtx` file.
* `parse_vtx` elab rule: creates `List ℂ` of vertexes from `.vtx` file.
-/


open Lean Meta Elab Term

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
  for line in (← IO.FS.readFile vtxPath).splitOn "\n" do
    if line.isEmpty then
      continue
    res := (← parseVertex line) :: res
  return res.reverse

/-- Creates `List ℂ` from `.vtx` file. -/
elab "parse_vtx" s:str : term => do
  return ← mkListLit (mkConst ``Complex) (← parseVtxFile s.getString)

end ParseVtx
