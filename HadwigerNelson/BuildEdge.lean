/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import HadwigerNelson.FactorSquares
import HadwigerNelson.ParseVtx
import HadwigerNelson.UnitGraph
import Qq

/-!
# `build_edge` tactic

In this file we implement `build_edge` tactic and `from_vtx` elaboration rule.

## Main declarations

* `Real.evalToFloat`: evaluates some expressions of type `ℝ` to `Float`. We use it to filter pairs
  of vertexes that are likely at unit distance from each other.
* `build_edge`: tactic that proves `unitDistance u v` for fixed `u` and `v`. It successfully proves
  it for number which are linear combination of square roots of naturals over rationals.
* `from_vtx`: constructs a unit distance graph from `.vtx` file.
-/

open Lean Meta Qq

partial def Real.evalToFloat (x : Expr) : MetaM Float := do
  if x.nat?.isSome then
    return Float.ofNat x.nat?.get!
  if x.isAppOf ``Real.sqrt then
    let arg ← Real.evalToFloat x.getAppArgs[0]!
    return Float.sqrt arg
  if x.isAppOf ``Neg.neg then
    let args := x.getAppArgs
    let x ← Real.evalToFloat args[args.size - 1]!
    return -x
  if x.isAppOf ``HAdd.hAdd then
    let args := x.getAppArgs
    let x ← Real.evalToFloat args[args.size - 2]!
    let y ← Real.evalToFloat args[args.size - 1]!
    return x + y
  if x.isAppOf ``HSub.hSub then
    let args := x.getAppArgs
    let x ← Real.evalToFloat args[args.size - 2]!
    let y ← Real.evalToFloat args[args.size - 1]!
    return x - y
  if x.isAppOf ``HMul.hMul then
    let args := x.getAppArgs
    let x ← Real.evalToFloat args[args.size - 2]!
    let y ← Real.evalToFloat args[args.size - 1]!
    return x * y
  if x.isAppOf ``HDiv.hDiv then
    let args := x.getAppArgs
    let x ← Real.evalToFloat args[args.size - 2]!
    let y ← Real.evalToFloat args[args.size - 1]!
    return x / y
  throwError "cannot eval to Float"

def Complex.evalToFloat (z : Expr) : MetaM (Float × Float) := do
  let x ← Real.evalToFloat z.getAppArgs[0]!
  let y ← Real.evalToFloat z.getAppArgs[1]!
  return (x, y)

def getDistance (x y : Float × Float) : Float :=
  let a := x.1 - y.1
  let b := x.2 - y.2
  a^2 + b^2

syntax "build_edge" : tactic
macro_rules
| `(tactic| build_edge) =>
    `(tactic|
      simp [unitDistance, Complex.abs, Complex.normSq];
      repeat (fail_if_no_progress (
        ring_nf <;>
        norm_num <;>
        (try (rw [← Real.sqrt_mul (by simp)]; norm_num)) <;>
        factor_sqrt <;>
        (try (rw [← Real.sqrt_div_self]; norm_num))
      ))
    )

def UnitGraph.ofVertexes (vertexes : List Expr) : MetaM <| Expr := do
  let vertexesExpr : Expr := ← mkListLit q(ℂ) vertexes
  let mut edges : List Expr := []

  for (u, i) in vertexes.zip (List.finRange vertexes.length) do
    for (v, j) in vertexes.zip (List.finRange vertexes.length) do
      if j <= i then
        continue
      let approxDist := getDistance (← Complex.evalToFloat u) (← Complex.evalToFloat v)
      if Float.abs (approxDist - 1) > 1e-5 then
        continue
      let finIExpr : Expr := toExpr i
      let finJExpr : Expr := toExpr j
      let mvar_p ← mkFreshExprMVar <| mkApp2 (mkConst ``unitDistance) u v
      let p := mvar_p.mvarId!
      let edgeExpr : Option Expr ← p.withContext do
        let lolq := Lean.Elab.Tactic.run p (Lean.Elab.Tactic.evalTactic (← `(tactic| build_edge)))
        let qeq := (← lolq.run).fst
        if !qeq.isEmpty then
          dbg_trace s!"Cannot prove edge: {i} {j}"
          dbg_trace s!"{(← ppExpr u)}"
          dbg_trace s!"{(← ppExpr v)}"
        if qeq.isEmpty then -- how to better check that the proof is correct?
          let proof := (← getExprMVarAssignment? p).get!
          return mkApp4 (mkConst ``UnitGraph.Edge.mk) vertexesExpr finIExpr finJExpr proof
        return none
      if edgeExpr.isSome then
        edges := edgeExpr.get! :: edges

  dbg_trace s!"Built {edges.length} edges"
  return mkApp2 (mkConst ``UnitGraph.mk) vertexesExpr
    (← mkListLit (mkApp (mkConst ``UnitGraph.Edge) vertexesExpr) edges)

elab "from_vtx" s:str : term => do
  let vertexes ← ParseVtx.parseVtxFile s.getString
  return ← UnitGraph.ofVertexes vertexes
