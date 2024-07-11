import HadwigerNelson.UnitGraph
import HadwigerNelson.ParseVtx
import HadwigerNelson.FactorSquares
import Qq

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
  throwError "can't eval to Float"

def Complex.evalToFloat (z : Expr) : MetaM (Float × Float) := do
  let x ← Real.evalToFloat z.getAppArgs[0]!
  let y ← Real.evalToFloat z.getAppArgs[1]!
  return (x, y)

def getDistance (x y : Float × Float) : Float :=
  let a := x.1 - y.1
  let b := x.2 - y.2
  a^2 + b^2

syntax "theta_calc" : tactic
macro_rules
| `(tactic| theta_calc) =>
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

def aux (li : List Expr) (type : Expr) : MetaM Expr := do match li with
| .nil => return ← Meta.mkAppOptM ``List.nil #[type]
| .cons head tail => return ← Meta.mkAppM ``List.cons #[head, (← aux tail type)]

def UnitGraph.ofVertexes (vertexes : List Expr) : MetaM <| Expr := do
  let vertexesExpr : Expr := ← aux vertexes q(ℂ)
  let mut edges : List Expr := []

  for (u, i) in vertexes.zip (List.finRange vertexes.length) do
    for (v, j) in vertexes.zip (List.finRange vertexes.length) do
      if j <= i then
        continue
      let approxDist := getDistance (← Complex.evalToFloat u) (← Complex.evalToFloat v)
      if Float.abs (approxDist - 1) > 1e-5 then
        continue
      -- dbg_trace "try"
      let finIExpr : Expr := toExpr i
      let finJExpr : Expr := toExpr j
      let mvar_p ← Meta.mkFreshExprMVar <| mkApp2 (mkConst ``unitDistance) u v
      let p := mvar_p.mvarId!
      let edgeExpr : Option Expr ← p.withContext do
        let lolq := Lean.Elab.Tactic.run p (Lean.Elab.Tactic.evalTactic (← `(tactic| theta_calc)))
        let qeq := (← lolq.run).fst
        if !qeq.isEmpty then
          dbg_trace s!"{i} {j}"
          dbg_trace s!"{(← ppExpr u)}"
          dbg_trace s!"{(← ppExpr v)}"
        if qeq.isEmpty then -- how to better check that the proof is correct?
          let proof := (← getExprMVarAssignment? p).get!
          return mkApp4 (mkConst ``UnitGraph.Edge.mk) vertexesExpr finIExpr finJExpr proof
        return none
      if edgeExpr.isSome then
        edges := edgeExpr.get! :: edges

  dbg_trace edges.length
  return mkApp2 (mkConst ``UnitGraph.mk) vertexesExpr (← aux edges (mkApp (mkConst ``UnitGraph.Edge) vertexesExpr))

elab "from_vtx" s:str : term => do
  let vertexes ← ParseVtx.parseVtxFile s.getString
  return ← UnitGraph.ofVertexes vertexes

set_option trace.profiler true

-- set_option maxHeartbeats 0 in
-- noncomputable def tri : UnitGraph := from_vtx "vtx/test510.vtx"

-- noncomputable def a : ℂ := { re := 0, im := 0 }
-- noncomputable def b : ℂ := { re := (-21 - 3 * √5 + 7 * √33 - 3 * √165) / 96, im := (7 * √3 + 21 * √11 - 3 * √15 + 3 * √55) / 96 }

-- set_option maxRecDepth 500 in
-- example : unitDistance a b := by
--   unfold a b
--   theta_calc







-- open UnitGraph

-- example : ¬ planeColorable 2 := by
--   intro h_p_col
--   absurd planeColorable_graph_Colorable h_p_col tri
--   apply Noncolorable_from_unsat
--   dsimp [tri, toCompGraph, CompGraph.ColorablilityCNF]
--   apply LitToNat_equisat _
--   clear h_p_col
--   unsat_native_decide
