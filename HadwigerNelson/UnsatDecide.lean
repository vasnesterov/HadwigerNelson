import LeanSAT
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Use

namespace CNF

def liftToNat {α : Type} (emb : α → ℕ) (cnf : CNF α) : CNF ℕ :=
  cnf.map (fun cl => cl.map fun (a, b) => (emb a, b))

theorem lift_equisat {α : Type} [Fintype α] [Inhabited α] {emb : α → ℕ} {cnf : CNF α}
    (h_inj : emb.Injective) (h_unsat : (liftToNat emb cnf).unsat) : cnf.unsat := by
  intro assign
  simp_all [unsat, eval, liftToNat, List.all_eq]
  let embInv := Function.invFun emb
  have h_li : Function.LeftInverse embInv emb := by exact Function.leftInverse_invFun h_inj
  specialize h_unsat fun x => assign (embInv x)
  obtain ⟨cl, h_cl_in, h_cl_eval⟩ := h_unsat
  use cl
  constructor
  · assumption
  simp [Clause.eval] at *
  simp [List.any_map] at h_cl_eval
  simp [List.any_eq] at *
  intro a ha
  specialize h_cl_eval a
  simp [h_li a] at h_cl_eval
  exact h_cl_eval ha

end CNF

open BVDecide Lean Meta
/--
Turn an `LratCert` into a proof that some `reflected` expression is UNSAT by providing a `verifier`
function together with a correctenss theorem for it.

- `verifier` is expected to have type `α → LratCert → Bool`
- `unsat_of_verifier_eq_true` is expected to have type
  `∀ (b : α) (c : LratCert), verifier b c = true → unsat b`
-/
def BVDecide.LratCert.toReflectionProofCNF (cert : LratCert) (cfg : TacticContext) (cnfExpr : Expr)
    (verifier : Name) (unsat_of_verifier_eq_true : Name)
    : MetaM Expr := do
  withTraceNode `sat (fun _ => return "Compiling expr term") do
    mkAuxDecl cfg.exprDef cnfExpr (mkApp (mkConst ``CNF) (mkConst ``Nat))

  let certType := toTypeExpr LratCert

  withTraceNode `sat (fun _ => return "Compiling proof certificate term") do
    mkAuxDecl cfg.certDef (toExpr cert) certType

  let cnfExpr := mkConst cfg.exprDef
  let lratFormulaExpr := mkApp (mkConst ``BVDecide.LratFormula.ofCnf) cnfExpr
  let certExpr := mkConst cfg.certDef

  withTraceNode `sat (fun _ => return "Compiling reflection proof term") do
    let auxValue := mkApp2 (mkConst verifier) lratFormulaExpr certExpr
    mkAuxDecl cfg.reflectionDef auxValue (mkConst ``Bool)

  let nativeProof :=
    mkApp3
      (mkConst ``Lean.ofReduceBool)
      (mkConst cfg.reflectionDef)
      (toExpr true)
      (← mkEqRefl (toExpr true))
  return mkApp3 (mkConst unsat_of_verifier_eq_true) cnfExpr certExpr nativeProof

syntax (name := unsatDecide) "unsat_native_decide" : tactic

open Lean.Elab.Tactic in
elab_rules : tactic
  | `(tactic| unsat_native_decide) => do
    let cfg ← TacticContext.new (← mkTemp)
    liftMetaFinishingTactic fun g => do
      let target ← g.getType''
      if ! (← isDefEq target.getAppFn (mkConst ``CNF.unsat)) then
        throwError "The goal should be in the form (...).unsat"
      let args := target.getAppArgs
      if ! (← isDefEq args[0]! (mkConst ``Nat)) then
        throwError "CNF type should be Nat"
      let cnfExpr := args[1]!
      let t ← inferType cnfExpr
      let cnf ← unsafe evalExpr (CNF ℕ) t cnfExpr
      let res ← runExternal (BVDecide.LratFormula.ofCnf cnf) cfg.solver cfg.lratPath cfg.prevalidate cfg.timeout
      let cert := res.toOption.get!
      let proof ← LratCert.toReflectionProofCNF cert cfg cnfExpr ``verifyCert ``verifyCert_correct
      g.assign proof
