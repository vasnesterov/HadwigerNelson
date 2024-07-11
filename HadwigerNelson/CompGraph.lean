import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import LeanSAT

structure CompGraph where
  nVertexes : ℕ
  edges : List {x : (Fin nVertexes) × (Fin nVertexes) // x.1 ≠ x.2}

abbrev Lit (n : ℕ) (c : ℕ) := Fin n × Fin c

def CompGraph.ColorablilityCNF (g : CompGraph) (n : ℕ) : CNF <| Lit g.nVertexes n :=
  let vertexesCNF : CNF <| Lit g.nVertexes n :=
    List.finRange g.nVertexes |>.map fun v =>
    List.finRange n |>.map fun c => ((v, c), true)
  let edgesCNF : CNF <| Lit g.nVertexes n :=
    List.join <| g.edges.map fun ⟨(u, v), _⟩ =>
      (List.finRange n).map fun c => [((u, c), false), ((v, c), false)]
  vertexesCNF ++ edgesCNF

def mkEdge {nVertexes : ℕ} (u v : Fin nVertexes) (h : u ≠ v := by decide) :
    {x : (Fin nVertexes) × (Fin nVertexes) // x.1 ≠ x.2} := ⟨(u, v), h⟩

def CompGraph.toSimpleGraph (g : CompGraph) : SimpleGraph (Fin g.nVertexes) :=
  SimpleGraph.fromEdgeSet (g.edges.map fun e => Sym2.mk e.val).toFinset

theorem sat_from_Colorable (g : CompGraph) {n : ℕ} (h_col : g.toSimpleGraph.Colorable n) :
    ∃ f : Lit g.nVertexes n → Bool, (CompGraph.ColorablilityCNF g n).sat f := by
  obtain ⟨col⟩ := h_col
  use fun (v, c) => col v == c
  simp [CNF.sat, CNF.eval]
  intro clause h_clause
  simp [CompGraph.ColorablilityCNF] at h_clause
  cases' h_clause with h_clause_vertex h_clause_edge
  · obtain ⟨v, hv⟩ := h_clause_vertex
    rw [← hv]
    simp [CNF.Clause.eval]
  · obtain ⟨li, ⟨u, v, ⟨h_edge_neq, h_edge⟩, h_li⟩, h_clause⟩ := h_clause_edge
    rw [← h_li] at h_clause
    simp at h_clause
    obtain ⟨c, hc⟩ := h_clause
    rw [← hc]
    simp [CNF.Clause.eval]
    by_contra h
    push_neg at h
    have : col u = col v := by simp [h]
    absurd this
    apply SimpleGraph.Coloring.valid col
    simp [CompGraph.toSimpleGraph]
    constructor
    · use u; use v
      tauto
    · assumption

instance (n : ℕ) (c : ℕ) (x : CNF <| Lit n c) : Decidable x.unsat :=
  inferInstanceAs <| Decidable (∀ f, CNF.eval f x = false)

theorem Noncolorable_from_unsat (g : CompGraph) {n : ℕ}
    (h_unsat : (CompGraph.ColorablilityCNF g n).unsat) : ¬ g.toSimpleGraph.Colorable n := by
  by_contra h_col
  obtain ⟨f, _⟩ := sat_from_Colorable g h_col
  simp_all [CNF.sat, h_unsat f]


def triangle : CompGraph where
  nVertexes := 3
  edges := [mkEdge 0 1, mkEdge 1 2, mkEdge 2 0]

-- #eval triangle.ColorablilityCNF 3

def CNF.liftToNat {α : Type} (emb : α → ℕ) (cnf : CNF α) : CNF ℕ :=
  cnf.map (fun cl => cl.map fun (a, b) => (emb a, b))

theorem lift_equisat {α : Type} [Fintype α] [Inhabited α] {emb : α → ℕ} {cnf : CNF α}
    (h_inj : emb.Injective) (h_unsat : (CNF.liftToNat emb cnf).unsat) : cnf.unsat := by
  intro assign
  simp_all [CNF.unsat, CNF.eval, CNF.liftToNat, List.all_eq]
  let embInv := Function.invFun emb
  have h_li : Function.LeftInverse embInv emb := by exact Function.leftInverse_invFun h_inj
  specialize h_unsat fun x => assign (embInv x)
  obtain ⟨cl, h_cl_in, h_cl_eval⟩ := h_unsat
  use cl
  constructor
  · assumption
  simp [CNF.Clause.eval] at *
  simp [List.any_map] at h_cl_eval
  simp [List.any_eq] at *
  intro a ha
  specialize h_cl_eval a
  simp [h_li a] at h_cl_eval
  exact h_cl_eval ha

def LitToNat {n c : ℕ} : Lit n c → ℕ := fun (u, i) => u * c + i

def liftLitCNF {n c : ℕ} (cnf : CNF <| Lit n c) : CNF ℕ :=
  cnf.map (fun cl => cl.map fun (p, b) => (LitToNat p, b))

theorem LitToNat_equisat {n c : ℕ} (cnf : CNF <| Lit n c)
    (h_n_pos : n > 0 := by decide) (h_c_pos : c > 0 := by decide)
    : (liftLitCNF cnf).unsat → cnf.unsat := by
  have : Inhabited (Lit n c) := ⟨(⟨0, h_n_pos⟩, ⟨0, h_c_pos⟩)⟩
  apply lift_equisat
  let NatToLit : ℕ → Lit n c := fun x =>
    if h : x >= n * c then
      default
    else
      let v : Fin n := Fin.mk (x / c) (by
        apply Nat.div_lt_of_lt_mul
        rw [mul_comm]
        exact Nat.gt_of_not_le h
      )
      let i : Fin c := Fin.mk (x % c) (Nat.mod_lt _ h_c_pos)
      (v, i)
  apply Function.LeftInverse.injective (g := NatToLit)
  intro (v, i)
  simp [NatToLit, LitToNat]
  have hv : ((v : ℕ) * c + (i : ℕ)) / c = v := by
    rw [mul_comm, Nat.mul_add_div h_c_pos, (Nat.div_eq_zero_iff h_c_pos).mpr i.isLt, add_zero]
  have hi : ((v : ℕ) * c + (i : ℕ)) % c = i := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt]
  split_ifs with h
  · exfalso
    absurd h
    simp
    apply Nat.lt_mul_of_div_lt (hc := h_c_pos)
    rw [hv]
    exact v.isLt
  · conv =>
      lhs
      congr
      all_goals lhs
      · rw [hv]
      · rw [hi]

-- #eval liftLitCNF (triangle.ColorablilityCNF 3)

syntax (name := unsatDecide) "unsat_native_decide" : tactic

open Lean.Elab.Tactic
elab_rules : tactic
  | `(tactic| unsat_native_decide) => do
    let cfg ← BVDecide.TacticContext.new (← BVDecide.mkTemp)
    liftMetaFinishingTactic fun g => do
      let target ← g.getType''
      if ! (← Lean.Meta.isDefEq target.getAppFn (Lean.mkConst ``CNF.unsat)) then
        throwError "The goal should be in the form (...).unsat"
      let args := target.getAppArgs
      if ! (← Lean.Meta.isDefEq args[0]! (Lean.mkConst ``Nat)) then
        throwError "CNF type should be Nat"
      let cnfExpr := args[1]!
      let t ← Lean.Meta.inferType cnfExpr
      let cnf ← unsafe Lean.Meta.evalExpr (CNF ℕ) t cnfExpr
      let res ← BVDecide.runExternal (BVDecide.LratFormula.ofCnf cnf) cfg.solver cfg.lratPath cfg.prevalidate cfg.timeout
      let cert := res.toOption.get!
      let proof ← BVDecide.LratCert.toReflectionProofCNF cert cfg cnfExpr ``BVDecide.verifyCert ``BVDecide.verifyCert_correct
      g.assign proof

def CompGraph.complete (n : ℕ) : CompGraph where
  nVertexes := n
  edges := List.join <| (List.finRange n).map fun i =>
    (List.finRange n).filterMap fun j =>
      if h : i ≠ j then
        mkEdge i j h
      else
        none

theorem lol : ¬ triangle.toSimpleGraph.Colorable 2 := by
  apply Noncolorable_from_unsat
  -- decide -- slow
  apply LitToNat_equisat _
  unsat_native_decide


-- #eval ((CompGraph.complete 20).ColorablilityCNF 10).length

theorem lool : ¬ (CompGraph.complete 10).toSimpleGraph.Colorable 8 := by
  apply Noncolorable_from_unsat
  -- decide -- slow
  apply LitToNat_equisat _
  unsat_native_decide
