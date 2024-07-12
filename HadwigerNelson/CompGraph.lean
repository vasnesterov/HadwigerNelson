/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import HadwigerNelson.UnsatDecide
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
# Computational Graphs

In this file we reduce the colorability of the finite graph to the satisfability of some CNF.

## Main declarations

* `CompGraph`: a computational structure for finite graphs without loops.
* `ColorablilityCNF`: CNF meaning that given graph is colorable in given number of colors.
* `Noncolorable_from_unsat`: if the CNF is unsatisfiable, then the graph is not colorable.
-/


/-- Structure to compute with graphs. It is inconvenient to use `SimpleGraph` for such purposes
because we want to store edges explicitly. -/
structure CompGraph where
  nVertexes : ℕ
  edges : List {x : (Fin nVertexes) × (Fin nVertexes) // x.1 ≠ x.2}

namespace CompGraph

def mkEdge {nVertexes : ℕ} (u v : Fin nVertexes) (h : u ≠ v := by decide) :
    {x : (Fin nVertexes) × (Fin nVertexes) // x.1 ≠ x.2} := ⟨(u, v), h⟩

def toSimpleGraph (g : CompGraph) : SimpleGraph (Fin g.nVertexes) :=
  SimpleGraph.fromEdgeSet (g.edges.map fun e => Sym2.mk e.val).toFinset

/-- Type representing literals which are used in standard CNF representing colorability of a
finite graph. -/
abbrev Lit (n : ℕ) (c : ℕ) := Fin n × Fin c

/-- CNF representing colorability of a finite graph `g` with `n` colors. The literal `(v, c)` means
"the vertex `v` has color `c`". In the CNF we have clauses of two types:
* `(v, 0) ∨ (v, 1) ∨ ... ∨ (v, n - 1)` for all `v` meaning that `v` must have at least one color.
* `¬(u, c) ∨ ¬(v, c)` for all colors `c` and edges `(u, v)` meaning that monochrome edges are
  forbidden.
-/
def ColorablilityCNF (g : CompGraph) (n : ℕ) : CNF <| Lit g.nVertexes n :=
  let vertexesCNF : CNF <| Lit g.nVertexes n :=
    List.finRange g.nVertexes |>.map fun v =>
    List.finRange n |>.map fun c => ((v, c), true)
  let edgesCNF : CNF <| Lit g.nVertexes n :=
    List.join <| g.edges.map fun ⟨(u, v), _⟩ =>
      (List.finRange n).map fun c => [((u, c), false), ((v, c), false)]
  vertexesCNF ++ edgesCNF

open CNF

/-- If `g` is `n`-colorable, then the corresponding CNF is satisfiable. The opposite is also true,
but we do not prove it. `Lit` suffix denotes underlying type of literals. -/
theorem sat_from_Colorable_Lit (g : CompGraph) {n : ℕ} (h_col : g.toSimpleGraph.Colorable n) :
    ∃ f : Lit g.nVertexes n → Bool, (ColorablilityCNF g n).sat f := by
  obtain ⟨col⟩ := h_col
  use fun (v, c) => col v == c
  simp only [sat, eval, List.all_eq_true]
  intro clause h_clause
  simp only [ColorablilityCNF, ne_eq, List.mem_append, List.mem_map, List.mem_finRange, true_and,
    List.mem_join, Subtype.exists, exists_and_right, Misc.Prod.exists] at h_clause
  cases' h_clause with h_clause_vertex h_clause_edge
  · obtain ⟨v, hv⟩ := h_clause_vertex
    rw [← hv]
    simp only [Clause.eval, List.any_eq_true, List.mem_map, List.mem_finRange, true_and,
      beq_iff_eq, exists_exists_eq_and, exists_eq']
  · obtain ⟨li, ⟨u, v, ⟨h_edge_neq, h_edge⟩, h_li⟩, h_clause⟩ := h_clause_edge
    rw [← h_li] at h_clause
    simp only [List.mem_map, List.mem_finRange, true_and] at h_clause
    obtain ⟨c, hc⟩ := h_clause
    rw [← hc]
    simp only [Clause.eval, List.any_cons, beq_false, List.any_nil, Bool.or_false, Bool.or_eq_true,
      Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    by_contra h
    push_neg at h
    have : col u = col v := by simp [h]
    absurd this
    apply SimpleGraph.Coloring.valid col
    simp only [toSimpleGraph, ne_eq, List.coe_toFinset, List.mem_map, Subtype.exists,
      exists_and_right, Misc.Prod.exists, SimpleGraph.fromEdgeSet_adj, Set.mem_setOf_eq, Sym2.eq,
      Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    constructor
    · use u; use v
      tauto
    · assumption

/-- Contraposition to the `sat_from_Colorable`. `Lit` suffix denotes underlying type of literals. -/
theorem Noncolorable_from_unsat_Lit {g : CompGraph} {n : ℕ}
    (h_unsat : (CompGraph.ColorablilityCNF g n).unsat) : ¬ g.toSimpleGraph.Colorable n := by
  by_contra h_col
  obtain ⟨f, _⟩ := sat_from_Colorable_Lit g h_col
  simp_all [sat, h_unsat f]

-- for debug
instance (n : ℕ) (c : ℕ) (x : CNF <| Lit n c) : Decidable x.unsat :=
  inferInstanceAs <| Decidable (∀ f, eval f x = false)

/-- We lift `Lit` to `ℕ` because LeanSAT API uses `CNF ℕ`. -/
def liftLit {n c : ℕ} : Lit n c → ℕ := fun (u, i) => u * c + i

/-- We lift `Lit` to `ℕ` because LeanSAT API uses `CNF ℕ`. -/
def liftLitCNF {n c : ℕ} (cnf : CNF <| Lit n c) : CNF ℕ :=
  cnf.map (fun cl => cl.map fun (p, b) => (liftLit p, b))

/-- Lifting preserves unsatisfability. In fact the lifted CNF is equisatisfiable with the original
one, but we prove this only in one direction. -/
theorem unsat_of_liftLitCNF_unsat {n c : ℕ} {cnf : CNF <| Lit n c}
    (h_unsat : (liftLitCNF cnf).unsat) (h_n_pos : n > 0 := by decide) (h_c_pos : c > 0 := by decide)
    : cnf.unsat := by
  have : Inhabited (Lit n c) := ⟨(⟨0, h_n_pos⟩, ⟨0, h_c_pos⟩)⟩
  apply unsat_of_liftToNat_unsat _ h_unsat
  let liftLitInv : ℕ → Lit n c := fun x =>
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
  apply Function.LeftInverse.injective (g := liftLitInv)
  intro (v, i)
  simp only [ge_iff_le, liftLit, liftLitInv]
  have hv : ((v : ℕ) * c + (i : ℕ)) / c = v := by
    rw [mul_comm, Nat.mul_add_div h_c_pos, (Nat.div_eq_zero_iff h_c_pos).mpr i.isLt, add_zero]
  have hi : ((v : ℕ) * c + (i : ℕ)) % c = i := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt]
  split_ifs with h
  · exfalso
    absurd h
    rw [not_le]
    apply Nat.lt_mul_of_div_lt (hc := h_c_pos)
    rw [hv]
    exact v.isLt
  · conv =>
      lhs
      congr
      all_goals lhs
      · rw [hv]
      · rw [hi]

/-- If the corresponding CNF is UNSAT, then the graph is not colorable. -/
theorem Noncolorable_from_unsat (g : CompGraph) {n : ℕ}
    (h_unsat : liftLitCNF (CompGraph.ColorablilityCNF g n) |>.unsat)
    (h_n_pos : n > 0 := by decide) (h_v_pos : g.nVertexes > 0 := by decide) :
    ¬ g.toSimpleGraph.Colorable n := by
  have h_unsat := unsat_of_liftLitCNF_unsat h_unsat h_v_pos h_n_pos
  apply Noncolorable_from_unsat_Lit h_unsat

--- examples ---

private def triangle : CompGraph where
  nVertexes := 3
  edges := [mkEdge 0 1, mkEdge 1 2, mkEdge 2 0]

-- #eval triangle.ColorablilityCNF 3
-- #eval liftLitCNF (triangle.ColorablilityCNF 3)

example : ¬ triangle.toSimpleGraph.Colorable 2 := by
  apply Noncolorable_from_unsat _
  unsat_decide

/-- Complete graph with `n` vertexes. -/
private def complete (n : ℕ) : CompGraph where
  nVertexes := n
  edges := List.join <| (List.finRange n).map fun i =>
    (List.finRange n).filterMap fun j =>
      if h : i ≠ j then
        mkEdge i j h
      else
        none

-- #eval ((CompGraph.complete 20).ColorablilityCNF 10).length

example : ¬ (CompGraph.complete 10).toSimpleGraph.Colorable 8 := by
  apply Noncolorable_from_unsat _
  unsat_decide

end CompGraph
