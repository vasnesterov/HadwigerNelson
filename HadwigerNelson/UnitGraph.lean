import HadwigerNelson.CompGraph
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic


def unitDistance (u v : ℂ) : Prop := ‖u - v‖ = 1

def planeColorable (n : ℕ) : Prop := ∃ f : ℂ → Fin n, ∀ u v : ℂ, (unitDistance u v) → f u ≠ f v

lemma neq_of_unit {u v : ℂ} (h : unitDistance u v) : u ≠ v := by
  by_contra heq
  rw [heq] at h
  simp [unitDistance] at h

structure UnitGraph.Edge (vertexes : List ℂ) where
  i : Fin vertexes.length
  j : Fin vertexes.length
  p : unitDistance vertexes[i] vertexes[j]

structure UnitGraph where
  vertexes : List ℂ
  edges : List <| UnitGraph.Edge vertexes

namespace UnitGraph

def emtpy (vertexes : List ℂ) : UnitGraph := ⟨vertexes, []⟩

-- def insert (g : UnitGraph) (edge : EdgeType g.vertexes) : UnitGraph := ⟨g.vertexes, edge :: g.edges⟩

def toCompGraph (g : UnitGraph) : CompGraph where
  nVertexes := g.vertexes.length
  edges := g.edges.map fun ⟨u, v, h⟩ => ⟨
    (u, v),
    by
      simp
      by_contra heq
      rw [heq] at h
      simp [Prod, unitDistance] at h
  ⟩

def mul (g : UnitGraph) (z : ℂ) (h_unit : ‖z‖ = 1) : UnitGraph where
  vertexes := g.vertexes.map (· * z)
  edges := g.edges.map fun ⟨i, j, p⟩ =>
  ⟨
    ⟨i.val, by rw [List.length_map _ _]; exact i.isLt⟩,
    ⟨j.val, by rw [List.length_map _ _]; exact j.isLt⟩, by
    simp only [unitDistance, Fin.getElem_fin, List.getElem_map] at *
    rwa [← sub_mul, norm_mul, h_unit, mul_one]
  ⟩

def add (g : UnitGraph) (z : ℂ) : UnitGraph where
  vertexes := g.vertexes.map (· + z)
  edges := g.edges.map fun ⟨i, j, p⟩ =>
  ⟨
    ⟨i.val, by rw [List.length_map _ _]; exact i.isLt⟩,
    ⟨j.val, by rw [List.length_map _ _]; exact j.isLt⟩, by
    simp [unitDistance, Fin.getElem_fin, List.getElem_map] at *
    assumption
  ⟩

def planeColorable_graph_Colorable {n : ℕ} (h_p_col : planeColorable n) (g : UnitGraph) :
    g.toCompGraph.toSimpleGraph.Colorable n := by
  obtain ⟨val, h_val⟩ := h_p_col
  simp [SimpleGraph.Colorable]
  apply Nonempty.intro
  let val' (v : Fin g.toCompGraph.nVertexes) : Fin n := val g.vertexes[v]
  apply SimpleGraph.Coloring.mk val'
  intro u v h_adj
  simp [val']
  simp [toCompGraph, CompGraph.toSimpleGraph] at h_adj
  obtain ⟨⟨⟨i, j, h_unit⟩, _, h_sym⟩, _⟩ := h_adj
  cases' h_sym with h_sym h_sym
  all_goals
    rw [← h_sym.1, ← h_sym.2]
  · exact h_val g.vertexes[i] g.vertexes[j] h_unit
  · intro h
    have := h_val g.vertexes[(i : ℕ)] g.vertexes[(j : ℕ)] h_unit
    rw [h] at this
    trivial

example : ¬ planeColorable 1 := by
  let g : UnitGraph := {
    vertexes := [0, 1]
    edges := [⟨⟨0, by decide⟩, ⟨1, by decide⟩, by simp [unitDistance]⟩]
  }
  intro h_p_col
  absurd planeColorable_graph_Colorable h_p_col g
  apply Noncolorable_from_unsat
  dsimp [g]
  apply LitToNat_equisat _
  clear h_p_col
  unsat_native_decide

example : ¬ planeColorable 2 := by
  let z : ℂ := 1/2 + Complex.I / 2 * √3
  let g : UnitGraph := {
    vertexes := [0, 1, z]
    edges := [
      ⟨⟨0, by decide⟩, ⟨1, by decide⟩, by simp [unitDistance]⟩,
      ⟨⟨0, by decide⟩, ⟨2, by decide⟩, by simp [unitDistance, Complex.abs, Complex.normSq, z]; field_simp; norm_num⟩,
      ⟨⟨1, by decide⟩, ⟨2, by decide⟩, by simp [unitDistance, Complex.abs, Complex.normSq, z]; field_simp; norm_num⟩,
    ]
  }
  intro h_p_col
  absurd planeColorable_graph_Colorable h_p_col g
  apply Noncolorable_from_unsat
  dsimp [g, toCompGraph, CompGraph.ColorablilityCNF]
  apply LitToNat_equisat _
  clear h_p_col
  unsat_native_decide

end UnitGraph
