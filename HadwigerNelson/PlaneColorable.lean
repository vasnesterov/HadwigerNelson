import Mathlib.Analysis.Complex.Basic

open Complex ComplexConjugate Topology Filter

def unitDistance (u v : ℂ) : Prop := ‖u - v‖ = 1

def planeColorable (n : ℕ) : Prop := ∃ f : ℂ → Fin n, ∀ u v : ℂ, (unitDistance u v) → f u ≠ f v

lemma neq_of_unit {u v : ℂ} (h : unitDistance u v) : u ≠ v := by
  by_contra heq
  rw [heq] at h
  simp [unitDistance] at h
