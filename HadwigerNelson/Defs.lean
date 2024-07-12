/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Complex.Basic

/-!
# Basic definitions

* `unitDistance`: predicate meaning that two points are at an unit distance from each other.
* `planeColorable n`: proposition meaning that one can color the plane in `n` colors such that ends
of any unit segment will not have same color.
-/

open Complex ComplexConjugate Topology Filter

def unitDistance (u v : ℂ) : Prop := ‖u - v‖ = 1

def planeColorable (n : ℕ) : Prop := ∃ f : ℂ → Fin n, ∀ u v : ℂ, (unitDistance u v) → f u ≠ f v

lemma neq_of_unit {u v : ℂ} (h : unitDistance u v) : u ≠ v := by
  by_contra heq
  rw [heq] at h
  simp [unitDistance] at h
