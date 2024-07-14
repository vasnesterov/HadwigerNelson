/-
Copyright (c) 2024 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Tactic.Qify
import Mathlib.Util.SleepHeartbeats
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Star
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Factoring squares

In this file we implement a verified procedure of factoring squares, i.e. decomposing the natural
number `x` as `y * z^2` where `y` is square-free.

## Main declarations

* `factorSquares`: factors `x = y * z^2` where `y` is square-free.
* `factor_sqrt` tactic replaces `√x` with `z * √y` where `y` is square-free.

## Implementation notes

Unfortunately, we was not able to use the proved correctness of the procedure in the main proof,
because reducing WF-based function `factorSquares` is extremely inefficient.
-/


namespace FactorSquares

structure FactorSquaresResult (x : ℕ) where
  free : {x : ℕ // Squarefree x ∨ x = 0}
  sqrt : ℕ
  correct_prod : x = sqrt * sqrt * free

structure FactorSquaresState (x : ℕ) where
  free : ℕ
  sqrt : ℕ
  free_nz : free ≠ 0
  cur_factor : ℕ
  cur_factor_pos : 2 ≤ cur_factor
  correct_prod : x = sqrt * sqrt * free
  correct_free : ∀ f : ℕ, (2 ≤ f) → (f < cur_factor) → (¬ (f * f : ℕ) ∣ free)

def factorSquaresStep {x : ℕ} (s : FactorSquaresState x) : FactorSquaresState x :=
  if hdiv : (s.cur_factor * s.cur_factor : ℕ) ∣ s.free then
    {
      free := s.free / (s.cur_factor * s.cur_factor)
      sqrt := s.sqrt * s.cur_factor
      free_nz := by
        have cur_factor_pos' : 0 < (s.cur_factor * s.cur_factor : ℕ) := by
          simp only [mul_self_pos, ne_eq, Nat.cast_eq_zero]
          have := s.cur_factor_pos
          omega
        obtain ⟨c, hc⟩ := hdiv
        rw [hc]
        field_simp [cur_factor_pos']
        intro hc_eq_0
        apply s.free_nz
        rw [hc]
        field_simp [hc_eq_0]
      cur_factor := s.cur_factor
      cur_factor_pos := s.cur_factor_pos
      correct_prod := by
        have correct_prod := s.correct_prod
        have := s.cur_factor_pos
        generalize s.free = a at *
        generalize s.sqrt = b at *
        generalize s.cur_factor = c at *
        rw [correct_prod]
        obtain ⟨d, hd⟩ := hdiv
        rw [hd]
        qify; field_simp; ring
      correct_free := by
        intro f f_lb f_ub
        have correct_free := s.correct_free f f_lb f_ub
        have := s.cur_factor_pos
        contrapose! correct_free
        -- this should be a separate lemma `dvd_of_mul_left_dvd`
        obtain ⟨c, hc⟩ := correct_free
        use c * (s.cur_factor ^ 2)
        qify at *; field_simp at *; rw [hc]; ring_nf
    }
  else
    { s with
      cur_factor := s.cur_factor + 1
      cur_factor_pos := Nat.le_succ_of_le s.cur_factor_pos
      correct_free := by
        intro f f_lb f_ub
        if h : f < s.cur_factor then
          exact s.correct_free f f_lb h
        else
          rwa [show f = s.cur_factor by omega]
    }

@[semireducible]
def factorSquaresImp {x : ℕ} (s : FactorSquaresState x) : FactorSquaresResult x :=
  if h : s.free < s.cur_factor then
    {
      free := ⟨s.free, by
        left
        intro f f_dvd
        simp only [Nat.isUnit_iff]
        have f_le : f ≤ s.free := by
          trans f * f
          · apply Nat.le_mul_self
          · apply Nat.le_of_dvd <| Nat.zero_lt_of_ne_zero s.free_nz
            assumption
        by_contra f_neq_1
        apply (s.correct_free) f
        · by_contra! f_lt_2
          have f_lt_1 : f < 1 := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ f_lt_2) f_neq_1
          have f_eq_0 : f = 0 := by simp_all only [ne_eq, Nat.lt_one_iff]
          rw [f_eq_0] at f_dvd
          simp only [mul_zero, zero_dvd_iff, Int.natAbs_eq_zero] at f_dvd
          exact s.free_nz f_dvd
        · apply lt_of_le_of_lt
          · exact f_le
          · assumption
        · assumption
      ⟩
      sqrt := s.sqrt
      correct_prod := s.correct_prod
    }
  else
    factorSquaresImp <| factorSquaresStep s
termination_by (s.free + 1 - s.cur_factor)
decreasing_by
  simp [factorSquaresStep]
  split_ifs with h_if <;> simp_wf
  · have : (s.free / (↑s.cur_factor * ↑s.cur_factor)) < s.free := by
      apply Nat.div_lt_self <| Nat.zero_lt_of_ne_zero s.free_nz
      · simp only [Int.natAbs_mul, Int.natAbs_ofNat, one_lt_mul_self_iff]
        have := s.cur_factor_pos
        linarith
    omega
  · omega

def factorSquares (x : ℕ) : FactorSquaresResult x :=
  if h_nz : x = 0 then
    {
      free := ⟨0, by right; rfl⟩
      sqrt := 0
      correct_prod := by simp [h_nz]
    }
  else
    let s : FactorSquaresState x := {
      free := x
      sqrt := 1
      free_nz := h_nz
      cur_factor := 2
      cur_factor_pos := by rfl
      correct_prod := by simp
      correct_free := by
        intro f f_lb f_ub
        omega
    }
    factorSquaresImp s

syntax "factor_sqrt_aux" : conv

open Lean Meta Elab Tactic Conv Qq in
/-- Conversion mode tactic that replaces `x` with `z^2 * y` where `y` is square-free. -/
elab_rules : conv
  | `(conv| factor_sqrt_aux) => do
    let num ← unsafe evalExpr ℕ (mkConst ``Nat) (← getLhs).getAppArgs[1]!
    let ⟨⟨free, _⟩, sqrt, _⟩ := factorSquares num
    let freeExpr : Q(ℕ) := toExpr free
    let sqrtExpr : Q(ℕ) := toExpr sqrt
    changeLhs <|← mkAppM' (← mkAppOptM ``Nat.cast #[q(ℝ)]) #[q($sqrtExpr^2 * $freeExpr)]

/-- Replaces `√x` with `z * √y` where `y` is square-free and `z` is a square. -/
syntax "factor_sqrt" : tactic
macro_rules
| `(tactic| factor_sqrt) =>
    `(tactic|
      (repeat conv in Real.sqrt (OfNat.ofNat _) => congr; factor_sqrt_aux);
      (repeat rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul, Real.sqrt_sq]) <;> norm_num
    )

example : √8 = 2 * √2 := by
  factor_sqrt

open Lean Meta

theorem sqrt_reduce (nsqrt n' : Nat) : √(Nat.cast (nsqrt ^ 2 * n')) = nsqrt * √n' := by
  simp

simproc reduceSqrt (Real.sqrt _) := fun e => do
  let some (n, Rty) ← getOfNatValue? e.appArg! ``Real | return .continue
  if n == 0 || n == 1 || Squarefree n then return .continue
  let mut nsqrt := 1
  let mut n' := 1
  let mut n'' := n
  for p in Nat.factors n do
    let mut multiplicity := 0
    while n'' % p == 0 do
      n'' := n'' / p
      multiplicity := multiplicity + 1
    nsqrt := nsqrt * p ^ (multiplicity / 2)
    n' := n' * p ^ (multiplicity % 2)
  -- now `n'` is squarefree and `n = nsqrt^2 * n'`.
  -- pf1 is `OfNat.ofNat n = Nat.cast n`
  let pf1 ← mkEqSymm (← mkAppOptM ``Nat.cast_eq_ofNat #[Rty, toExpr n, none, none])
  -- pf2 is `√(OfNat.ofNat n) = √(Nat.cast n)`
  let pf2 ← mkCongrArg (.const ``Real.sqrt []) pf1
  -- pf3 is `√(Nat.cast (nsqrt ^ 2 * n')) = nsqrt * √n'`
  let pf3 ← mkAppM ``sqrt_reduce #[toExpr nsqrt, toExpr n']
  -- pf4 is `√(OfNat.ofNat n) = nsqrt * √n'`
  let pf4 ← mkEqTrans pf2 pf3
  let some (_, _, rhs) := (← inferType pf4).eq? | return .continue -- should not fail
  return .visit { expr := rhs, proof? := pf4 }

example : √12 = 2 * √3 := by simp only [reduceSqrt, Nat.cast_ofNat]
