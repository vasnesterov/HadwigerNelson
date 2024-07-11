import HadwigerNelson.UnitGraph
import HadwigerNelson.FactorSquares
import Qq


set_option autoImplicit true

namespace Mathlib
open Lean hiding Rat mkRat
open Meta

namespace Meta.NormNum
open Qq

#eval (factorSquares 1234).sqrt

example : (factorSquares 7).sqrt = 1 := by rfl

#reduce (factorSquares 8).free.val

def complexFunction (x : ℕ) : ℕ := x^2

example : complexFunction 2 = 4 := by
  reduce

lemma factor_sqrt (x : ℕ) {y z : ℕ}
    (hy : y = (factorSquares x).sqrt := by rfl) (hz : z = (factorSquares x).free := by rfl) :
  (√x : ℝ) = y * √z := by
  sorry
  -- if h : x = 0 then
  --   rw [h]
  --   simp [factorSquares]
  -- else
  --   rw [Real.sqrt_eq_iff_sq_eq]
  --   · ring_nf
  --     rw [Real.sq_sqrt (Nat.cast_nonneg' (factorSquares x).free)]
  --     rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.cast_inj]
  --     have := (factorSquares x).correct_prod.symm
  --     ring_nf at this
  --     assumption
  --   · apply Nat.cast_nonneg'
  --   · sorry

lemma factor_sqrt_fast (x : ℕ) :
  let factored := factorSquaresFast' x;
  (√x : ℝ) = factored.1 * √factored.2 := by
  sorry

example : (factorSquares 4).free.val = 1 := by
  reduce

set_option maxRecDepth 1000 in
example : (√(8 : ℕ) : ℝ) = 2 * √2 := by
  rw [factor_sqrt]
  repeat (conv in factorSquares _ =>
    reduce)
  dsimp only
  -- simp [factorSquares, factorSquaresImp, factorSquaresStep]


  -- rw [sqrt_mul_sqrt 8]

#print factorial


#help tactic
---------------------------------------------------------------------------------------------

theorem sqrt_pow_even {x : ℝ} {n : ℕ} (h : 0 ≤ x) : √x ^ (n*2) = x^n := by
  rwa [pow_mul', Real.sq_sqrt]

@[simp]
theorem sqrt_pow {x : ℝ} {n : ℕ} (h_nn : 0 ≤ x) : √x ^ n = x^(n / 2) * √x^(n % 2) := by
  if h : Even n then
    obtain ⟨k, hk⟩ := h
    rw [hk]
    ring_nf
    simp only [Nat.mul_mod_left, pow_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_div_cancel_right₀, one_mul]
    exact sqrt_pow_even h_nn
  else
    have h := Nat.odd_iff_not_even.mpr h
    obtain ⟨k, hk⟩ := h
    rw [hk]
    ring_nf
    simp only [Nat.add_mul_mod_self_right, Nat.reduceMod, pow_one, mul_eq_mul_left_iff]
    left
    rw [show (1 + k * 2) / 2 = k by omega]
    exact sqrt_pow_even h_nn

theorem I_pow_even {n : ℕ} : Complex.I ^ (n*2) = (-1)^n := by
  rw [pow_mul', Complex.I_sq]

@[simp]
theorem I_pow {n : ℕ} : Complex.I^n = (-1)^(n / 2) * Complex.I^(n % 2) := by
  if h : Even n then
    obtain ⟨k, hk⟩ := h
    rw [hk]
    ring_nf
    simp only [Nat.mul_mod_left, pow_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_div_cancel_right₀, one_mul]
    exact I_pow_even
  else
    have h := Nat.odd_iff_not_even.mpr h
    obtain ⟨k, hk⟩ := h
    rw [hk]
    ring_nf
    simp only [Nat.add_mul_mod_self_right, Nat.reduceMod, pow_one, mul_eq_mul_left_iff]
    left
    rw [show (1 + k * 2) / 2 = k by omega]
    exact I_pow_even

----------------------------------------------------------------------------------------------------

open Lean Meta Elab Tactic

#check Lean.Meta.Rewrite.Config


def a : ℝ := 1

example : (a + a) - ((a - 3*a)^2 - a / a^5) = -1 := by unfold a; norm_num

example : √3 * √3 = 3 := by norm_num

example : √2 * √3 = √6 := by
  rw [← Real.sqrt_mul (by simp)]
  norm_num


-- example : 3 * (1 - √2) = 3 - 3 * √2 := by
--   rw [Real.sqrt_eq_rpow]
--   norm_num

-- example : (1 + √2) * (1 - √2) = 1 := by norm_num
