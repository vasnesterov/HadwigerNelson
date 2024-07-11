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

@[simp]
lemma factor_sqrt (x : ℕ) :
  let factored := factorSquares x;
  (√x : ℝ) = factored.sqrt * Real.sqrt factored.free := by
  if h : x = 0 then
    rw [h]
    simp [factorSquares]
  else
    rw [Real.sqrt_eq_iff_sq_eq]
    · ring_nf
      rw [Real.sq_sqrt (Nat.cast_nonneg' (factorSquares x).free)]
      rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.cast_inj]
      have := (factorSquares x).correct_prod.symm
      ring_nf at this
      assumption
    · apply Nat.cast_nonneg'
    · sorry

example : (√(8 : ℕ) : ℝ) = 2 * √2 := by
  rw [factor_sqrt]

  -- rw [sqrt_mul_sqrt 8]


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


-- /-- The `norm_num` extension which identifies expressions of the form `a + b`,
-- such that `norm_num` successfully recognises both `a` and `b`. -/
-- @[norm_num Real.sqrt _ * Real.sqrt _] def evalSqrtMulSqrt : NormNumExt where eval {u α} e := do
--   let .app (.app (f : Q($α → $α → $α)) (a : Q($α))) (b : Q($α)) ← whnfR e | failure
--   let ra ← derive a; let rb ← derive b
--   match ra, rb with
--   | .isBool .., _ | _, .isBool .. => failure
--   | .isNat _ .., .isNat _ .. | .isNat _ .., .isNegNat _ .. | .isNat _ .., .isRat _ ..
--   | .isNegNat _ .., .isNat _ .. | .isNegNat _ .., .isNegNat _ .. | .isNegNat _ .., .isRat _ ..
--   | .isRat _ .., .isNat _ .. | .isRat _ .., .isNegNat _ .. | .isRat _ .., .isRat _ .. =>
--     guard <|← withNewMCtxDepth <| isDefEq f q(HAdd.hAdd (α := $α))
--   let rec
--   /-- Main part of `evalAdd`. -/
--   core : Option (Result e) := do
--     let rec intArm (rα : Q(Ring $α)) := do
--       haveI' : $e =Q $a + $b := ⟨⟩
--       let ⟨za, na, pa⟩ ← ra.toInt _; let ⟨zb, nb, pb⟩ ← rb.toInt _
--       haveI' : $f =Q HAdd.hAdd := ⟨⟩
--       let zc := za + zb
--       have c := mkRawIntLit zc
--       haveI' : Int.add $na $nb =Q $c := ⟨⟩
--       return .isInt rα c zc q(isInt_add (f := $f) (.refl $f) $pa $pb (.refl $c))
--     let rec ratArm (dα : Q(DivisionRing $α)) : Option (Result _) := do
--       haveI' : $e =Q $a + $b := ⟨⟩
--       haveI' : $f =Q HAdd.hAdd := ⟨⟩
--       let ⟨qa, na, da, pa⟩ ← ra.toRat' dα; let ⟨qb, nb, db, pb⟩ ← rb.toRat' dα
--       let qc := qa + qb
--       let dd := qa.den * qb.den
--       let k := dd / qc.den
--       have t1 : Q(ℤ) := mkRawIntLit (k * qc.num)
--       have t2 : Q(ℕ) := mkRawNatLit dd
--       have nc : Q(ℤ) := mkRawIntLit qc.num
--       have dc : Q(ℕ) := mkRawNatLit qc.den
--       have k : Q(ℕ) := mkRawNatLit k
--       let r1 : Q(Int.add (Int.mul $na $db) (Int.mul $nb $da) = Int.mul $k $nc) :=
--         (q(Eq.refl $t1) : Expr)
--       let r2 : Q(Nat.mul $da $db = Nat.mul $k $dc) := (q(Eq.refl $t2) : Expr)
--       return .isRat' dα qc nc dc q(isRat_add (f := $f) (.refl $f) $pa $pb $r1 $r2)
--     match ra, rb with
--     | .isBool .., _ | _, .isBool .. => failure
--     | .isRat dα .., _ | _, .isRat dα .. => ratArm dα
--     | .isNegNat rα .., _ | _, .isNegNat rα .. => intArm rα
--     | .isNat _ na pa, .isNat sα nb pb =>
--       haveI' : $e =Q $a + $b := ⟨⟩
--       haveI' : $f =Q HAdd.hAdd := ⟨⟩
--       assumeInstancesCommute
--       have c : Q(ℕ) := mkRawNatLit (na.natLit! + nb.natLit!)
--       haveI' : Nat.add $na $nb =Q $c := ⟨⟩
--       return .isNat sα c q(isNat_add (f := $f) (.refl $f) $pa $pb (.refl $c))
--   core

def a : ℝ := 1

example : (a + a) - ((a - 3*a)^2 - a / a^5) = -1 := by unfold a; norm_num

example : √3 * √3 = 3 := by norm_num

example : √2 * √3 = √6 := by norm_num


-- example : 3 * (1 - √2) = 3 - 3 * √2 := by
--   rw [Real.sqrt_eq_rpow]
--   norm_num

-- example : (1 + √2) * (1 - √2) = 1 := by norm_num
