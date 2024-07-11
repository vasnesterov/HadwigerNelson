import HadwigerNelson.UnitGraph
import Qq

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

noncomputable def theta (i : ℕ) : ℂ where
  re := (2*i - 1) / (2*i)
  im := 1 / (2*i) * √(4*i - 1)

noncomputable def θ' : ℂ := ⟨(1/6) * √33, (1/6) * √3⟩
noncomputable def θ'_inv : ℂ := ⟨(1/6) * √33, - (1/6) * √3⟩

syntax "theta_calc" : tactic
macro_rules
| `(tactic| theta_calc) =>
    `(tactic| simp [unitDistance, theta, θ', θ'_inv, Complex.abs, Complex.normSq]; repeat (fail_if_no_progress (ring_nf; norm_num)))

example : ‖theta 42‖ = 1 := by theta_calc

open Qq Lean

def kekV : List Expr := Id.run do
  let mut ans : List Expr := []
  for j in [:2] do
    let jj : Q(ℕ) := toExpr j
    ans := q((theta 1)^$jj) :: ans
  return q(0 : ℂ) :: ans

def V_31 : List Expr := Id.run do
  let mut ans : List Expr := []
  for j in [:6] do
    for k in [:5] do
      let jj : Q(ℕ) := toExpr j
      let kk : Q(ℕ) := toExpr k
      ans := q((theta 1)^$jj * θ'_inv * θ'^$kk) :: ans
  return q(0 : ℂ) :: ans

def V_ex : List Expr := [q(0 : ℂ), q(1 : ℂ)]

example : unitDistance 0 1 := by theta_calc

lemma kqu (u v : ℂ) (h : (u - v).re^2 + (u - v).im^2 = 1) : unitDistance u v := by
  simp only [unitDistance, Complex.norm_eq_abs, Complex.abs, Complex.normSq,
    MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, AbsoluteValue.coe_mk, MulHom.coe_mk, Real.sqrt_eq_one]
  simp at h

@[simp]
lemma sub_re (u v : ℂ) : (u - v).re = u.re - v.re := by rfl

@[simp]
lemma sub_im (u v : ℂ) : (u - v).im = u.im - v.im := by rfl

@[simp]
lemma kek_sub (u v : ℂ) : u - v = ⟨u.re - v.re, u.im - v.im⟩ := by rfl

lemma kek_mul (a b c d : ℝ) : (⟨a, b⟩ : ℂ) * (⟨c, d⟩ : ℂ) = ⟨a * c - b * d, a * d + b * c⟩ := by rfl

set_option trace.profiler true

example : unitDistance ((theta 1)^6) (theta 1) := by
  theta_calc

example : unitDistance ((theta 1)^6) (theta 1) := by
  unfold unitDistance theta
  simp only [Nat.cast_one, mul_one, one_div, pow_succ, pow_zero, one_mul, kek_sub, Complex.mul_re,
    Complex.mul_im, Complex.norm_eq_abs]
  norm_num
  ring_nf
  norm_num
  simp [Complex.abs]
  norm_num
  ring_nf
  norm_num

example : (theta 1)^6 = 1 := by
  theta_calc
  unfold theta
  ring_nf
  norm_num [← Complex.ofReal_pow]
  ring_nf
  norm_num [← Complex.ofReal_pow]

example : (1/2 + Complex.I)^2 = -3/4 + Complex.I := by
  ring_nf
  simp
  ring_nf

example : (1/2 + Complex.I)^3 = -11/8 - 1/4 * Complex.I := by
  ring_nf
  norm_num
  ring_nf

example : unitDistance
    ( (theta 1)^3 * θ'^3 )
    ( (theta 1)^2 * θ'^3 ) := by
  -- theta_calc
  -- unfold unitDistance theta θ' Complex.abs
  simp only [unitDistance, theta, θ', θ'_inv]--, Complex.abs, Complex.normSq]
  conv =>
    lhs; congr
    ring_nf
    norm_num
    ring_nf
    norm_num
    ring_nf
  -- -- simp [Complex.add_re]
  -- ring_nf
  -- norm_num [← Complex.ofReal_pow]
  -- ring_nf
  -- norm_num [← Complex.ofReal_pow]

#check UnitGraph.mk

def aaux (li : List Expr) (type : Expr) : MetaM Expr := do match li with
| .nil => return ← Meta.mkAppOptM ``List.nil #[type]
| .cons head tail => return ← Meta.mkAppM ``List.cons #[head, (← aaux tail type)]

-- def aaux_inv (e : Expr) : MetaM <| List Expr :=
--   if e.isAppOf ``List.nil then

#check UnitGraph.Edge.mk

def UnitGraph.ofVertexes (vertexes : List Expr) : MetaM <| Expr := do
  let vertexesExpr : Expr := ← aaux vertexes q(ℂ)
  let mut edges : List Expr := []

  for (u, i) in vertexes.zip (List.finRange vertexes.length) do
    for (v, j) in vertexes.zip (List.finRange vertexes.length) do
      if j <= i then
        continue
      let finIExpr : Expr := toExpr i
      let finJExpr : Expr := toExpr j
      let mvar_p ← Meta.mkFreshExprMVar <| mkApp2 (mkConst ``unitDistance) u v
      let p := mvar_p.mvarId!
      let edgeExpr : Option Expr ← p.withContext do
        let lolq := Lean.Elab.Tactic.run p (Lean.Elab.Tactic.evalTactic (← `(tactic| try theta_calc)))
        let qeq := (← lolq.run).fst
        dbg_trace s!"{i} {j} {qeq.length}"
        if qeq.isEmpty then -- how to better check that the proof is correct?
          let proof := (← getExprMVarAssignment? p).get!
          return mkApp4 (mkConst ``UnitGraph.Edge.mk) vertexesExpr finIExpr finJExpr proof
        return none
      if edgeExpr.isSome then
        edges := edgeExpr.get! :: edges

  return mkApp2 (mkConst ``UnitGraph.mk) vertexesExpr (← aaux edges (mkApp (mkConst ``UnitGraph.Edge) vertexesExpr))

open Lean.Elab.Tactic in
elab "of_vertexes " : tactic =>
  withMainContext do
    -- let vertexes ← elabTerm v (mkApp (mkConst ``List) (mkConst ``Expr))
    liftMetaFinishingTactic fun g => do
      let res ← UnitGraph.ofVertexes V_31
      g.assign res

-- set_option maxHeartbeats 0 in
-- noncomputable def kuk : UnitGraph := by of_vertexes

open UnitGraph

example : ¬ planeColorable 2 := by
  intro h_p_col
  absurd planeColorable_graph_Colorable h_p_col kuk
  apply Noncolorable_from_unsat
  dsimp [kuk, toCompGraph, CompGraph.ColorablilityCNF]
  apply LitToNat_equisat _
  clear h_p_col
  unsat_native_decide
