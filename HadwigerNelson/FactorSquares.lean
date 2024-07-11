import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic

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
        have kek := s.correct_prod
        have := s.cur_factor_pos
        generalize s.free = a at *
        generalize s.sqrt = b at *
        generalize s.cur_factor = c at *
        rw [kek]
        obtain ⟨d, hd⟩ := hdiv
        rw [hd]
        qify; field_simp; ring
      correct_free := by
        intro f f_lb f_ub
        have kek := s.correct_free f f_lb f_ub
        have := s.cur_factor_pos
        contrapose! kek
        -- separate lemma dvd_of_mul_left_dvd
        obtain ⟨c, hc⟩ := kek
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
        have kek := s.correct_free
        by_contra f_neq_1
        apply kek f
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

def kek : {x : ℕ // Squarefree x ∨ x = 0} := ⟨1, by left; simp⟩

#print axioms kek

#print factorSquaresStep

------------------------------------------

-- structure QSqrt where
--   coeffs : Batteries.HashMap {d : ℤ // Squarefree d ∧ d ≠ 0} {c : ℚ // c ≠ 0}

-- instance : ToString QSqrt where
--   toString x :=
--     x.coeffs.fold (init := "") fun acc d c =>
--       acc ++ s!"+ ({c.val})√{d} "

-- def QSqrt.zero : QSqrt where
--   coeffs := .empty


-- lemma Batteries.HashMap.insert_contains_iff {α β : Type} [BEq α] [Hashable α]
--     (map : Batteries.HashMap α β) (k₁ k₂ : α) (v : β) :
--     (map.insert k₁ v).contains k₂ ↔ (k₁ = k₂ ∨ map.contains k₂) := by
--   sorry

-- def QSqrt.ofList (coeffs : List (ℤ × ℚ)) : QSqrt :=
--   coeffs.foldl (init := .zero) fun acc (d, a) =>
--     if hd : d = 0 then
--       acc
--     else
--       let factorRes := factorSquares d hd
--       let k := factorRes.free
--       let v : ℚ := match acc.coeffs.find? factorRes.free with
--       | none => a * factorRes.sqrt
--       | some v_was => v_was + a * factorRes.sqrt
--       if hv : v = 0 then
--         acc
--       else
--         {
--           coeffs := acc.coeffs.insert k ⟨v, hv⟩
--         }

-- instance : BEq QSqrt where
--   beq := fun a b =>
--     a.coeffs.toList.all fun ⟨k, v⟩ =>
--       match b.coeffs.find? k with
--       | none => false
--       | some v' => v == v'

-- #eval QSqrt.ofList [(1, 11), (2, 3)] == QSqrt.ofList [(1, 1), (2, 1), (4, 5), (8, 1)]

-- instance : Mul QSqrt where
--   mul x y :=
--     .ofList <| Batteries.HashMap.toList <|
--     x.coeffs.fold (init := .empty) fun acc₁ d₁ c₁ =>
--     y.coeffs.fold (init := acc₁) fun acc₂ d₂ c₂ =>
--       let key := d₁.val * d₂.val
--       let value_was := acc₂.findD key 0
--       let value := value_was + if d₁.val < 0 && d₂.val < 0 then
--           -c₁.val * c₂.val
--         else
--           c₁.val * c₂.val
--       acc₂.insert key value

-- def QSqrt.one : QSqrt := .ofList [(1, 1)]

-- instance : CommRing QSqrt where
--   zero := .zero
--   one := .ofList [(1, 1)]
--   add x y := .ofList <| List.map (fun (x, y) => (x.val, y)) <| Batteries.HashMap.toList <|
--     let xq := x.coeffs.mapVal (fun _ v => v.val)
--     let yq := y.coeffs.mapVal (fun _ v => v.val)
--     xq.mergeWith (fun _ v₁ v₂ => v₁ + v₂) yq
--   neg x := {
--     coeffs := sorry --x.coeffs.mapVal fun _ v => -v
--   }
--   sub x y := {
--     coeffs := sorry -- x.coeffs.mergeWith (fun _ v₁ v₂ => v₁ - v₂) y.coeffs
--   }
--   nsmul n x := {
--     coeffs := sorry -- x.coeffs.mapVal fun _ (v : ℚ) => n * v
--   }
--   zsmul n x := {
--     coeffs := sorry -- x.coeffs.mapVal fun _ (v : ℚ) => n * v
--   }
--   natCast n := .ofList [(1, n)]
--   intCast n := .ofList [(1, n)]
--   npow :=
--     let rec go n x := match n with
--     | 0 => QSqrt.one
--     | k + 1 => (go k x) * x
--     go
--   add_assoc a b c := sorry
--   add_comm a b := sorry
--   zero_add a := sorry
--   add_zero a := sorry
--   left_distrib := sorry
--   right_distrib := sorry
--   zero_mul := sorry
--   mul_zero := sorry
--   mul_assoc := sorry
--   one_mul := sorry
--   mul_one := sorry
--   mul_comm := sorry
--   nsmul_zero := sorry
--   nsmul_succ := sorry
--   natCast_zero := sorry
--   natCast_succ := sorry
--   npow_zero := sorry
--   npow_succ := sorry
--   sub_eq_add_neg := sorry
--   zsmul_zero' := sorry
--   zsmul_succ' := sorry
--   zsmul_neg' := sorry
--   add_left_neg := sorry
--   intCast_ofNat := sorry
--   intCast_negSucc := sorry

-- def QSqrt.re (x : QSqrt) : QSqrt where
--   coeffs := x.coeffs.filter fun d _ => d.val > 0

-- def QSqrt.im (x : QSqrt) : QSqrt :=
--   .ofList <| x.coeffs.toList.filterMap fun (d, c) =>
--     if d.val ≥ 0 then .none else .some (-d.val, c)

-- def QSqrt.norm_sq (x : QSqrt) : QSqrt :=
--   x.re^2 + x.im^2



-- def theta (i : ℕ) : QSqrt :=
--   .ofList [(1, (2*i - 1) / (2*i)), (1 - 4*i, 1 / (2*i))]

-- def θ' : QSqrt := .ofList [(33, 1/6), (-3, 1/6)]
-- def θ'_inv : QSqrt := .ofList [(33, 1/6), (-3, -1/6)]

-- #eval ((theta 1)^6)

-- #eval (θ' * θ'_inv)

-- #eval θ'^2 == theta 3

-- #eval (theta 33).norm_sq

-- def V_31 : List QSqrt := Id.run do
--   let mut ans := []
--   for j in [:6] do
--     for k in [:5] do
--     ans := (theta 1)^j * θ'_inv * θ'^k :: ans
--   return .zero :: ans

-- #eval V_31.length

-- def unitDistance (u v : ℂ) : Prop := ‖u - v‖ = 1

-- #print unitDistance

-- #check Complex.instNorm

-- structure UnitGraph where
--   vertexes : List ℂ
--   edges : List <|
--     {e : Fin vertexes.length × Fin vertexes.length // unitDistance vertexes[e.1] vertexes[e.2]}

-- def kek : UnitGraph where
--   vertexes := [0, 1]
--   edges := [
--     ⟨((0 : Fin 2), (1 : Fin 2)), by
--       simp [getElem, unitDistance]
--     ⟩
--   ]



-- -------------------------------------

-- noncomputable def QSqrt.emb (x : QSqrt) : ℂ :=
--   x.coeffs.fold (init := 0) (fun acc d a =>
--     let root : ℂ := if d.val < 0 then ⟨0, √(-d.val)⟩ else ⟨√d.val, 0⟩
--     acc + root * a.val
--   )



-- theorem QSqrt.emb_isometric (x : QSqrt) : Complex.normSq x.emb = x.norm_sq.emb := by
--   simp [Complex.normSq, QSqrt.norm_sq]

-- instance (x : QSqrt) : Decidable (Complex.normSq x.emb = 1) :=
--   if h : x.norm_sq == 1 then
--     .isTrue <| by
--       have hm : x.norm_sq = 1 := by sorry
--       rw [QSqrt.emb_isometric x]
--       sorry
--   else
--     sorry
