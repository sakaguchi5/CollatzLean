import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerFarey
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.RhinTwoThreeGap14
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The single external theorem interface: Rhin linear form, exponent 14

このファイルだけが査読済み外部数学を interface として受け取る。
13.3 を安全に 14 へ丸めた形

  max(p,q)^(-14) <= |q log 2 - p log 3|

を positive integer `p,q` かつ `2 <= max p q` に対して仮定する。
これは Rhin 型評価の適用範囲 `M >= 2` をそのまま保持する。
それ以外の power gap / denominator growth は Lean 内で導く。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

structure RhinLinearForm14 where
  lower :
    ∀ p q : ℕ,
      0 < p →
      0 < q →
      2 ≤ max p q →
      (((max p q : ℕ) : ℝ) ^ 14)⁻¹ ≤
        |(q : ℝ) * Real.log 2 -
          (p : ℝ) * Real.log 3|

namespace RhinLinearForm14

private theorem log_two_gt_half :
    (1 / 2 : ℝ) < Real.log 2 := by
  have h :=
    Real.log_lt_sub_one_of_pos
      (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hlog : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact Real.log_inv 2
  rw [hlog] at h
  norm_num at h ⊢
  linarith

private theorem log_three_lt_two : Real.log 3 < 2 := by
  have h :=
    Real.log_lt_sub_one_of_pos
      (x := (3 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

private theorem exponent_p_lt_H
    {p H : ℕ}
    (hp : 0 < p)
    (hPow : 3 ^ p < 2 ^ H) :
    p < H := by
  have h23 : 2 ^ p < 3 ^ p :=
    Nat.pow_lt_pow_left (by norm_num : 2 < 3) (Nat.ne_of_gt hp)
  by_contra hnot
  have hH : H ≤ p := by omega
  have htwo : 2 ^ H ≤ 2 ^ p :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hH
  omega

private theorem linear_form_pos_of_three_lt_two
    {p H : ℕ}
    (hPow : 3 ^ p < 2 ^ H) :
    0 < (H : ℝ) * Real.log 2 -
      (p : ℝ) * Real.log 3 := by
  have hCast :
      (3 : ℝ) ^ p < (2 : ℝ) ^ H := by
    exact_mod_cast hPow
  have hlog :=
    Real.log_lt_log (by positivity : (0 : ℝ) < (3 : ℝ) ^ p) hCast
  rw [Real.log_pow, Real.log_pow] at hlog
  nlinarith

/-- raw Rhin lower bound gives the H-based integer power-gap corollary. -/
theorem toRhinTwoThreePowerGap14
    (R : RhinLinearForm14) :
    RhinTwoThreePowerGap14 := by
  refine ⟨?_⟩
  intro p H hp hPow
  have hpH : p < H := exponent_p_lt_H hp hPow
  have hHpos : 0 < H := by omega
  have hmax : max p H = H := max_eq_right (by omega)
  have hlinPos := linear_form_pos_of_three_lt_two hPow
  have hMaxTwo : 2 ≤ max p H := by
    rw [hmax]
    omega
  have hR := R.lower p H hp hHpos hMaxTwo
  rw [hmax, abs_of_pos hlinPos] at hR
  let A : ℝ := (3 : ℝ) ^ p
  let B : ℝ := (2 : ℝ) ^ H
  have hApos : 0 < A := by positivity
  have hBpos : 0 < B := by positivity
  have hAB : A < B := by
    dsimp [A, B]
    exact_mod_cast hPow
  have hxPos : 0 < B / A := div_pos hBpos hApos
  have hxNe : B / A ≠ 1 := by
    intro h
    have : B = A := (div_eq_one_iff_eq hApos.ne').mp h
    exact (ne_of_gt hAB) this
  have hLogRatio :=
    Real.log_lt_sub_one_of_pos hxPos hxNe
  have hLogEq :
      Real.log (B / A) =
        (H : ℝ) * Real.log 2 -
          (p : ℝ) * Real.log 3 := by
    dsimp [A, B]
    rw [Real.log_div (by positivity) (by positivity)]
    rw [Real.log_pow, Real.log_pow]
  rw [hLogEq] at hLogRatio
  have hLowerUpper :
      (((H : ℝ) ^ 14)⁻¹) < B / A - 1 :=
    lt_of_le_of_lt hR hLogRatio
  have hDiffEq : B / A - 1 = (B - A) / A := by
    field_simp [hApos.ne']
  rw [hDiffEq] at hLowerUpper
  have hHpowPos : 0 < (H : ℝ) ^ 14 := by positivity
  have h1 :
      A / ((H : ℝ) ^ 14) < B - A := by
    have hraw := (lt_div_iff₀ hApos).1 hLowerUpper
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hraw
  have h2 :
      A < ((H : ℝ) ^ 14) * (B - A) := by
    have hraw := (div_lt_iff₀ hHpowPos).1 h1
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw
  have hNatCast :
      (((2 ^ H - 3 ^ p : ℕ) : ℝ)) = B - A := by
    dsimp [A, B]
    rw [Nat.cast_sub (Nat.le_of_lt hPow)]
    norm_num
  have hNatStrict :
      ((3 ^ p : ℕ) : ℝ) <
        (((H ^ 14 * (2 ^ H - 3 ^ p) : ℕ) : ℝ)) := by
    rw [Nat.cast_mul, Nat.cast_pow, hNatCast]
    simpa [A] using h2
  exact Nat.le_of_lt (by exact_mod_cast hNatStrict)

/-- Consequently the existing Boundary-A polynomial gap interface is available. -/
theorem boundaryGap
    (R : RhinLinearForm14) :
    ∀ p H : ℕ,
      0 < p →
      3 ^ p < 2 ^ H →
      3 ^ p ≤
        rhinGapK * (p + 1) ^ rhinGapA *
          (2 ^ H - 3 ^ p) :=
  R.toRhinTwoThreePowerGap14.boundary_gap

private theorem log_order_of_below
    {x : CriticalPowerFraction}
    (h : x.Below) :
    (x.p : ℝ) * Real.log 3 <
      (x.q : ℝ) * Real.log 2 := by
  have hc : (3 : ℝ) ^ x.p < (2 : ℝ) ^ x.q := by
    exact_mod_cast h
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < (3 : ℝ) ^ x.p) hc
  rw [Real.log_pow, Real.log_pow] at hl
  exact hl

private theorem log_order_of_above
    {x : CriticalPowerFraction}
    (h : x.Above) :
    (x.q : ℝ) * Real.log 2 <
      (x.p : ℝ) * Real.log 3 := by
  have hc : (2 : ℝ) ^ x.q < (3 : ℝ) ^ x.p := by
    exact_mod_cast h
  have hl := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ x.q) hc
  rw [Real.log_pow, Real.log_pow] at hl
  exact hl

/-- Below → Above の並びでは determinant の向きも一意。 -/
private theorem determinant_eq_of_below_above
    {a b : CriticalPowerFraction}
    (hadj : CriticalPowerFraction.FareyAdjacent a b)
    (ha : a.Below)
    (hb : b.Above) :
    a.p * b.q + 1 = b.p * a.q := by
  rcases hadj with hd | hd
  · exact hd
  · have hcross :=
      CriticalPowerFraction.cross_lt_of_below_above ha hb
    omega


/-- Above → Below の並びでは determinant の向きも一意。 -/
private theorem determinant_eq_of_above_below
    {a b : CriticalPowerFraction}
    (hadj : CriticalPowerFraction.FareyAdjacent a b)
    (ha : a.Above)
    (hb : b.Below) :
    b.p * a.q + 1 = a.p * b.q := by
  rcases hadj with hd | hd
  · have hcross :=
      CriticalPowerFraction.cross_lt_of_below_above hb ha
    omega
  · exact hd

/--
Farey adjacent な opposite-side pair では、
`a` と critical slope の rational error は Farey width より小さい。
-/
private theorem ratio_error_lt_of_opposite
    {a b : CriticalPowerFraction}
    (hadj : CriticalPowerFraction.FareyAdjacent a b)
    (hOpp :
      (a.Below ∧ b.Above) ∨
      (a.Above ∧ b.Below)) :
    |Real.log 2 / Real.log 3 - (a.p : ℝ) / a.q| <
      1 / ((a.q : ℝ) * b.q) := by
  have hlog3Pos : 0 < Real.log 3 :=
    Real.log_pos (by norm_num)
  have haqR : 0 < (a.q : ℝ) := by
    exact_mod_cast a.q_pos
  have hbqR : 0 < (b.q : ℝ) := by
    exact_mod_cast b.q_pos
  rcases hOpp with h | h
  ·/- Below → Above -/
    have haLog := log_order_of_below h.1
    have hbLog := log_order_of_above h.2
    have hdet :
        a.p * b.q + 1 = b.p * a.q :=
      determinant_eq_of_below_above hadj h.1 h.2
    have hdetR :
        (a.p : ℝ) * b.q + 1 =
          (b.p : ℝ) * a.q := by
      exact_mod_cast hdet
    have hRealDet :
        (b.p : ℝ) / b.q - (a.p : ℝ) / a.q =
          1 / ((a.q : ℝ) * b.q) := by
      field_simp [haqR.ne', hbqR.ne']
      nlinarith [hdetR]
    have haAlpha :
        (a.p : ℝ) / a.q <
          Real.log 2 / Real.log 3 := by
      rw [div_lt_iff₀ haqR]
      rw [show
        (Real.log 2 / Real.log 3) * (a.q : ℝ) =
          ((a.q : ℝ) * Real.log 2) / Real.log 3 by
            ring]
      rw [lt_div_iff₀ hlog3Pos]
      nlinarith [haLog]
    have hAlphaB :
        Real.log 2 / Real.log 3 <
          (b.p : ℝ) / b.q := by
      rw [lt_div_iff₀ hbqR]
      rw [show
        (Real.log 2 / Real.log 3) * (b.q : ℝ) =
          ((b.q : ℝ) * Real.log 2) / Real.log 3 by
            ring]
      rw [div_lt_iff₀ hlog3Pos]
      nlinarith [hbLog]
    rw [abs_of_pos (sub_pos.mpr haAlpha)]
    rw [← hRealDet]
    linarith
  ·/- Above → Below -/
    have haLog := log_order_of_above h.1
    have hbLog := log_order_of_below h.2
    have hdet :
        b.p * a.q + 1 = a.p * b.q :=
      determinant_eq_of_above_below hadj h.1 h.2
    have hdetR :
        (b.p : ℝ) * a.q + 1 =
          (a.p : ℝ) * b.q := by
      exact_mod_cast hdet
    have hRealDet :
        (a.p : ℝ) / a.q - (b.p : ℝ) / b.q =
          1 / ((a.q : ℝ) * b.q) := by
      field_simp [haqR.ne', hbqR.ne']
      nlinarith [hdetR]
    have hbAlpha :
        (b.p : ℝ) / b.q <
          Real.log 2 / Real.log 3 := by
      rw [div_lt_iff₀ hbqR]
      rw [show
        (Real.log 2 / Real.log 3) * (b.q : ℝ) =
          ((b.q : ℝ) * Real.log 2) / Real.log 3 by
            ring]
      rw [lt_div_iff₀ hlog3Pos]
      nlinarith [hbLog]
    have hAlphaA :
        Real.log 2 / Real.log 3 <
          (a.p : ℝ) / a.q := by
      rw [lt_div_iff₀ haqR]
      rw [show
        (Real.log 2 / Real.log 3) * (a.q : ℝ) =
          ((a.q : ℝ) * Real.log 2) / Real.log 3 by
            ring]
      rw [div_lt_iff₀ hlog3Pos]
      nlinarith [haLog]
    rw [abs_sub_comm]
    rw [abs_of_pos (sub_pos.mpr hAlphaA)]
    rw [← hRealDet]
    linarith

/--
critical slope からの rational error bound を
linear form bound へ変換する。
-/
private theorem linearForm_width_of_ratio_error
    {a b : CriticalPowerFraction}
    (hErr :
      |Real.log 2 / Real.log 3 - (a.p : ℝ) / a.q| <
        1 / ((a.q : ℝ) * b.q)) :
    |(a.q : ℝ) * Real.log 2 -
        (a.p : ℝ) * Real.log 3| <
      Real.log 3 / (b.q : ℝ) := by
  have hlog3Pos : 0 < Real.log 3 :=
    Real.log_pos (by norm_num)
  have haqR : 0 < (a.q : ℝ) := by
    exact_mod_cast a.q_pos
  have hbqR : 0 < (b.q : ℝ) := by
    exact_mod_cast b.q_pos
  have hscalePos :
      0 < (a.q : ℝ) * Real.log 3 :=
    mul_pos haqR hlog3Pos
  have hEq :
      (a.q : ℝ) * Real.log 2 -
          (a.p : ℝ) * Real.log 3 =
        ((a.q : ℝ) * Real.log 3) *
          (Real.log 2 / Real.log 3 -
            (a.p : ℝ) / a.q) := by
    field_simp [hlog3Pos.ne', haqR.ne']
  have hmul :=
    mul_lt_mul_of_pos_left hErr hscalePos
  calc
    |(a.q : ℝ) * Real.log 2 -
        (a.p : ℝ) * Real.log 3|
        =
      ((a.q : ℝ) * Real.log 3) *
        |Real.log 2 / Real.log 3 -
          (a.p : ℝ) / a.q| := by
            rw [hEq, abs_mul, abs_of_pos hscalePos]
    _ <
      ((a.q : ℝ) * Real.log 3) *
        (1 / ((a.q : ℝ) * b.q)) := hmul
    _ = Real.log 3 / (b.q : ℝ) := by
      field_simp [haqR.ne', hbqR.ne']

/--
opposite-side Farey adjacent pair に対する
共通 linear-form width。
-/
private theorem linearForm_width_of_opposite
    {a b : CriticalPowerFraction}
    (hadj : CriticalPowerFraction.FareyAdjacent a b)
    (hOpp :
      (a.Below ∧ b.Above) ∨
      (a.Above ∧ b.Below)) :
    |(a.q : ℝ) * Real.log 2 -
        (a.p : ℝ) * Real.log 3| <
      Real.log 3 / (b.q : ℝ) := by
  apply linearForm_width_of_ratio_error
  exact ratio_error_lt_of_opposite hadj hOpp


/--
Rhin 型下界と `log 3 / q'` 型上界から
`q' ≤ 2 q^14` を得る。
-/
private theorem denominator_le_of_rhin_width
    {q q' : ℕ}
    {E : ℝ}
    (hq : 0 < q)
    (hq' : 0 < q')
    (hR :
      (((q : ℝ) ^ 14)⁻¹) ≤ E)
    (hWidth :
      E < Real.log 3 / (q' : ℝ)) :
    q' ≤ 2 * q ^ 14 := by
  have hLogBound :
      Real.log 3 / (q' : ℝ) ≤
        2 / (q' : ℝ) := by
    have hq'R : 0 < (q' : ℝ) := by
      exact_mod_cast hq'
    exact
      (div_le_div_iff_of_pos_right hq'R).2
        (le_of_lt log_three_lt_two)
  have hCombine :
      (((q : ℝ) ^ 14)⁻¹) <
        2 / (q' : ℝ) :=
    lt_of_le_of_lt hR
      (lt_of_lt_of_le hWidth hLogBound)
  have hqPow :
      0 < (q : ℝ) ^ 14 := by
    positivity
  have hq'R :
      0 < (q' : ℝ) := by
    exact_mod_cast hq'
  have hraw :=
    (lt_div_iff₀ hq'R).1 hCombine
  have hdiv :
      (q' : ℝ) / (q : ℝ) ^ 14 < 2 := by
    simpa [div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hraw
  have hmul :
      (q' : ℝ) <
        2 * (q : ℝ) ^ 14 := by
    have :=
      (div_lt_iff₀ hqPow).1 hdiv
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  exact Nat.le_of_lt (by
    exact_mod_cast hmul)

/--
For Farey adjacent fractions bracketing the critical slope,
Rhin implies the next denominator bound `q' <= 2 q^14`.
-/
theorem nextDenominator_le
    (R : RhinLinearForm14)
    {a b : CriticalPowerFraction}
    (haPos : 0 < a.p)
    (haLe : a.p ≤ a.q)
    (haQTwo : 2 ≤ a.q)
    (hadj : CriticalPowerFraction.FareyAdjacent a b)
    (hOpp :
      (a.Below ∧ b.Above) ∨
      (a.Above ∧ b.Below)) :
    b.q ≤ 2 * a.q ^ 14 := by
  have hqPos : 0 < a.q :=
    a.q_pos
  have hbqPos : 0 < b.q :=
    b.q_pos
  have hmax :
      max a.p a.q = a.q :=
    max_eq_right haLe
  have hMaxTwo :
      2 ≤ max a.p a.q := by
    rw [hmax]
    exact haQTwo
  have hR :=
    R.lower
      a.p a.q
      haPos hqPos hMaxTwo
  rw [hmax] at hR
  have hWidth :
      |(a.q : ℝ) * Real.log 2 -
          (a.p : ℝ) * Real.log 3| <
        Real.log 3 / (b.q : ℝ) :=
    linearForm_width_of_opposite hadj hOpp
  exact
    denominator_le_of_rhin_width
      hqPos hbqPos hR hWidth

/-- specialized to the actual critical power-Farey sequence. -/
theorem actual_q_next_le
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 9 ≤ j) :
    criticalPowerQ (j + 1) ≤
      2 * criticalPowerQ j ^ 14 := by
  apply R.nextDenominator_le
  · exact criticalPowerP_pos (by omega)
  · exact criticalPowerP_le_Q j
  · change 2 ≤ criticalPowerQ j
    have hmono :=
      criticalPowerQ_mono_of_le
        (show 9 ≤ j by exact hj)
    rw [criticalPowerQ_nine] at hmono
    exact le_trans (by norm_num : 2 ≤ 1054) hmono
  · exact criticalPower_adjacent_next hj
  · rcases criticalPower_opposite_next with h | h
    · exact Or.inl ⟨h.2.1, h.2.2⟩
    · exact Or.inr ⟨h.2.1, h.2.2⟩

end RhinLinearForm14

end ExternalArithmetic
end CSTMicro
end Collatz2
