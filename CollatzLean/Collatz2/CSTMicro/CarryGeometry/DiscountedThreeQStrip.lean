import CollatzLean.Collatz2.CSTMicro.CarryGeometry.LocalRankTopLedger
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Rat.Defs

/-!
# Discounted sharp strip

`ThreeQSmallStrip` は各 proper cut contribution を一様に `< 3^m` と評価して

  3q < m

を得た。ここでは cut `k` の critical roof からの沈み

  e_k = extraDepth(w,k)

を保持する。FirstCrossing では

  2^e_k * normalizedCutTerm(k) < 3^m,

従って rational normalization では

  normalizedCutTerm(k) / 3^m < 2^(-e_k).

全 proper cut を足して

  3q < 1 + sum_{k=1}^{m-1} 2^(-e_k)

を得る。
-/

namespace Collatz2
namespace Word

/-- 非空 odd-only word の affine constant は正。 -/
theorem affineConst_pos_of_nonempty
    {w : Word}
    (hne : w ≠ []) :
    0 < affineConst w := by
  cases w with
  | nil => contradiction
  | cons e t =>
      simp only [affineConst_cons]
      positivity

/--
proper cut の critical depth discount を残した exact integer bound。

  2^extraDepth(k) * normalizedCutTerm(k) < 3^p.
-/
theorem FirstCrossing.twoPow_extraDepth_mul_normalizedCutTerm_lt_threePow
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    2 ^ extraDepth w k * normalizedCutTerm w k <
      3 ^ oddSteps w := by
  have hDepth :
      prefixTwoDepth w k ≤ criticalHeight k :=
    hF.prefixTwoDepth_le_criticalHeight hkPos hkLt
  have hAdd :
      prefixTwoDepth w k + extraDepth w k = criticalHeight k := by
    unfold extraDepth
    omega
  have hCrit := criticalHeight_pow_lt_threePow hkPos
  have hRightPos : 0 < 3 ^ (oddSteps w - k) := by positivity
  have hScaled :
      2 ^ criticalHeight k * 3 ^ (oddSteps w - k) <
        3 ^ k * 3 ^ (oddSteps w - k) :=
    Nat.mul_lt_mul_of_pos_right hCrit hRightPos
  have hKLe : k ≤ oddSteps w := Nat.le_of_lt hkLt
  have hSum : k + (oddSteps w - k) = oddSteps w :=
    Nat.add_sub_of_le hKLe
  unfold normalizedCutTerm
  calc
    2 ^ extraDepth w k *
          (2 ^ prefixTwoDepth w k * 3 ^ (oddSteps w - k))
        =
      2 ^ (prefixTwoDepth w k + extraDepth w k) *
        3 ^ (oddSteps w - k) := by
          rw [pow_add]
          ring
    _ = 2 ^ criticalHeight k * 3 ^ (oddSteps w - k) := by
          rw [hAdd]
    _ < 3 ^ k * 3 ^ (oddSteps w - k) := hScaled
    _ = 3 ^ oddSteps w := by
          rw [← pow_add, hSum]

/-- termwise rational discounted bound。 -/
theorem FirstCrossing.normalizedCutRatio_lt_invTwoPowExtraDepth
    {w : Word}
    (hF : FirstCrossing w)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps w) :
    ((normalizedCutTerm w k : ℕ) : ℚ) /
        ((3 ^ oddSteps w : ℕ) : ℚ) <
      (1 : ℚ) / (((2 ^ extraDepth w k : ℕ)) : ℚ) := by
  have hNat :=
    hF.twoPow_extraDepth_mul_normalizedCutTerm_lt_threePow hkPos hkLt
  apply (div_lt_div_iff₀ (by positivity : (0 : ℚ) < ((3 ^ oddSteps w : ℕ) : ℚ))
      (by positivity : (0 : ℚ) < ((2 ^ extraDepth w k : ℕ) : ℚ))).2
  have hQ :
      (((2 ^ extraDepth w k : ℕ) : ℚ)) *
          ((normalizedCutTerm w k : ℕ) : ℚ) <
        ((3 ^ oddSteps w : ℕ) : ℚ) := by
    exact_mod_cast hNat
  nlinarith

/-- proper cuts `1,...,p-1` の discounted critical-depth mass。 -/
noncomputable def discountedExtraDepthMass
    (w : Word) : ℚ :=
  Finset.sum (Finset.range (oddSteps w - 1))
    (fun j =>
      (1 : ℚ) /
        (((2 ^ extraDepth w (j + 1) : ℕ)) : ℚ))

/-- proper normalized cut ratios の exact sum。 -/
noncomputable def properNormalizedCutRatioSum
    (w : Word) : ℚ :=
  Finset.sum (Finset.range (oddSteps w - 1))
    (fun j =>
      ((normalizedCutTerm w (j + 1) : ℕ) : ℚ) /
        ((3 ^ oddSteps w : ℕ) : ℚ))

/--
`3*affineConst / 3^p` は `1 + proper cut ratios` に exact 分解する。
-/
theorem three_mul_affineConst_div_threePow_eq_one_add_properRatioSum
    {w : Word}
    (hp : 0 < oddSteps w) :
    ((3 * affineConst w : ℕ) : ℚ) /
        ((3 ^ oddSteps w : ℕ) : ℚ) =
      1 + properNormalizedCutRatioSum w := by
  let p := oddSteps w
  have hpEq : p = (p - 1) + 1 := by omega
  have hSum := sum_normalizedCutTerm_eq_three_mul_affineConst w
  have hZero : normalizedCutTerm w 0 = 3 ^ p := by
    simp [normalizedCutTerm, prefixTwoDepth, p]
  rw [show oddSteps w = (p - 1) + 1 by simpa [p] using hpEq] at hSum
  rw [Finset.sum_range_succ'] at hSum
  rw [show normalizedCutTerm w 0 = 3 ^ p by simpa [p] using hZero] at hSum
  have hNat :
      3 * affineConst w =
        3 ^ p +
          Finset.sum (Finset.range (p - 1))
            (fun j => normalizedCutTerm w (j + 1)) := by
    simpa [Nat.add_comm] using hSum.symm
  have hQ :
      ((3 * affineConst w : ℕ) : ℚ) =
        ((3 ^ p : ℕ) : ℚ) +
          Finset.sum (Finset.range (p - 1))
            (fun j => ((normalizedCutTerm w (j + 1) : ℕ) : ℚ)) := by
    exact_mod_cast hNat
  rw [hQ]
  unfold properNormalizedCutRatioSum
  rw [add_div]
  have hPowNe : (((3 ^ p : ℕ) : ℚ)) ≠ 0 := by positivity
  rw [div_self hPowNe]
  rw [Finset.sum_div]

/--
FirstCrossing affine ratio の discounted upper bound。
-/
theorem FirstCrossing.three_mul_affineConst_div_threePow_lt_discounted
    {w : Word}
    (hF : FirstCrossing w)
    (hp : 1 < oddSteps w) :
    ((3 * affineConst w : ℕ) : ℚ) /
        ((3 ^ oddSteps w : ℕ) : ℚ) <
      1 + discountedExtraDepthMass w := by
  let p := oddSteps w
  have hNonempty : (Finset.range (p - 1)).Nonempty := by
    refine ⟨0, Finset.mem_range.mpr ?_⟩
    omega
  have hSumLt :
      properNormalizedCutRatioSum w < discountedExtraDepthMass w := by
    unfold properNormalizedCutRatioSum discountedExtraDepthMass
    apply Finset.sum_lt_sum_of_nonempty hNonempty
    intro j hj
    have hjLt : j < p - 1 := Finset.mem_range.mp hj
    have hkPos : 0 < j + 1 := by omega
    have hkLt : j + 1 < oddSteps w := by
      dsimp [p] at hjLt
      omega
    exact hF.normalizedCutRatio_lt_invTwoPowExtraDepth hkPos hkLt
  rw [three_mul_affineConst_div_threePow_eq_one_add_properRatioSum (by omega)]
  linarith

end Word

namespace CSTMicro
namespace FirstFailureEdge

/--
actual upper affine equation から、
`2^H * q` は affine numerator 以下。
-/
theorem twoPow_mul_upperNormalizedDefectNat_le_affineConst
    (F : FirstFailureEdge) :
    2 ^ Collatz2.Word.twoSteps F.upperExponentWord *
        F.upperNormalizedDefectNat ≤
      Collatz2.Word.affineConst F.upperExponentWord := by
  have hAffine :=
    F.upperExponentWord_affineConst_eq_gap_mul_R_add_twoPow_mul_upperQ
  have hEq :
      Collatz2.Word.affineConst F.upperExponentWord =
        Collatz2.Word.terminalGap F.upperExponentWord *
            F.step.edge.upperR +
          2 ^ Collatz2.Word.twoSteps F.upperExponentWord *
            F.upperNormalizedDefectNat := by
    simpa using hAffine
  omega


/--
actual upper q は contracting gap により

  3^m * q < B

を満たす。
-/
theorem threePow_mul_upperNormalizedDefectNat_lt_affineConst
    (F : FirstFailureEdge) :
    3 ^ Collatz2.Word.oddSteps F.upperExponentWord *
        F.upperNormalizedDefectNat <
      Collatz2.Word.affineConst F.upperExponentWord := by
  have hF :
      Collatz2.Word.FirstCrossing F.upperExponentWord :=
    F.upperExponentWord_firstCrossing
  have hPow :
      3 ^ Collatz2.Word.oddSteps F.upperExponentWord <
        2 ^ Collatz2.Word.twoSteps F.upperExponentWord :=
    (Collatz2.Word.contracting_iff_threePow_lt_twoPow).1
      hF.terminalContracting
  have hMqLeB :
      2 ^ Collatz2.Word.twoSteps F.upperExponentWord *
          F.upperNormalizedDefectNat ≤
        Collatz2.Word.affineConst F.upperExponentWord :=
    F.twoPow_mul_upperNormalizedDefectNat_le_affineConst
  by_cases hq0 : F.upperNormalizedDefectNat = 0
  · rw [hq0, mul_zero]
    exact
      Collatz2.Word.affineConst_pos_of_nonempty
        hF.nonempty
  · have hqPos : 0 < F.upperNormalizedDefectNat :=
      Nat.pos_of_ne_zero hq0
    have hMul :
        3 ^ Collatz2.Word.oddSteps F.upperExponentWord *
            F.upperNormalizedDefectNat <
          2 ^ Collatz2.Word.twoSteps F.upperExponentWord *
            F.upperNormalizedDefectNat :=
      Nat.mul_lt_mul_of_pos_right hPow hqPos
    exact lt_of_lt_of_le hMul hMqLeB


/--
natural inequality `3^m q < B` を affine ratio の
rational inequality へ移す。
-/
theorem three_mul_upperNormalizedDefectNat_lt_affineRatio
    (F : FirstFailureEdge) :
    ((3 * F.upperNormalizedDefectNat : ℕ) : ℚ) <
      ((3 * Collatz2.Word.affineConst F.upperExponentWord : ℕ) : ℚ) /
        ((3 ^ Collatz2.Word.oddSteps F.upperExponentWord : ℕ) : ℚ) := by
  have hStrictNat :=
    F.threePow_mul_upperNormalizedDefectNat_lt_affineConst
  apply
    (lt_div_iff₀
      (by
        positivity :
        (0 : ℚ) <
          ((3 ^ Collatz2.Word.oddSteps F.upperExponentWord : ℕ) : ℚ))).2
  have hQ :
      (((3 ^ Collatz2.Word.oddSteps F.upperExponentWord *
          F.upperNormalizedDefectNat : ℕ)) : ℚ) <
        ((Collatz2.Word.affineConst F.upperExponentWord : ℕ) : ℚ) := by
    exact_mod_cast hStrictNat
  push_cast at hQ ⊢
  nlinarith

/--
nontrivial first-failure upper の discounted sharp strip。

  3q < 1 + sum_{k=1}^{m-1} 2^(-extraDepth(k)).
-/
theorem three_mul_upperNormalizedDefectNat_lt_one_add_discountedExtraDepthMass
    (F : FirstFailureEdge)
    (hLen : 2 < F.step.edge.upperWord.length) :
    ((3 * F.upperNormalizedDefectNat : ℕ) : ℚ) <
      1 + Collatz2.Word.discountedExtraDepthMass F.upperExponentWord := by
  have hm :
      1 < Collatz2.Word.oddSteps F.upperExponentWord := by
    rw [F.upperExponentWord_oddSteps]
    exact F.one_lt_edge_oddTotal_of_two_lt_upperWord_length hLen
  have hLeft := F.three_mul_upperNormalizedDefectNat_lt_affineRatio
  have hRight :=
    F.upperExponentWord_firstCrossing.three_mul_affineConst_div_threePow_lt_discounted hm
  exact lt_trans hLeft hRight

end FirstFailureEdge
end CSTMicro
end Collatz2
