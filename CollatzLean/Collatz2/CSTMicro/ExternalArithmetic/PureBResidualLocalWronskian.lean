import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ExtendedCriticalBeattyPhaseShift
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBShiftedWronskianElimination

/-!
# Pure B Stage 8R bridge: residual local Wronskian

`ExtendedCriticalBeattyPhaseShift` により、positive phase

  0 < a < P_(j+1)

では current / next standard block の Beatty rise がそれぞれ exact に

  beta(a+P_j)     - beta(a) = Q_j,
  beta(a+P_(j+1)) - beta(a) = Q_(j+1)

となる。

本ファイルでは、この広い phase window 上で local interval numerator / gap を直接持ち、
隣接二 block の local Wronskian

  Wloc(a,j)
    = Gamma_(j+1) Phi[a,a+P_j]
        - Gamma_j Phi[a,a+P_(j+1)]

を live object として定義する。

核心は一セル移動則

  2^(beta(a+1)-beta(a)) Wloc(a+1,j) = 3 Wloc(a,j).

狭い旧 corridor は `a=1` の anchor を得るために一度だけ使い、
その後はこの一セル移動則だけで

  2^beta(a) Wloc(a,j)
    = 3^(a-1) Wcorr_j

を `0<a<P_(j+1)` 全体へ延長する。
corrected Wronskian は exact に signed pure power

  Wcorr_j = +/- 2^S_j,
  S_j = Q_j + Q_(j+1) - 1

なので、最終的に

  2^(S_j-beta(a)) | Wloc(a,j)

が corridor-free な local residual precision として得られる。

このファイルは Pure B obstruction 自体には依存しない。
次段で integral tail endpoint-state identity と合成し、Stage 8R の
`hRangeJ / hRangeNext` を除去するための pure local arithmetic bridge である。
-/

-/
namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. live local block objects -/

/-- phase `a` から scale `j` の standard length `P_j` を読む local numerator。 -/
def residualLocalBlockNumerator
    (a j : ℕ) : ℤ :=
  criticalIntervalPhiZ a (a + criticalPowerP j)

/-- phase `a` から scale `j` の standard length `P_j` を読む local power gap。 -/
def residualLocalBlockGap
    (a j : ℕ) : ℤ :=
  criticalIntervalGapZ a (a + criticalPowerP j)

/--
隣接 standard lengths `P_j, P_(j+1)` の local Wronskian。

符号順序は既存 `shiftedAdjacentCorrectedWronskianElimination` と揃える。
-/
def residualLocalAdjacentWronskian
    (a j : ℕ) : ℤ :=
  actualCriticalRawPowerGap (j + 1) *
      residualLocalBlockNumerator a j -
    actualCriticalRawPowerGap j *
      residualLocalBlockNumerator a (j + 1)

/-- 一セル interval の critical numerator は 1。 -/
theorem criticalIntervalPhiZ_oneCell
    (a : ℕ) :
    criticalIntervalPhiZ a (a + 1) = 1 := by
  unfold criticalIntervalPhiZ
  simp

/-! ## 2. extended phase window では local gap = canonical raw gap -/

/--
`0<a<P_(j+1)` では scale `j` の local gap は canonical raw gap そのもの。
-/
theorem residualLocalBlockGap_eq_rawGap
    {a j : ℕ}
    (hj : 9 ≤ j)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1)) :
    residualLocalBlockGap a j =
      actualCriticalRawPowerGap j := by
  have hRise :=
    actual_beattyIndex_currentP_rise_eq_Q_of_pos_lt_nextP
      (j := j) (x := a) hj haPos haLt
  unfold residualLocalBlockGap criticalIntervalGapZ
  rw [hRise]
  have hLen : a + criticalPowerP j - a = criticalPowerP j := by
    omega
  rw [hLen]
  rfl

/--
同じ `0<a<P_(j+1)` だけで next block の local gap も canonical raw gap になる。
-/
theorem residualLocalNextBlockGap_eq_rawGap
    {a j : ℕ}
    (hj : 9 ≤ j)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1)) :
    residualLocalBlockGap a (j + 1) =
      actualCriticalRawPowerGap (j + 1) := by
  have hRise :=
    actual_beattyIndex_nextP_rise_eq_nextQ_of_pos_lt_nextP
      (j := j) (x := a) hj haPos haLt
  unfold residualLocalBlockGap criticalIntervalGapZ
  rw [hRise]
  have hLen :
      a + criticalPowerP (j + 1) - a =
        criticalPowerP (j + 1) := by
    omega
  rw [hLen]
  rfl

/-! ## 3. local numerator の一セル transport -/

/--
positive next-numerator window 内で scale `r` block を一セル右へ動かす exact law。

  delta_a := beta(a+1)-beta(a)

と置くと

  2^delta_a Phi_(r)(a+1)
    = 3 Phi_(r)(a) + Gamma_r.

証明は `[a,a+P_r+1)` を

* `[a,a+P_r)` + final one-cell,
* initial one-cell + `[a+1,a+P_r+1)`

の二通りに cut し、extended Beatty rise `=Q_r` を代入するだけ。
-/
theorem residualLocalBlockNumerator_step
    {a r : ℕ}
    (hr : 9 ≤ r)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (r + 1)) :
    (2 : ℤ) ^ (beattyIndex (a + 1) - beattyIndex a) *
        residualLocalBlockNumerator (a + 1) r =
      3 * residualLocalBlockNumerator a r +
        actualCriticalRawPowerGap r := by
  let p := criticalPowerP r
  have hpPos : 0 < p := by
    dsimp [p]
    exact criticalPowerP_pos (by omega)
  have hRise :
      beattyIndex (a + p) - beattyIndex a =
        criticalPowerQ r := by
    dsimp [p]
    exact
      actual_beattyIndex_currentP_rise_eq_Q_of_pos_lt_nextP
        (j := r) (x := a) hr haPos haLt
  have hCutFinal :=
    criticalIntervalPhiZ_concat
      (a := a)
      (c := a + p)
      (b := a + p + 1)
      (by omega)
      (by omega)
  have hCutInitial :=
    criticalIntervalPhiZ_concat
      (a := a)
      (c := a + 1)
      (b := a + p + 1)
      (by omega)
      (by omega)
  have hFinalLen : a + p + 1 - (a + p) = 1 := by omega
  have hTailLen : a + p + 1 - (a + 1) = p := by omega
  have hCellStart : criticalIntervalPhiZ a (a + 1) = 1 :=
    criticalIntervalPhiZ_oneCell a
  have hCellEnd :
      criticalIntervalPhiZ (a + p) (a + p + 1) = 1 :=
    criticalIntervalPhiZ_oneCell (a + p)
  have hShiftedEnd :
      a + p + 1 = (a + 1) + p := by omega
  rw [hFinalLen, hCellEnd, hRise] at hCutFinal
  simp only [pow_one] at hCutFinal
  rw [hTailLen, hCellStart] at hCutInitial
  simp only [mul_one] at hCutInitial
  have hEq :
      3 * criticalIntervalPhiZ a (a + p) +
          (2 : ℤ) ^ criticalPowerQ r =
        (3 : ℤ) ^ p +
          (2 : ℤ) ^ (beattyIndex (a + 1) - beattyIndex a) *
            criticalIntervalPhiZ (a + 1) ((a + 1) + p) := by
    rw [← hShiftedEnd]
    linarith
  unfold residualLocalBlockNumerator actualCriticalRawPowerGap
  dsimp [p] at hEq ⊢
  linarith

/-! ## 4. local adjacent Wronskian の一セル transport -/

/--
local Wronskian では二つの numerator transport の gap cross-term が exact に消える。

  2^delta_a Wloc(a+1,j) = 3 Wloc(a,j).

必要な phase 条件は `0<a<P_(j+1)` だけ。
-/
theorem residualLocalAdjacentWronskian_step
    {a j : ℕ}
    (hj : 9 ≤ j)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1)) :
    (2 : ℤ) ^ (beattyIndex (a + 1) - beattyIndex a) *
        residualLocalAdjacentWronskian (a + 1) j =
      3 * residualLocalAdjacentWronskian a j := by
  have hJ :=
    residualLocalBlockNumerator_step
      (r := j) hj haPos haLt
  have hPNext :
      criticalPowerP (j + 1) < criticalPowerP (j + 2) :=
    criticalPowerP_strict_succ (r := j + 1) (by omega)
  have haLtNext : a < criticalPowerP (j + 2) :=
    lt_trans haLt hPNext
  have hN :=
    residualLocalBlockNumerator_step
      (r := j + 1) (by omega) haPos haLtNext
  have hJScaled :=
    congrArg
      (fun z : ℤ => actualCriticalRawPowerGap (j + 1) * z)
      hJ
  have hNScaled :=
    congrArg
      (fun z : ℤ => actualCriticalRawPowerGap j * z)
      hN
  unfold residualLocalAdjacentWronskian at ⊢
  ring_nf at hJScaled hNScaled ⊢
  linarith

/-! ## 5. phase 1 の corrected-Wronskian anchor -/

/--
`j>=9` では adjacent numerator gap は 1 より大きいので、phase `1` は旧 narrow
corridor の中に入る。
-/
theorem one_add_criticalPowerP_lt_next
    {j : ℕ}
    (hj : 9 ≤ j) :
    1 + criticalPowerP j < criticalPowerP (j + 1) := by
  have hSpec :=
    actualCriticalPartialQuotient_spec
      (r := j) (by omega : 2 ≤ j)
  have haOne :
      1 ≤ actualCriticalPartialQuotient j := by
    exact Nat.succ_le_iff.mpr hSpec.1
  have hPrevLower0 :=
    criticalPowerP_add_two_linear_lower (j - 3)
  have hPrevLower :
      2 ≤ criticalPowerP (j - 1) := by
    have hIdx : j - 3 + 2 = j - 1 := by omega
    rw [hIdx] at hPrevLower0
    omega
  have hMul :
      criticalPowerP j ≤
        actualCriticalPartialQuotient j * criticalPowerP j := by
    simpa [one_mul] using
      Nat.mul_le_mul_right (criticalPowerP j) haOne
  have hRec :
      criticalPowerP (j + 1) =
        criticalPowerP (j - 1) +
          actualCriticalPartialQuotient j * criticalPowerP j := by
    simpa using hSpec.2.1
  rw [hRec]
  omega

/-- phase `1` では既存 corrected shifted elimination が local Wronskian の anchor を与える。 -/
theorem residualLocalAdjacentWronskian_one_scaled
    {j : ℕ}
    (hj : 9 ≤ j) :
    (2 : ℤ) ^ beattyIndex 1 *
        residualLocalAdjacentWronskian 1 j =
      correctedChristoffelWronskianNext
        actualCriticalContinuedFractionData j := by
  have hRangeJ :
      1 + criticalPowerP j < criticalPowerP (j + 1) :=
    one_add_criticalPowerP_lt_next hj
  have hRangeNext :
      1 + criticalPowerP (j + 1) < criticalPowerP (j + 2) := by
    simpa only [show j + 1 + 1 = j + 2 by omega] using
      one_add_criticalPowerP_lt_next (j := j + 1) (by omega)
  have h :=
    shiftedAdjacentCorrectedWronskianElimination
      (j := j)
      (l := 1)
      hj
      (by omega)
      hRangeJ
      hRangeNext
      0
  simpa [
    residualLocalAdjacentWronskian,
    residualLocalBlockNumerator,
    criticalIntervalDefectZ
  ] using h

/-! ## 6. anchor から全 positive next-numerator window へ transport -/

/--
local Wronskian の scaled quantity は `0<a<P_(j+1)` 全域で exact。

  2^beta(a) Wloc(a,j)
    = 3^(a-1) Wcorr_j.

旧 corridor は theorem の仮定から完全に消えている。
-/
theorem residualLocalAdjacentWronskian_scaled_eq_corrected
    {a j : ℕ}
    (hj : 9 ≤ j)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1)) :
    (2 : ℤ) ^ beattyIndex a *
        residualLocalAdjacentWronskian a j =
      (3 : ℤ) ^ (a - 1) *
        correctedChristoffelWronskianNext
          actualCriticalContinuedFractionData j := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
      by_cases haOne : a = 1
      · subst a
        simpa using residualLocalAdjacentWronskian_one_scaled hj
      · have haTwo : 2 ≤ a := by omega
        let b := a - 1
        have hbPos : 0 < b := by
          dsimp [b]
          omega
        have hbLt : b < criticalPowerP (j + 1) := by
          dsimp [b]
          omega
        have hbA : b < a := by
          dsimp [b]
          omega
        have hIH := ih b hbA hbPos hbLt
        have hStep :=
          residualLocalAdjacentWronskian_step
            (a := b) (j := j) hj hbPos hbLt
        have hbSucc : b + 1 = a := by
          dsimp [b]
          omega
        rw [hbSucc] at hStep
        have hBetaMono : beattyIndex b ≤ beattyIndex a := by
          exact le_of_lt (beattyIndex_strictMono hbA)
        have hBetaSplit :
            beattyIndex a =
              beattyIndex b + (beattyIndex a - beattyIndex b) := by
          omega
        have hExp :
            a - 1 = (b - 1) + 1 := by
          dsimp [b]
          omega
        calc
          (2 : ℤ) ^ beattyIndex a *
                residualLocalAdjacentWronskian a j
              =
            (2 : ℤ) ^ beattyIndex b *
              ((2 : ℤ) ^ (beattyIndex a - beattyIndex b) *
                residualLocalAdjacentWronskian a j) := by
                  rw [hBetaSplit, pow_add]
                  ring_nf
                  simp
          _ =
            (2 : ℤ) ^ beattyIndex b *
              (3 * residualLocalAdjacentWronskian b j) := by
                  rw [hStep]
          _ =
            3 *
              ((2 : ℤ) ^ beattyIndex b *
                residualLocalAdjacentWronskian b j) := by
                  ring
          _ =
            3 *
              ((3 : ℤ) ^ (b - 1) *
                correctedChristoffelWronskianNext
                  actualCriticalContinuedFractionData j) := by
                  rw [hIH]
          _ =
            (3 : ℤ) ^ (a - 1) *
              correctedChristoffelWronskianNext
                actualCriticalContinuedFractionData j := by
                  rw [hExp, pow_succ]
                  ring

/-! ## 7. exact residual 2-adic precision -/

/-- positive phase window では `beta(a)` は strong precision 以下。 -/
theorem beattyIndex_le_strongPrecision_of_pos_lt_nextP
    {a j : ℕ}
    (hj : 9 ≤ j)
    (haLt : a < criticalPowerP (j + 1)) :
    beattyIndex a ≤
      actualCriticalContinuedFractionData.strongPrecision j := by
  have hBetaLt := beattyIndex_strictMono haLt
  have hmod : (j + 1) % 2 < 2 :=
    Nat.mod_lt (j + 1) (by decide)
  have hBetaLtQ : beattyIndex a < criticalPowerQ (j + 1) := by
    by_cases hOdd : (j + 1) % 2 = 1
    · have hEnd :=
        actual_beattyIndex_currentP_eq_Q_of_odd
          (j := j + 1) (by omega) hOdd
      rw [hEnd] at hBetaLt
      exact hBetaLt
    · have hEven : (j + 1) % 2 = 0 := by omega
      have hEnd :=
        actual_beattyIndex_currentP_eq_Q_pred_of_even
          (j := j + 1) (by omega) hEven
      rw [hEnd] at hBetaLt
      have hQPos := criticalPowerQ_pos (j + 1)
      omega
  have hStrong :
      actualCriticalContinuedFractionData.strongPrecision j =
        criticalPowerQ j + criticalPowerQ (j + 1) - 1 := by
    simp [actualCriticalContinuedFractionData]
  have hQPos := criticalPowerQ_pos j
  rw [hStrong]
  omega

/--
local Wronskian の exact signed form。

* even `j`: `-3^(a-1) 2^(S_j-beta(a))`
* odd  `j`: `+3^(a-1) 2^(S_j-beta(a))`

したがって phase loss は exact に `beta(a)` だけである。
-/
theorem residualLocalAdjacentWronskian_signed_residualPrecision
    {a j : ℕ}
    (hj : 9 ≤ j)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1)) :
    (j % 2 = 0 ∧
        residualLocalAdjacentWronskian a j =
          -(
            (3 : ℤ) ^ (a - 1) *
              (2 : ℤ) ^
                (actualCriticalContinuedFractionData.strongPrecision j -
                  beattyIndex a)
          )) ∨
      (j % 2 = 1 ∧
        residualLocalAdjacentWronskian a j =
          (3 : ℤ) ^ (a - 1) *
            (2 : ℤ) ^
              (actualCriticalContinuedFractionData.strongPrecision j -
                beattyIndex a)) := by
  have hScaled :=
    residualLocalAdjacentWronskian_scaled_eq_corrected
      (a := a) (j := j) hj haPos haLt
  have hBetaLe :=
    beattyIndex_le_strongPrecision_of_pos_lt_nextP
      (a := a) (j := j) hj haLt
  let t :=
    actualCriticalContinuedFractionData.strongPrecision j - beattyIndex a
  have hSplit :
      actualCriticalContinuedFractionData.strongPrecision j =
        beattyIndex a + t := by
    dsimp [t]
    omega
  have hTwoNe : (2 : ℤ) ^ beattyIndex a ≠ 0 := by
    positivity
  rcases
      actualCorrectedChristoffelWronskianNext_signed_strongPrecision
        hj with
    hEven | hOdd
  · left
    refine ⟨hEven.1, ?_⟩
    rw [hEven.2, hSplit, pow_add] at hScaled
    have hCancel :
        (2 : ℤ) ^ beattyIndex a *
            residualLocalAdjacentWronskian a j =
          (2 : ℤ) ^ beattyIndex a *
            (-((3 : ℤ) ^ (a - 1) * (2 : ℤ) ^ t)) := by
      calc
        (2 : ℤ) ^ beattyIndex a *
              residualLocalAdjacentWronskian a j
            =
          (3 : ℤ) ^ (a - 1) *
            (-((2 : ℤ) ^ beattyIndex a * (2 : ℤ) ^ t)) := hScaled
        _ =
          (2 : ℤ) ^ beattyIndex a *
            (-((3 : ℤ) ^ (a - 1) * (2 : ℤ) ^ t)) := by
              ring
    have hEq := mul_left_cancel₀ hTwoNe hCancel
    simpa [t] using hEq
  · right
    refine ⟨hOdd.1, ?_⟩
    rw [hOdd.2, hSplit, pow_add] at hScaled
    have hCancel :
        (2 : ℤ) ^ beattyIndex a *
            residualLocalAdjacentWronskian a j =
          (2 : ℤ) ^ beattyIndex a *
            ((3 : ℤ) ^ (a - 1) * (2 : ℤ) ^ t) := by
      calc
        (2 : ℤ) ^ beattyIndex a *
              residualLocalAdjacentWronskian a j
            =
          (3 : ℤ) ^ (a - 1) *
            ((2 : ℤ) ^ beattyIndex a * (2 : ℤ) ^ t) := hScaled
        _ =
          (2 : ℤ) ^ beattyIndex a *
            ((3 : ℤ) ^ (a - 1) * (2 : ℤ) ^ t) := by
              ring
    have hEq := mul_left_cancel₀ hTwoNe hCancel
    simpa [t] using hEq

/--
Stage 8R が直接使う divisibility form。

  2^(S_j-beta(a)) | Wloc(a,j).

これは old two-corridor hypotheses を一切持たない。
-/
theorem twoPow_residualPrecision_dvd_residualLocalAdjacentWronskian
    {a j : ℕ}
    (hj : 9 ≤ j)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1)) :
    (2 : ℤ) ^
        (actualCriticalContinuedFractionData.strongPrecision j - beattyIndex a) ∣
      residualLocalAdjacentWronskian a j := by
  rcases
      residualLocalAdjacentWronskian_signed_residualPrecision
        (a := a) (j := j) hj haPos haLt with
    hEven | hOdd
  · rw [hEven.2]
    refine ⟨-((3 : ℤ) ^ (a - 1)), ?_⟩
    ring
  · rw [hOdd.2]
    refine ⟨(3 : ℤ) ^ (a - 1), ?_⟩
    ring

/-- local Wronskian は positive next-numerator window で nonzero。 -/
theorem residualLocalAdjacentWronskian_ne_zero
    {a j : ℕ}
    (hj : 9 ≤ j)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1)) :
    residualLocalAdjacentWronskian a j ≠ 0 := by
  rcases
      residualLocalAdjacentWronskian_signed_residualPrecision
        (a := a) (j := j) hj haPos haLt with
    hEven | hOdd
  · rw [hEven.2]
    apply neg_ne_zero.mpr
    exact
      mul_ne_zero
        (pow_ne_zero _
          (by norm_num : (3 : ℤ) ≠ 0))
        (pow_ne_zero _
          (by norm_num : (2 : ℤ) ≠ 0))
  · rw [hOdd.2]
    exact
      mul_ne_zero
        (pow_ne_zero _
          (by norm_num : (3 : ℤ) ≠ 0))
        (pow_ne_zero _
          (by norm_num : (2 : ℤ) ≠ 0))

end ExternalArithmetic
end CSTMicro
end Collatz2
