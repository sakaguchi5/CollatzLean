import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalPhasePeriodicity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CorrectedChristoffelWronskian

/-!
# Stage 8B.3: shifted interval -> corrected Christoffel linear form

任意 shifted standard-length blockを「Christoffel と同じ」と同一視しない。
Stage 8B.1/2 の exact phase corridor と Stage 3 concat lawを使い、shift dependence を
left endpoint prefix defectへ完全に押し込む。

L_j(y) := correctedP_j + correctedQ_j * y
Gamma_j := 2^Q_j - 3^P_j
E_l(y) := criticalPrefixDefectZ l y

とすると、corridor 内で

odd j:
  2^beta_l F[l,l+P_j](y)
    = 3^l L_j(y) + Gamma_j E_l(y)

even j, l>0:
  2^beta_l F[l,l+P_j](y)
    = -3^(l-1) L_j(y) + Gamma_j E_l(y).

同じ global parameter `y` が保たれるため、後段で corrected Wronskian を直接使える。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- actual corrected Christoffel affine linear form `P_j + Q_j*y`. -/
def actualCorrectedChristoffelLinearForm
    (j : ℕ)
    (y : ℤ) : ℤ :=
  correctedChristoffelP actualCriticalContinuedFractionData j +
    correctedChristoffelQ actualCriticalContinuedFractionData j * y

/-- actual raw power gap `Gamma_j = 2^Q_j - 3^P_j`. -/
def actualCriticalRawPowerGap
    (j : ℕ) : ℤ :=
  (2 : ℤ) ^ criticalPowerQ j -
    (3 : ℤ) ^ criticalPowerP j

/-- odd origin block defect is exactly the corrected linear form. -/
theorem criticalOriginDefect_eq_correctedLinearForm_of_odd
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (y : ℤ) :
    criticalIntervalDefectZ 0 (criticalPowerP j) y =
      actualCorrectedChristoffelLinearForm j y := by
  rw [← criticalPrefixDefectZ_eq_interval_zero]
  unfold criticalPrefixDefectZ criticalPrefixGapZ
    actualCorrectedChristoffelLinearForm
  rw [actual_criticalPrefixPhiZ_eq_christoffelPhiAt hj]
  rw [actual_beattyIndex_currentP_eq_Q_of_odd hj hjOdd]
  rw [correctedChristoffelP_odd actualCriticalContinuedFractionData hjOdd]
  rw [correctedChristoffelQ_odd actualCriticalContinuedFractionData hjOdd]
  ring_nf
  rfl

/-- even base positive phase `[1,P_j+1)` and corrected form are related exactly. -/
theorem two_mul_even_basePhaseDefect_eq_corrected
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hRange : criticalPowerP j + 1 < criticalPowerP (j + 1))
    (y : ℤ) :
    2 * criticalIntervalDefectZ
          1 (criticalPowerP j + 1) y =
      - actualCorrectedChristoffelLinearForm j y +
        actualCriticalRawPowerGap j *
          criticalPrefixDefectZ 1 y := by
  let P := criticalPowerP j
  let Q := criticalPowerQ j
  let phi := criticalChristoffelPhiAt actualCriticalContinuedFractionData j
  have hBeta1 : beattyIndex 1 = 1 := actual_beattyIndex_one_eq_one
  have hBetaP : beattyIndex P = Q - 1 := by
    dsimp [P, Q]
    exact actual_beattyIndex_currentP_eq_Q_pred_of_even hj hjEven
  have hBetaP1 : beattyIndex (P + 1) = Q + 1 := by
    have hShift :=
      actual_beattyIndex_add_currentP_eq_add_Q_of_even
        hj hjEven (by omega : 0 < 1) (by simpa [P] using hRange)
    rw [hBeta1] at hShift
    simpa [P, Q] using hShift
  have hPhiP : criticalPrefixPhiZ P = phi := by
    dsimp [P, phi]
    exact actual_criticalPrefixPhiZ_eq_christoffelPhiAt hj
  have hPhiOne : criticalPrefixPhiZ 1 = 1 :=
    criticalPrefixPhiZ_one_stage8
  have hOneCell : criticalIntervalPhiZ P (P + 1) = 1 :=
    criticalIntervalPhiZ_step_eq_one_stage8 P
  have hEndAtOne :=
    criticalPrefixPhiZ_endpoint_decomposition
      (a := 1) (b := P + 1) (by omega : 1 ≤ P + 1)
  have hEndAtP :=
    criticalPrefixPhiZ_endpoint_decomposition
      (a := P) (b := P + 1) (by omega : P ≤ P + 1)
  have hPhiBase :
      2 * criticalIntervalPhiZ 1 (P + 1) =
        3 * phi + (2 : ℤ) ^ (Q - 1) - (3 : ℤ) ^ P := by
    rw [hPhiOne, hBeta1] at hEndAtOne
    rw [hPhiP, hBetaP, hOneCell] at hEndAtP
    have hExpOne : P + 1 - 1 = P := by omega
    have hExpP : P + 1 - P = 1 := by omega
    rw [hExpOne] at hEndAtOne
    rw [hExpP] at hEndAtP
    norm_num at hEndAtOne hEndAtP
    have hEq :
        (3 : ℤ) ^ P + 2 * criticalIntervalPhiZ 1 (P + 1) =
          3 * phi + (2 : ℤ) ^ (Q - 1) :=
      hEndAtOne.symm.trans hEndAtP
    calc
      2 * criticalIntervalPhiZ 1 (P + 1) =
          ((3 : ℤ) ^ P + 2 * criticalIntervalPhiZ 1 (P + 1)) -
            (3 : ℤ) ^ P := by ring
      _ = (3 * phi + (2 : ℤ) ^ (Q - 1)) - (3 : ℤ) ^ P := by
        rw [hEq]
      _ = 3 * phi + (2 : ℤ) ^ (Q - 1) - (3 : ℤ) ^ P := by ring
  have hGapBase :
      criticalIntervalGapZ 1 (P + 1) =
        actualCriticalRawPowerGap j := by
    unfold criticalIntervalGapZ actualCriticalRawPowerGap
    rw [hBetaP1, hBeta1]
    have hBeta : Q + 1 - 1 = Q := by omega
    have hLen : P + 1 - 1 = P := by omega
    rw [hBeta, hLen]
  have hEOne : criticalPrefixDefectZ 1 y = 1 + y := by
    unfold criticalPrefixDefectZ criticalPrefixGapZ
    rw [hPhiOne, hBeta1]
    norm_num
  unfold criticalIntervalDefectZ
  rw [hGapBase, hEOne]
  unfold actualCorrectedChristoffelLinearForm actualCriticalRawPowerGap
  rw [correctedChristoffelP_even actualCriticalContinuedFractionData hjEven]
  rw [correctedChristoffelQ_even actualCriticalContinuedFractionData hjEven]
  -- actual CF data の p/q を current power P/Q に揃える。
  have hPActual :
      actualCriticalContinuedFractionData.p j = criticalPowerP j := by
    rfl
  have hQActual :
      actualCriticalContinuedFractionData.q j = criticalPowerQ j := by
    rfl
  rw [hPActual, hQActual]
  have hQPos : 0 < Q := by
    dsimp [Q]
    exact criticalPowerQ_pos j
  have hQSplit : Q = (Q - 1) + 1 := by
    omega
  have hTwoQ :
      (2 : ℤ) ^ Q = 2 * (2 : ℤ) ^ (Q - 1) := by
    rw [hQSplit, pow_succ]
    ring_nf
    simp
  dsimp [P, Q, phi] at hPhiBase hTwoQ ⊢
  rw [hTwoQ]
  linear_combination hPhiBase

/--
odd shifted standard block の exact corrected dictionary。
phase dependence は `Gamma_j * E_l(y)` のみに残る。
-/
theorem shiftedDefect_correctedDictionary_of_odd
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hRange : l + criticalPowerP j < criticalPowerP (j + 1))
    (y : ℤ) :
    (2 : ℤ) ^ beattyIndex l *
        criticalIntervalDefectZ
          l (l + criticalPowerP j) y =
      (3 : ℤ) ^ l * actualCorrectedChristoffelLinearForm j y +
        actualCriticalRawPowerGap j * criticalPrefixDefectZ l y := by
  let P := criticalPowerP j
  let Q := criticalPowerQ j
  have hLP : l + P = P + l := by omega
  have hRange' : P + l < criticalPowerP (j + 1) := by
    simpa [P, Nat.add_comm] using hRange
  have hConcatL :=
    criticalIntervalDefectZ_concat
      (a := 0) (c := l) (b := l + P)
      (by omega) (by omega) y
  have hConcatP :=
    criticalIntervalDefectZ_concat
      (a := 0) (c := P) (b := P + l)
      (by omega) (by omega) y
  have hOrigin :=
    criticalOriginDefect_eq_correctedLinearForm_of_odd hj hjOdd y
  have hPeriodic :=
    criticalIntervalDefectZ_shift_currentP_eq_of_odd
      hj hjOdd hRange' y
  have hBetaP := actual_beattyIndex_currentP_eq_Q_of_odd hj hjOdd
  rw [hLP] at hConcatL
  rw [hOrigin, hPeriodic, hBetaP] at hConcatP
  -- outer interval を prefix にする。
  rw [← criticalPrefixDefectZ_eq_interval_zero] at hConcatL
  -- RHS の interval [0,l) も prefix にする。
  rw [← criticalPrefixDefectZ_eq_interval_zero] at hConcatL
  -- hConcatP も同様に2 occurrence を変換する。
  rw [← criticalPrefixDefectZ_eq_interval_zero] at hConcatP
  rw [← criticalPrefixDefectZ_eq_interval_zero] at hConcatP
  have hExpL : P + l - l = P := by
    omega
  have hExpP : P + l - P = l := by
    omega
  simp only [hExpL, beattyIndex_zero, Nat.sub_zero] at hConcatL
  simp only [hExpP, beattyIndex_zero, Nat.sub_zero] at hConcatP
  have hEq :
      (3 : ℤ) ^ P * criticalPrefixDefectZ l y +
          (2 : ℤ) ^ beattyIndex l *
            criticalIntervalDefectZ l (P + l) y =
        (3 : ℤ) ^ l * actualCorrectedChristoffelLinearForm j y +
          (2 : ℤ) ^ Q * criticalPrefixDefectZ l y :=
    hConcatL.symm.trans hConcatP
  unfold actualCriticalRawPowerGap
  rw [hLP]
  dsimp [P, Q] at hEq ⊢
  linear_combination hEq

/--
even shifted standard block (`l>0`) の exact corrected dictionary。
origin first-flat blockだけはこの theorem の外に明示的に残す。
-/
theorem shiftedDefect_correctedDictionary_of_even
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hlPos : 0 < l)
    (hRange : l + criticalPowerP j < criticalPowerP (j + 1))
    (y : ℤ) :
    (2 : ℤ) ^ beattyIndex l *
        criticalIntervalDefectZ
          l (l + criticalPowerP j) y =
      - (3 : ℤ) ^ (l - 1) *
          actualCorrectedChristoffelLinearForm j y +
        actualCriticalRawPowerGap j * criticalPrefixDefectZ l y := by
  let P := criticalPowerP j
  let Q := criticalPowerQ j
  have hl : 1 ≤ l := by omega
  have hLP : l + P = P + l := by omega
  have hRange' : P + l < criticalPowerP (j + 1) := by
    simpa [P, Nat.add_comm] using hRange
  have hP1Range : P + 1 < criticalPowerP (j + 1) := by omega
  have hBeta1 : beattyIndex 1 = 1 := actual_beattyIndex_one_eq_one
  have hShiftP1 :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_even
      hj hjEven (by omega : 0 < 1) hP1Range
  rw [hBeta1] at hShiftP1
  have hBetaRise :
      beattyIndex (P + 1) - beattyIndex 1 = Q := by
    dsimp [P, Q] at hShiftP1 ⊢
    omega
  have hConcatL :=
    criticalIntervalDefectZ_concat
      (a := 1) (c := l) (b := P + l)
      hl (by omega) y
  have hConcatP1 :=
    criticalIntervalDefectZ_concat
      (a := 1) (c := P + 1) (b := P + l)
      (by omega) (by omega) y
  have hPeriodic :=
    criticalIntervalDefectZ_shift_currentP_pos_eq_of_even
      hj hjEven hl hRange' y
  rw [hPeriodic, hBetaRise] at hConcatP1
  have hBase :=
    two_mul_even_basePhaseDefect_eq_corrected
      hj hjEven hP1Range y
  have hPrefixSplit :=
    criticalPrefixDefectZ_endpoint_decomposition
      (a := 1) (b := l) hl y
  rw [hBeta1] at hPrefixSplit
  have hBetaDiff : beattyIndex l - beattyIndex 1 = beattyIndex l - 1 := by
    rw [hBeta1]
  rw [hBetaDiff] at hConcatL
  have hExpL : P + l - l = P := by omega
  have hExpP1 : P + l - (P + 1) = l - 1 := by omega
  rw [hExpL] at hConcatL
  rw [hExpP1] at hConcatP1
  have hEq :
      (3 : ℤ) ^ P * criticalIntervalDefectZ 1 l y +
          (2 : ℤ) ^ (beattyIndex l - 1) *
            criticalIntervalDefectZ l (P + l) y =
        (3 : ℤ) ^ (l - 1) *
            criticalIntervalDefectZ 1 (P + 1) y +
          (2 : ℤ) ^ Q * criticalIntervalDefectZ 1 l y :=
    hConcatL.symm.trans hConcatP1
  have hDouble :
      (2 : ℤ) ^ beattyIndex l *
          criticalIntervalDefectZ l (P + l) y =
        2 *
          ((2 : ℤ) ^ (beattyIndex l - 1) *
            criticalIntervalDefectZ l (P + l) y) := by
    have hBetaPos : 0 < beattyIndex l := by
      have h := beattyIndex_strictMono (a := 0) (b := l) hlPos
      simpa using h
    have hExp : beattyIndex l = (beattyIndex l - 1) + 1 := by omega
    rw [hExp, pow_succ]
    ring_nf
    simp
  rw [hLP]
  rw [hDouble]
  have hPrefix :
      criticalPrefixDefectZ l y =
        (3 : ℤ) ^ (l - 1) * criticalPrefixDefectZ 1 y +
          2 * criticalIntervalDefectZ 1 l y := by
    simpa using hPrefixSplit
  unfold actualCriticalRawPowerGap at hBase
  unfold actualCriticalRawPowerGap
  have hGamma :
      ((2 : ℤ) ^ Q - (3 : ℤ) ^ P) * criticalPrefixDefectZ l y =
        ((2 : ℤ) ^ Q - (3 : ℤ) ^ P) *
          ((3 : ℤ) ^ (l - 1) * criticalPrefixDefectZ 1 y +
            2 * criticalIntervalDefectZ 1 l y) := by
    rw [hPrefix]
  dsimp [P, Q] at hEq hBase hGamma ⊢
  linear_combination
    2 * hEq +
      (3 : ℤ) ^ (l - 1) * hBase -
      hGamma

/-- corrected linear forms の cross combination では common parameter `y` が消える。 -/
theorem actualCorrectedChristoffelLinearForm_cross_eq_wronskian
    (j : ℕ)
    (y : ℤ) :
    correctedChristoffelQ actualCriticalContinuedFractionData (j + 1) *
          actualCorrectedChristoffelLinearForm j y -
        correctedChristoffelQ actualCriticalContinuedFractionData j *
          actualCorrectedChristoffelLinearForm (j + 1) y =
      correctedChristoffelWronskianNext
        actualCriticalContinuedFractionData j := by
  unfold actualCorrectedChristoffelLinearForm
    correctedChristoffelWronskianNext
  ring

end ExternalArithmetic
end CSTMicro
end Collatz2
