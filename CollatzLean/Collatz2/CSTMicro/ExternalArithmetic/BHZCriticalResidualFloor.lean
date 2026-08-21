import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalDigitResidualArithmetic

/-!
# BHZ residual budget の universal lower floor

complementary Ostrowski budget

  S_k = Σ_{j=1}^k (a_j-c_j) q_(j-1)

には admissibility だけから

  q_(k-1) - 1 <= S_k

という universal lower floor がある。

直観的には、ある digit が maximal なら一つ前の digit が 0 に強制されるため、
complementary digit 側では一つ前の recurrence contribution が丸ごと復活する。
この補題が「完全 square に一文字だけ足りない」最悪 case を定量化する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- `q_2=2`。小 index の residual floor を閉じるための明示値。 -/
theorem criticalBHZq_two :
    criticalBHZq 2 = 2 := by
  have hRec := criticalBHZq_recurrence (k := 2) (by omega)
  simpa [criticalBHZa_two] using hRec

/--
defect が 0 なら対応する digit は maximal。
-/
theorem bhzCriticalDigit_eq_a_of_defect_zero
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hDefZero : bhzCriticalDigitDefect P k = 0) :
    P.digit k = criticalBHZa k := by
  have hDigitLe := P.digit_le_a k
  have hALeDigit : criticalBHZa k ≤ P.digit k := by
    unfold bhzCriticalDigitDefect at hDefZero
    exact Nat.le_of_sub_eq_zero hDefZero
  omega

/--
`k = 2` における residual lower floor。
-/
theorem bhzCriticalResidualBudget_ge_q_pred_sub_one_two
    {s : ℕ}
    (P : CriticalBHZPhasePacket s) :
    criticalBHZq (2 - 1) - 1 ≤
      bhzCriticalResidualBudget P 2 := by
  simp [criticalBHZq_one]

/--
`k = 3` における residual lower floor。

`defect_3 > 0` なら第 3 項自身が `q_2` を供給する。
`defect_3 = 0` なら admissibility により digit 2 が 0 となり、
`defect_2 = 1` が一段前で floor を供給する。
-/
theorem bhzCriticalResidualBudget_ge_q_pred_sub_one_three
    {s : ℕ}
    (P : CriticalBHZPhasePacket s) :
    criticalBHZq (3 - 1) - 1 ≤
      bhzCriticalResidualBudget P 3 := by
  have hRec2 :
      bhzCriticalResidualBudget P 2 =
        bhzCriticalResidualBudget P 1 +
          bhzCriticalDigitDefect P 2 * criticalBHZq 1 := by
    simpa using bhzCriticalResidualBudget_succ P 1
  have hRec3 :
      bhzCriticalResidualBudget P 3 =
        bhzCriticalResidualBudget P 2 +
          bhzCriticalDigitDefect P 3 * criticalBHZq 2 := by
    simpa using bhzCriticalResidualBudget_succ P 2
  by_cases hDef3Pos : 0 < bhzCriticalDigitDefect P 3
  · have hOne :
        1 ≤ bhzCriticalDigitDefect P 3 := by
      omega
    have hTerm :
        criticalBHZq 2 ≤
          bhzCriticalDigitDefect P 3 * criticalBHZq 2 := by
      simpa [one_mul] using
        Nat.mul_le_mul_right (criticalBHZq 2) hOne
    have hQLeResidual :
        criticalBHZq 2 ≤
          bhzCriticalResidualBudget P 3 := by
      rw [hRec3]
      exact le_add_of_le_right hTerm
    have hPred :
        3 - 1 = 2 := by
      omega
    rw [hPred]
    omega
  · have hDef3 :
        bhzCriticalDigitDefect P 3 = 0 := by
      omega
    have hDigitEq :
        P.digit 3 = criticalBHZa 3 :=
      bhzCriticalDigit_eq_a_of_defect_zero P hDef3
    have hPred :
        P.digit 2 = 0 := by
      have h :=
        P.digit_pred_eq_zero_of_eq_max
          (k := 3) (by omega) hDigitEq
      simpa using h
    have hDef2 :
        bhzCriticalDigitDefect P 2 = 1 := by
      simp [
        bhzCriticalDigitDefect,
        hPred,
        criticalBHZa_two
      ]
    rw [hDef2] at hRec2
    rw [hDef3] at hRec3
    simp only [one_mul] at hRec2
    simp only [zero_mul, add_zero] at hRec3
    rw [criticalBHZq_two]
    simp [criticalBHZq_one] at hRec2
    omega

/--
現在の defect が positive なら、最新 residual term だけで
`q_(k-1)` を供給する。
-/
theorem bhzCriticalResidualBudget_ge_q_pred_sub_one_of_defect_pos
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k)
    (hDefPos : 0 < bhzCriticalDigitDefect P k) :
    criticalBHZq (k - 1) - 1 ≤
      bhzCriticalResidualBudget P k := by
  have hRec :=
    bhzCriticalResidualBudget_succ P (k - 1)
  have hPred :
      k - 1 + 1 = k := by
    omega
  rw [hPred] at hRec
  have hOne :
      1 ≤ bhzCriticalDigitDefect P k := by
    omega
  have hTerm :
      criticalBHZq (k - 1) ≤
        bhzCriticalDigitDefect P k *
          criticalBHZq (k - 1) := by
    simpa [one_mul] using
      Nat.mul_le_mul_right
        (criticalBHZq (k - 1)) hOne
  omega

/--
現在の defect が 0 の場合の induction step。

maximal digit の BHZ admissibility により一つ前の digit が 0 となる。
したがって一つ前の defect は `a_(k-1)` そのものであり、
`q` recurrence と `k-2` の induction hypothesis を合わせて
`q_(k-1)-1` の floor を得る。
-/
theorem bhzCriticalResidualBudget_ge_q_pred_sub_one_of_defect_zero
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 4 ≤ k)
    (hDefZero : bhzCriticalDigitDefect P k = 0)
    (hIH :
      criticalBHZq (k - 3) - 1 ≤
        bhzCriticalResidualBudget P (k - 2)) :
    criticalBHZq (k - 1) - 1 ≤
      bhzCriticalResidualBudget P k := by
  have hDigitEq :
      P.digit k = criticalBHZa k :=
    bhzCriticalDigit_eq_a_of_defect_zero P hDefZero
  have hPredDigit :
      P.digit (k - 1) = 0 := by
    exact
      P.digit_pred_eq_zero_of_eq_max
        (by omega) hDigitEq
  have hDefPred :
      bhzCriticalDigitDefect P (k - 1) =
        criticalBHZa (k - 1) := by
    simp [bhzCriticalDigitDefect, hPredDigit]
  have hRecK :=
    bhzCriticalResidualBudget_succ P (k - 1)
  have hRecPred :=
    bhzCriticalResidualBudget_succ P (k - 2)
  have hPredK :
      k - 1 + 1 = k := by
    omega
  have hPredPred :
      k - 2 + 1 = k - 1 := by
    omega
  rw [hPredK] at hRecK
  rw [hPredPred] at hRecPred
  rw [hDefZero] at hRecK
  rw [hDefPred] at hRecPred
  simp only [zero_mul, add_zero] at hRecK
  have hQRec :=
    criticalBHZq_recurrence
      (k := k - 1) (by omega)
  have hQPred1 :
      k - 1 - 1 = k - 2 := by
    omega
  have hQPred2 :
      k - 1 - 2 = k - 3 := by
    omega
  rw [hQPred1, hQPred2] at hQRec
  omega

/--
BHZ admissibility から得る complementary residual の universal lower floor。
-/
theorem bhzCriticalResidualBudget_ge_q_pred_sub_one
    {s : ℕ}
    (P : CriticalBHZPhasePacket s) :
    ∀ k : ℕ,
      2 ≤ k →
      criticalBHZq (k - 1) - 1 ≤
        bhzCriticalResidualBudget P k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk
      by_cases hk2 : k = 2
      · subst k
        exact
          bhzCriticalResidualBudget_ge_q_pred_sub_one_two P
      by_cases hk3 : k = 3
      · subst k
        exact
          bhzCriticalResidualBudget_ge_q_pred_sub_one_three P
      have hk4 : 4 ≤ k := by
        omega
      by_cases hDefPos :
          0 < bhzCriticalDigitDefect P k
      · exact
          bhzCriticalResidualBudget_ge_q_pred_sub_one_of_defect_pos
            P hk hDefPos
      · have hDefZero :
            bhzCriticalDigitDefect P k = 0 := by
          omega
        have hIH :=
          ih (k - 2) (by omega) (by omega)
        have hPred :
            k - 2 - 1 = k - 3 := by
          omega
        rw [hPred] at hIH
        exact
          bhzCriticalResidualBudget_ge_q_pred_sub_one_of_defect_zero
            P hk4 hDefZero hIH

end ExternalArithmetic
end CSTMicro
end Collatz2
