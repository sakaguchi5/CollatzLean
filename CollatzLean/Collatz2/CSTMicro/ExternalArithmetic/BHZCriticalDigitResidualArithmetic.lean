import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalProposition33ActualStage
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerPGapGrowth14

/-!
# BHZ digit / residual arithmetic for the quantitative selector

このファイルでは published Proposition 3.3 自体には触れず、既に構成済みの
BHZ/Ostrowski phase packet から、局所 selector に必要な純算術だけを取り出す。

主な内容:

* `c_k ≤ a_k`;
* `c_k = a_k -> c_(k-1)=0`;
* residual budget の one-step recurrence;
* standard candidate が square でないなら
    `a_(k+1)-c_(k+1) ≤ 1`,
    `1 ≤ a_(k+2)-c_(k+2)`;
* defect が 1 で previous residual が十分なら semistandard candidate は square。

旧 uniform `C_BHZ` は使わない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

open scoped BigOperators

/-- BHZ partial quotient は index 2 以降 positive。 -/
theorem criticalBHZa_pos
    {k : ℕ}
    (hk : 2 ≤ k) :
    0 < criticalBHZa k := by
  rw [criticalBHZa_eq_actual hk]
  exact actualCriticalPartialQuotient_pos hk

namespace BHZCriticalPhaseExpansion

/-- base expansion の digit accessor。 -/
@[simp] theorem digit_base
    (s : ℕ)
    (h : s < criticalBHZq 2)
    (k : ℕ) :
    (BHZCriticalPhaseExpansion.base s h).digit k =
      if k = 2 then s else 0 := by
  simp [digit, digitsHigh, digitFromHigh]

/-- step expansion の digit accessor。 -/
@[simp] theorem digit_step
    {K s rem d : ℕ}
    (lower : BHZCriticalPhaseExpansion K rem)
    (hBound : s < criticalBHZq (K + 1))
    (hDec : s = rem + d * criticalBHZq K)
    (hDigit : d ≤ criticalBHZa (K + 1))
    (hMax :
      d = criticalBHZa (K + 1) →
        rem < criticalBHZq (K - 1))
    (k : ℕ) :
    (BHZCriticalPhaseExpansion.step
      lower hBound hDec hDigit hMax).digit k =
      if k = K + 1 then d else lower.digit k := by
  simp [digit, digitsHigh, digitFromHigh]

/-- expansion の全 digit は対応する partial quotient 以下。 -/
theorem digit_le_a
    {K s : ℕ}
    (E : BHZCriticalPhaseExpansion K s) :
    ∀ k : ℕ, E.digit k ≤ criticalBHZa k := by
  induction E with
  | base s hBound =>
      intro k
      by_cases hk2 : k = 2
      · subst k
        have hq2 : criticalBHZq 2 = 2 := by
          norm_num [
            criticalBHZq,
            criticalPowerP,
            criticalPowerConvergent,
            criticalInitialConvergent
          ]
        rw [hq2] at hBound
        simp [digit_base, criticalBHZa_two]
        omega
      · simp [digit_base, hk2]
  | @step K s rem d lower hBound hDec hDigit hMax ih =>
      intro k
      by_cases hkTop : k = K + 1
      · subst k
        simpa using hDigit
      · simpa [digit_step, hkTop] using ih k


/-- top index より上の digit は 0。 -/
theorem digit_eq_zero_of_top_lt
    {K s k : ℕ}
    (E : BHZCriticalPhaseExpansion K s)
    (hTop : K < k) :
    E.digit k = 0 := by
  unfold digit
  induction E generalizing k with
  | base t hb =>
      simp [digitsHigh, digitFromHigh]
      omega
  | @step J t rem d lower hb hdec hle hmax ih =>
      simp only [digitsHigh, digitFromHigh]
      have hNe : k ≠ J + 1 := by omega
      simp only [hNe, ↓reduceIte]
      exact ih (by omega)

/--
value が一つ前の weight より小さければ top digit は 0。
maximal digit admissibility を remainder から digit statement に戻す補助補題。
-/
theorem top_digit_eq_zero_of_lt_prev
    {K s : ℕ}
    (E : BHZCriticalPhaseExpansion K s)
    (hSmall : s < criticalBHZq (K - 1)) :
    E.digit K = 0 := by
  cases E with
  | base s hBound =>
      have hOne : criticalBHZq 1 = 1 := criticalBHZq_one
      have hs0 : s = 0 := by
        simpa [hOne] using hSmall
      simp [digit_base, hs0]
  | @step K s rem d lower hBound hDec hDigit hMax =>
      have hK : 2 ≤ K := lower.top_ge_two
      have hQPos : 0 < criticalBHZq K :=
        criticalBHZq_pos K
      have hSmall' : s < criticalBHZq K := by
        simpa only [show K + 1 - 1 = K by omega] using hSmall
      have hd0 : d = 0 := by
        by_contra hd
        have hdPos : 0 < d := Nat.pos_of_ne_zero hd
        have hOneLe : 1 ≤ d := by omega
        have hQLeMul :
            criticalBHZq K ≤ d * criticalBHZq K := by
          simpa [one_mul] using
            Nat.mul_le_mul_right (criticalBHZq K) hOneLe
        have hMulLeS : d * criticalBHZq K ≤ s := by
          rw [hDec]
          omega
        omega
      simp [digit_step, hd0]

/--
BHZ admissibility `c_k=a_k -> c_(k-1)=0`。
finite expansion constructor の `max_remainder` から内部証明する。
-/
theorem digit_pred_eq_zero_of_eq_max
    {K s : ℕ}
    (E : BHZCriticalPhaseExpansion K s) :
    ∀ {k : ℕ},
      2 ≤ k →
      E.digit k = criticalBHZa k →
      E.digit (k - 1) = 0 := by
  induction E with
  | base s hBound =>
      intro k hk hEq
      by_cases hk2 : k = 2
      · subst k
        simp only [Nat.add_one_sub_one, digit_one]
      · have hk3 : 3 ≤ k := by omega
        have hDigitZero :
            (BHZCriticalPhaseExpansion.base s hBound).digit k = 0 := by
          simp [digit_base, hk2]
        have hAPos : 0 < criticalBHZa k :=
          criticalBHZa_pos (by omega)
        rw [hDigitZero] at hEq
        omega
  | @step K s rem d lower hBound hDec hDigit hMax ih =>
      intro k hk hEq
      have hK : 2 ≤ K := lower.top_ge_two
      by_cases hkTop : k = K + 1
      · subst k
        have hdEq : d = criticalBHZa (K + 1) := by
          simpa [digit_step] using hEq
        have hRemSmall : rem < criticalBHZq (K - 1) :=
          hMax hdEq
        have hLowerTop : lower.digit K = 0 :=
          lower.top_digit_eq_zero_of_lt_prev hRemSmall
        have hPred : K + 1 - 1 = K := by omega
        rw [hPred]
        simp [digit_step, hLowerTop]
      · by_cases hkLe : k ≤ K
        · have hLowerEq : lower.digit k = criticalBHZa k := by
            simpa [digit_step, hkTop] using hEq
          have hLowerPred := ih hk hLowerEq
          have hPredNe : k - 1 ≠ K + 1 := by omega
          simpa [digit_step, hPredNe] using hLowerPred
        · have hkAbove : K + 1 < k := by omega
          have hDigitZero :
              (BHZCriticalPhaseExpansion.step
                lower hBound hDec hDigit hMax).digit k = 0 := by
            exact
              (BHZCriticalPhaseExpansion.step
                lower hBound hDec hDigit hMax).digit_eq_zero_of_top_lt
                  hkAbove
          have hAPos : 0 < criticalBHZa k :=
            criticalBHZa_pos (by omega)
          rw [hDigitZero] at hEq
          omega

end BHZCriticalPhaseExpansion

namespace CriticalBHZPhasePacket

/-- packet digit bound `c_k ≤ a_k`。 -/
theorem digit_le_a
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) :
    P.digit k ≤ criticalBHZa k := by
  unfold CriticalBHZPhasePacket.digit
  exact P.expansion.digit_le_a k

/-- packet-level BHZ admissibility。 -/
theorem digit_pred_eq_zero_of_eq_max
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    {k : ℕ}
    (hk : 2 ≤ k)
    (hEq : P.digit k = criticalBHZa k) :
    P.digit (k - 1) = 0 := by
  unfold CriticalBHZPhasePacket.digit at hEq ⊢
  exact P.expansion.digit_pred_eq_zero_of_eq_max hk hEq

end CriticalBHZPhasePacket

/-- complementary Ostrowski digit `a_k-c_k`。 -/
def bhzCriticalDigitDefect
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) : ℕ :=
  criticalBHZa k - P.digit k

/-- residual budget の one-step recurrence。 -/
theorem bhzCriticalResidualBudget_succ
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalResidualBudget P (k + 1) =
      bhzCriticalResidualBudget P k +
        bhzCriticalDigitDefect P (k + 1) * criticalBHZq k := by
  unfold bhzCriticalResidualBudget bhzCriticalDigitDefect
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
  simp only [show k + 1 - 1 = k by omega]

/-- newest residual term は全 residual budget 以下。 -/
theorem bhzCriticalDefect_mul_q_le_residual
    {s : ℕ}
    (P : CriticalBHZPhasePacket s)
    (k : ℕ) :
    bhzCriticalDigitDefect P (k + 1) * criticalBHZq k ≤
      bhzCriticalResidualBudget P (k + 1) := by
  rw [bhzCriticalResidualBudget_succ]
  omega

/-- `q_k` is monotone from BHZ index 1 onward. -/
theorem criticalBHZq_mono_from_one
    {i j : ℕ}
    (hi : 1 ≤ i)
    (hij : i ≤ j) :
    criticalBHZq i ≤ criticalBHZq j := by
  unfold criticalBHZq
  exact criticalPowerP_mono_from_two (by omega) (by omega)

/--
standard candidate が square でないなら次の defect は高々 1。
`a_(k+1)-c_(k+1) ≥ 2` なら residual の newest term だけで
二 root 分に達するため。
-/
theorem bhzCriticalDefect_succ_le_one_of_not_standard
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hNot : ¬ BHZStandardSquareEligible P k) :
    bhzCriticalDigitDefect P (k + 1) ≤ 1 := by
  by_contra h
  have hTwo : 2 ≤ bhzCriticalDigitDefect P (k + 1) := by omega
  have hQPos : 0 < criticalBHZq k := criticalBHZq_pos k
  have hTerm :
      2 * criticalBHZq k ≤
        bhzCriticalDigitDefect P (k + 1) * criticalBHZq k := by
    exact Nat.mul_le_mul_right (criticalBHZq k) hTwo
  have hResidual := bhzCriticalDefect_mul_q_le_residual P k
  have hEligible : BHZStandardSquareEligible P k := by
    unfold BHZStandardSquareEligible
    unfold bhzCriticalStandardRoot
    unfold bhzCriticalStandardPowerNumerator
    omega
  exact hNot hEligible

/--
standard candidate が square でないなら二つ先の defect は positive。
もし `c_(k+2)=a_(k+2)` なら admissibility で `c_(k+1)=0`。
indicator 1 と residual の `a_(k+1) q_k` が合わさって square になるため。
-/
theorem bhzCriticalDefect_add_two_pos_of_not_standard
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 1 ≤ k)
    (hNot : ¬ BHZStandardSquareEligible P k) :
    0 < bhzCriticalDigitDefect P (k + 2) := by
  by_contra hPos
  have hDefZero : bhzCriticalDigitDefect P (k + 2) = 0 := by omega
  have hDigitLe := P.digit_le_a (k + 2)
  have hALeDigit : criticalBHZa (k + 2) ≤ P.digit (k + 2) := by
    unfold bhzCriticalDigitDefect at hDefZero
    exact Nat.le_of_sub_eq_zero hDefZero
  have hDigitEq : P.digit (k + 2) = criticalBHZa (k + 2) := by
    omega
  have hPred : P.digit (k + 1) = 0 := by
    have h :=
      P.digit_pred_eq_zero_of_eq_max
        (k := k + 2) (by omega) hDigitEq
    simpa only [show k + 2 - 1 = k + 1 by omega] using h
  have hAPos : 0 < criticalBHZa (k + 1) :=
    criticalBHZa_pos (by omega)
  have hDefPrev :
      bhzCriticalDigitDefect P (k + 1) = criticalBHZa (k + 1) := by
    simp [bhzCriticalDigitDefect, hPred]
  have hOneLeDef : 1 ≤ bhzCriticalDigitDefect P (k + 1) := by
    rw [hDefPrev]
    omega
  have hTerm :
      criticalBHZq k ≤
        bhzCriticalDigitDefect P (k + 1) * criticalBHZq k := by
    simpa [one_mul] using
      Nat.mul_le_mul_right (criticalBHZq k) hOneLeDef
  have hResidual := bhzCriticalDefect_mul_q_le_residual P k
  have hIndicator : bhzCriticalNextMaxIndicator P k = 1 := by
    unfold bhzCriticalNextMaxIndicator
    simp [hDigitEq.symm]
  have hEligible : BHZStandardSquareEligible P k := by
    unfold BHZStandardSquareEligible
    unfold bhzCriticalStandardRoot
    unfold bhzCriticalStandardPowerNumerator
    rw [hIndicator]
    omega
  exact hNot hEligible

/--
defect 1 と previous residual `≥ q_(k-2)` から semistandard square eligibility。
`a_k≥2` により `0<c_k<a_k` も自動的に従う。
-/
theorem bhzCriticalSemistandardSquareEligible_of_defect_one
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k)
    (hA : 2 ≤ criticalBHZa k)
    (hDef : bhzCriticalDigitDefect P k = 1)
    (hBudget :
      criticalBHZq (k - 2) ≤
        bhzCriticalResidualBudget P (k - 1)) :
    BHZSemistandardSquareEligible P k := by
  have hDigitLe := P.digit_le_a k
  have hDigitPos : 0 < P.digit k := by
    unfold bhzCriticalDigitDefect at hDef
    omega
  have hDigitLt : P.digit k < criticalBHZa k := by
    unfold bhzCriticalDigitDefect at hDef
    omega
  have hRoot :=
    bhzCriticalSemistandardRoot_eq_residual_recurrence
      P hk hDigitLe
  have hResidualStep :=
    bhzCriticalResidualBudget_succ P (k - 1)
  have hPred : k - 1 + 1 = k := by omega
  rw [hPred] at hResidualStep
  have hDefRaw :
      criticalBHZa k - P.digit k = 1 := by
    simpa [bhzCriticalDigitDefect] using hDef
  have hRootBudget :
      bhzCriticalSemistandardRoot P k ≤
        bhzCriticalResidualBudget P k := by
    rw [hRoot, hResidualStep, hDefRaw, hDef]
    simp only [one_mul]
    calc
      criticalBHZq (k - 1) + criticalBHZq (k - 2) ≤
          criticalBHZq (k - 1) +
            bhzCriticalResidualBudget P (k - 1) :=
        Nat.add_le_add_left hBudget _
      _ =
          bhzCriticalResidualBudget P (k - 1) +
            criticalBHZq (k - 1) := by
        exact Nat.add_comm _ _
  refine ⟨hDigitPos, hDigitLt, ?_⟩
  unfold bhzCriticalSemistandardPowerNumerator
  omega

end ExternalArithmetic
end CSTMicro
end Collatz2
