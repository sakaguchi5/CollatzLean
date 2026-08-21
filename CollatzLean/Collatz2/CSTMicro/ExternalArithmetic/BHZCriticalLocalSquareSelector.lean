import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalDigitResidualArithmetic

/-!
# Exact local BHZ square selector

BHZ Proposition 3.3 の exact standard / semistandard candidates と
Ostrowski admissibility だけから、任意 level `k>=2` に対して

  q_k ≤ r ≤ 2 q_(k+2)

を満たす actual square root `r` が存在することを示す。

重要な局所現象:

* standard(k) が square でない
    -> defect_(k+1) ≤ 1
    -> defect_(k+2) > 0;
* standard(k+1) も square でない
    -> defect_(k+2) = 1;
* standard(k+2) も square でない
    -> defect_(k+3) = 1 and defect_(k+4) > 0.

最後に `a_(k+3) >= 2` なら semistandard(k+3) が square。
`a_(k+3)=1` なら residual recurrence により standard(k+3) が square であり、
この場合 `q_(k+3)=q_(k+2)+q_(k+1) ≤ 2 q_(k+2)`。

従って local level gap は bounded である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- defect 1 が newest residual に `q_k` を丸ごと供給する。 -/
theorem bhzCriticalResidual_ge_q_of_next_defect_one
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hDef : bhzCriticalDigitDefect P (k + 1) = 1) :
    criticalBHZq k ≤ bhzCriticalResidualBudget P (k + 1) := by
  have h := bhzCriticalDefect_mul_q_le_residual P k
  rw [hDef] at h
  simpa using h

/-- three consecutive defect contributions give the lower bound used in the terminal case. -/
theorem bhzCriticalResidual_add_four_ge_two_q_add_three
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k)
    (hDef2 : bhzCriticalDigitDefect P (k + 2) = 1)
    (hDef3 : bhzCriticalDigitDefect P (k + 3) = 1)
    (hDef4 : 1 ≤ bhzCriticalDigitDefect P (k + 4))
    (hA3 : criticalBHZa (k + 3) = 1) :
    2 * criticalBHZq (k + 3) ≤
      bhzCriticalResidualBudget P (k + 4) := by
  have hS2 :
      bhzCriticalResidualBudget P (k + 2) =
        bhzCriticalResidualBudget P (k + 1) +
          bhzCriticalDigitDefect P (k + 2) * criticalBHZq (k + 1) := by
    simpa only [show k + 1 + 1 = k + 2 by omega] using
      bhzCriticalResidualBudget_succ P (k + 1)
  have hS3 :
      bhzCriticalResidualBudget P (k + 3) =
        bhzCriticalResidualBudget P (k + 2) +
          bhzCriticalDigitDefect P (k + 3) * criticalBHZq (k + 2) := by
    simpa only [show k + 2 + 1 = k + 3 by omega] using
      bhzCriticalResidualBudget_succ P (k + 2)
  have hS4 :
      bhzCriticalResidualBudget P (k + 4) =
        bhzCriticalResidualBudget P (k + 3) +
          bhzCriticalDigitDefect P (k + 4) * criticalBHZq (k + 3) := by
    simpa only [show k + 3 + 1 = k + 4 by omega] using
      bhzCriticalResidualBudget_succ P (k + 3)
  have hQrec :=
    criticalBHZq_recurrence (k := k + 3) (by omega)
  have hQmono :
      criticalBHZq (k + 1) ≤ criticalBHZq (k + 2) :=
    criticalBHZq_mono_from_one (by omega) (by omega)
  rw [hDef2] at hS2
  rw [hDef3] at hS3
  rw [hA3] at hQrec
  simp only [one_mul] at hS2 hS3 hQrec
  have hTerm4 :
      criticalBHZq (k + 3) ≤
        bhzCriticalDigitDefect P (k + 4) *
          criticalBHZq (k + 3) := by
    simpa [one_mul] using
      Nat.mul_le_mul_right (criticalBHZq (k + 3)) hDef4
  have hQPred1 : k + 3 - 1 = k + 2 := by omega
  have hQPred2 : k + 3 - 2 = k + 1 := by omega
  rw [hQPred1, hQPred2] at hQrec
  -- S_(k+2) already contains q_(k+1), then S_(k+3) adds q_(k+2),
  -- which is exactly q_(k+3) when a_(k+3)=1.  The next positive defect
  -- contributes one more q_(k+3).
  omega

/--
Exact local selector.  No Rhin estimate is used here.
-/
theorem actualBHZCritical_exists_square_between_q_and_two_q_add_two
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k) :
    ∃ r : ℕ,
      criticalBHZq k ≤ r ∧
      r ≤ 2 * criticalBHZq (k + 2) ∧
      CriticalBeattySquareAt s r := by
  by_cases hStd0 : BHZStandardSquareEligible P k
  · refine ⟨criticalBHZq k, le_rfl, ?_, ?_⟩
    · have hMono : criticalBHZq k ≤ criticalBHZq (k + 2) :=
        criticalBHZq_mono_from_one (by omega) (by omega)
      omega
    · simpa [bhzCriticalStandardRoot] using
        actualBHZCritical_standard_squareAt P (by omega) hStd0
  have hDef1Le : bhzCriticalDigitDefect P (k + 1) ≤ 1 :=
    bhzCriticalDefect_succ_le_one_of_not_standard P hStd0
  have hDef2Pos : 0 < bhzCriticalDigitDefect P (k + 2) :=
    bhzCriticalDefect_add_two_pos_of_not_standard P (by omega) hStd0
  by_cases hStd1 : BHZStandardSquareEligible P (k + 1)
  · refine ⟨criticalBHZq (k + 1), ?_, ?_, ?_⟩
    · exact criticalBHZq_mono_from_one (by omega) (by omega)
    · have hMono : criticalBHZq (k + 1) ≤ criticalBHZq (k + 2) :=
        criticalBHZq_mono_from_one (by omega) (by omega)
      omega
    · simpa [bhzCriticalStandardRoot] using
        actualBHZCritical_standard_squareAt P (by omega) hStd1
  have hDef2Le : bhzCriticalDigitDefect P (k + 2) ≤ 1 :=
    bhzCriticalDefect_succ_le_one_of_not_standard P hStd1
  have hDef2 : bhzCriticalDigitDefect P (k + 2) = 1 := by
    omega
  have hDef3Pos : 0 < bhzCriticalDigitDefect P (k + 3) :=
    bhzCriticalDefect_add_two_pos_of_not_standard P (by omega) hStd1
  by_cases hStd2 : BHZStandardSquareEligible P (k + 2)
  · refine ⟨criticalBHZq (k + 2), ?_, by omega, ?_⟩
    · exact criticalBHZq_mono_from_one (by omega) (by omega)
    · simpa [bhzCriticalStandardRoot] using
        actualBHZCritical_standard_squareAt P (by omega) hStd2
  have hDef3Le : bhzCriticalDigitDefect P (k + 3) ≤ 1 :=
    bhzCriticalDefect_succ_le_one_of_not_standard P hStd2
  have hDef3 : bhzCriticalDigitDefect P (k + 3) = 1 := by
    omega
  have hDef4Pos : 0 < bhzCriticalDigitDefect P (k + 4) :=
    bhzCriticalDefect_add_two_pos_of_not_standard P (by omega) hStd2
  have hDef4 : 1 ≤ bhzCriticalDigitDefect P (k + 4) := by omega
  have hA3Pos : 0 < criticalBHZa (k + 3) :=
    criticalBHZa_pos (by omega)
  by_cases hA3Large : 2 ≤ criticalBHZa (k + 3)
  · have hBudget :
        criticalBHZq (k + 1) ≤
          bhzCriticalResidualBudget P (k + 2) := by
      exact
        bhzCriticalResidual_ge_q_of_next_defect_one
          P hDef2
    have hSemi :
        BHZSemistandardSquareEligible P (k + 3) :=
      bhzCriticalSemistandardSquareEligible_of_defect_one
        P (by omega) hA3Large hDef3 hBudget
    let r : ℕ := bhzCriticalSemistandardRoot P (k + 3)
    have hDigitLe := P.digit_le_a (k + 3)
    have hRootEq :=
      bhzCriticalSemistandardRoot_eq_residual_recurrence
        P (by omega) hDigitLe
    have hPred1 : k + 3 - 1 = k + 2 := by omega
    have hPred2 : k + 3 - 2 = k + 1 := by omega
    have hDigitLe := P.digit_le_a (k + 3)
    have hRootEq :=
      bhzCriticalSemistandardRoot_eq_residual_recurrence
        P (by omega) hDigitLe
    have hDef3Raw :
        criticalBHZa (k + 3) - P.digit (k + 3) = 1 := by
      simpa [bhzCriticalDigitDefect] using hDef3
    have hPred1 : k + 3 - 1 = k + 2 := by omega
    have hPred2 : k + 3 - 2 = k + 1 := by omega
    rw [hDef3Raw, hPred1, hPred2] at hRootEq
    simp only [one_mul] at hRootEq
    have hQMono1 :
        criticalBHZq k ≤ criticalBHZq (k + 1) :=
      criticalBHZq_mono_from_one (by omega) (by omega)
    have hQMono2 :
        criticalBHZq (k + 1) ≤ criticalBHZq (k + 2) :=
      criticalBHZq_mono_from_one (by omega) (by omega)
    refine ⟨r, ?_, ?_, ?_⟩
    · dsimp [r]
      rw [hRootEq]
      omega
    · dsimp [r]
      rw [hRootEq]
      omega
    · dsimp [r]
      exact
        actualBHZCritical_semistandard_squareAt
          P (by omega) hSemi
  · have hA3 : criticalBHZa (k + 3) = 1 := by omega
    have hResidual :
        2 * criticalBHZq (k + 3) ≤
          bhzCriticalResidualBudget P (k + 4) :=
      bhzCriticalResidual_add_four_ge_two_q_add_three
        P hk hDef2 hDef3 hDef4 hA3
    have hStd3 : BHZStandardSquareEligible P (k + 3) := by
      unfold BHZStandardSquareEligible
      unfold bhzCriticalStandardRoot
      unfold bhzCriticalStandardPowerNumerator
      have hSucc : k + 3 + 1 = k + 4 := by omega
      rw [hSucc]
      calc
        2 * criticalBHZq (k + 3)
            ≤ bhzCriticalResidualBudget P (k + 4) :=
          hResidual
        _ ≤
            bhzCriticalNextMaxIndicator P (k + 3) *
                criticalBHZq (k + 3) +
              bhzCriticalResidualBudget P (k + 4) := by
          omega
    have hQrec :=
      criticalBHZq_recurrence (k := k + 3) (by omega)
    have hPred1 : k + 3 - 1 = k + 2 := by omega
    have hPred2 : k + 3 - 2 = k + 1 := by omega
    rw [hA3, hPred1, hPred2] at hQrec
    simp only [one_mul] at hQrec
    have hQMono0 :
        criticalBHZq k ≤ criticalBHZq (k + 3) :=
      criticalBHZq_mono_from_one (by omega) (by omega)
    have hQMono1 :
        criticalBHZq (k + 1) ≤ criticalBHZq (k + 2) :=
      criticalBHZq_mono_from_one (by omega) (by omega)
    refine ⟨criticalBHZq (k + 3), hQMono0, ?_, ?_⟩
    · omega
    · simpa [bhzCriticalStandardRoot] using
        actualBHZCritical_standard_squareAt P (by omega) hStd3

end ExternalArithmetic
end CSTMicro
end Collatz2
