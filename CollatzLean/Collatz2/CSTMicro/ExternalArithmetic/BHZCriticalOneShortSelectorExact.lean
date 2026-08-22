import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalOneShortSelector

set_option linter.style.emptyLine false

/-!
# BHZ one-short selector の exact denominator bound

既存の one-short selector は、任意の phase と level `k >= 2` に対して

  q_k <= r <= 2 * q_(k+1)

を満たす one-short square root を返す。

しかし証明中で実際に現れる root は

* `q_k`,
* `q_(k+1)`,
* `q_k + q_(k+1)`

のいずれかである。したがって最後に単調性を使って `2*q_(k+1)` へ
丸める必要はない。本ファイルでは既存の case split をそのまま保ち、

  r <= q_k + q_(k+1)

という exact な上界を public theorem として取り出す。

Rhin の denominator growth はここでは一切使わない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
任意 phase の actual critical Sturmian word に対する exact local one-short selector。

既存証明の各場合で選ばれる root をそのまま保持することで、
`2*q_(k+1)` への粗い丸めを避ける。
-/
theorem actualBHZCritical_exists_oneShort_between_q_and_q_add_q_succ
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k) :
    ∃ r : ℕ,
      criticalBHZq k ≤ r ∧
      r ≤ criticalBHZq k + criticalBHZq (k + 1) ∧
      CriticalBeattyOneShortSquareAt s r := by
  have hQkTwo :
      2 ≤ criticalBHZq k :=
    criticalBHZq_ge_two hk

  have hQMono :
      criticalBHZq k ≤ criticalBHZq (k + 1) :=
    criticalBHZq_mono_from_one
      (by omega) (by omega)

  by_cases hStd0 :
      BHZStandardSquareEligible P k
  · have hSq :=
      actualBHZCritical_standard_squareAt
        P (by omega) hStd0

    refine
      ⟨criticalBHZq k, le_rfl, ?_, ?_⟩
    · omega
    · simpa [bhzCriticalStandardRoot] using
        hSq.toOneShort hQkTwo

  have hDef2Pos :
      0 < bhzCriticalDigitDefect P (k + 2) :=
    bhzCriticalDefect_add_two_pos_of_not_standard
      P (by omega) hStd0

  by_cases hStd1 :
      BHZStandardSquareEligible P (k + 1)
  · have hQ1Two :
        2 ≤ criticalBHZq (k + 1) :=
      criticalBHZq_ge_two (by omega)

    have hSq :=
      actualBHZCritical_standard_squareAt
        P (by omega) hStd1

    refine
      ⟨criticalBHZq (k + 1), hQMono, ?_, ?_⟩
    · omega
    · simpa [bhzCriticalStandardRoot] using
        hSq.toOneShort hQ1Two

  have hDef2Le :
      bhzCriticalDigitDefect P (k + 2) ≤ 1 :=
    bhzCriticalDefect_succ_le_one_of_not_standard
      P hStd1

  have hDef2 :
      bhzCriticalDigitDefect P (k + 2) = 1 := by
    omega

  have hDef3Pos :
      0 < bhzCriticalDigitDefect P (k + 3) :=
    bhzCriticalDefect_add_two_pos_of_not_standard
      P (by omega) hStd1

  have hResidualFloor :
      criticalBHZq k - 1 ≤
        bhzCriticalResidualBudget P (k + 1) := by
    simpa only [
      show k + 1 - 1 = k by omega
    ] using
      bhzCriticalResidualBudget_ge_q_pred_sub_one
        P (k + 1) (by omega)

  by_cases hALarge :
      2 ≤ criticalBHZa (k + 2)

  · have hEligible :
        BHZSemistandardOneShortEligible P (k + 2) :=
      bhzCriticalSemistandardOneShortEligible_add_two
        P hk hALarge hDef2 hResidualFloor

    have hRootEq :
        bhzCriticalSemistandardRoot P (k + 2) =
          criticalBHZq (k + 1) + criticalBHZq k :=
      bhzCriticalSemistandardRoot_add_two_eq_q_add
        P hk hDef2

    have hRootTwo :
        2 ≤ bhzCriticalSemistandardRoot P (k + 2) := by
      rw [hRootEq]
      have hPos :=
        criticalBHZq_pos (k + 1)
      omega

    have hOneShort :=
      actualBHZCritical_semistandard_oneShortSquareAt
        P (by omega) hRootTwo hEligible

    refine
      ⟨bhzCriticalSemistandardRoot P (k + 2),
        ?_, ?_, hOneShort⟩
    · rw [hRootEq]
      omega
    · rw [hRootEq]
      omega

  · have hAOne :
        criticalBHZa (k + 2) = 1 := by
      have hAPos :=
        criticalBHZa_pos
          (k := k + 2) (by omega)
      omega

    have hQRec :
        criticalBHZq (k + 2) =
          criticalBHZq (k + 1) + criticalBHZq k :=
      criticalBHZq_add_two_eq_q_add_of_a_one
        hk hAOne

    have hResidual2 :
        criticalBHZq (k + 2) - 1 ≤
          bhzCriticalResidualBudget P (k + 2) :=
      bhzCriticalResidual_add_two_ge_q_add_two_sub_one
        P hk hDef2 hAOne hResidualFloor

    have hResidual3 :
        2 * criticalBHZq (k + 2) - 1 ≤
          bhzCriticalResidualBudget P (k + 3) := by
      have h :=
        bhzCriticalResidual_succ_ge_two_q_sub_one
          P hResidual2 hDef3Pos
      simpa only [
        show k + 2 + 1 = k + 3 by omega
      ] using h

    have hEligible :
        BHZStandardOneShortEligible P (k + 2) := by
      apply
        bhzCriticalStandardOneShortEligible_of_residual
      simpa only [
        show k + 2 + 1 = k + 3 by omega
      ] using hResidual3

    have hRootTwo :
        2 ≤ bhzCriticalStandardRoot (k + 2) := by
      unfold bhzCriticalStandardRoot
      exact criticalBHZq_ge_two (by omega)

    have hOneShort :=
      actualBHZCritical_standard_oneShortSquareAt
        P (by omega) hRootTwo hEligible

    refine
      ⟨criticalBHZq (k + 2), ?_, ?_, ?_⟩
    · exact
        criticalBHZq_mono_from_one
          (by omega) (by omega)
    · rw [hQRec]
      omega
    · simpa [bhzCriticalStandardRoot] using
        hOneShort

end ExternalArithmetic
end CSTMicro
end Collatz2
