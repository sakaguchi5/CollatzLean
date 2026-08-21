import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalResidualFloor
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalOneShortPower

set_option linter.style.emptyLine false
/-!
# exact BHZ one-short selector

完全 square だけを選ぶと最悪 case で `q_(k+2)` scale まで進む。
しかし BHZ Proposition 3.3 の exact numerator と residual floor

  q_(j-1)-1 <= S_j

を組み合わせると、一文字だけ短い periodic prefix なら

  q_k <= r <= 2*q_(k+1)

の範囲で必ず見つかる。

場合分けは次の通り。

* standard(k) が square ならそのまま使う。
* standard(k+1) が square ならそのまま使う。
* 両方失敗すると defect_(k+2)=1 かつ defect_(k+3)>0。
  - a_(k+2)>=2 なら semistandard(k+2) が `2r-1` まで periodic。
  - a_(k+2)=1 なら standard(k+2) が `2q_(k+2)-1` まで periodic。

最後の case では recurrence により

  q_(k+2)=q_(k+1)+q_k <= 2*q_(k+1)

なので二段先の denominator growth は不要になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- index 2 以降では `q_k>=2`。 -/
theorem criticalBHZq_ge_two
    {k : ℕ}
    (hk : 2 ≤ k) :
    2 ≤ criticalBHZq k := by
  have hMono :=
    criticalBHZq_mono_from_one
      (i := 2) (j := k) (by omega) hk
  rw [criticalBHZq_two] at hMono
  exact hMono

/--
二つの consecutive standard failure の後、defect 1 の semistandard root は
`q_(k+1)+q_k` になる。
-/
theorem bhzCriticalSemistandardRoot_add_two_eq_q_add
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k)
    (hDef : bhzCriticalDigitDefect P (k + 2) = 1) :
    bhzCriticalSemistandardRoot P (k + 2) =
      criticalBHZq (k + 1) + criticalBHZq k := by
  have hDigitLe := P.digit_le_a (k + 2)
  have hRoot :=
    bhzCriticalSemistandardRoot_eq_residual_recurrence
      P (by omega) hDigitLe
  have hDefRaw :
      criticalBHZa (k + 2) - P.digit (k + 2) = 1 := by
    simpa [bhzCriticalDigitDefect] using hDef
  have hPred1 : k + 2 - 1 = k + 1 := by omega
  have hPred2 : k + 2 - 2 = k := by omega
  rw [hDefRaw, hPred1, hPred2] at hRoot
  simpa [one_mul] using hRoot

/--
`a_(k+2)=1` の場合の BHZ denominator recurrence。
-/
theorem criticalBHZq_add_two_eq_q_add_of_a_one
    {k : ℕ}
    (hk : 2 ≤ k)
    (hAOne : criticalBHZa (k + 2) = 1) :
    criticalBHZq (k + 2) =
      criticalBHZq (k + 1) + criticalBHZq k := by
  have hRec :=
    criticalBHZq_recurrence
      (k := k + 2) (by omega)

  have hPred1 :
      k + 2 - 1 = k + 1 := by
    omega
  have hPred2 :
      k + 2 - 2 = k := by
    omega

  rw [hAOne, hPred1, hPred2] at hRec
  simpa [one_mul] using hRec

/--
`a_(k+2)=1`, `defect_(k+2)=1` の場合、
一段前の residual floor を `q_(k+2)-1` まで持ち上げる。
-/
theorem bhzCriticalResidual_add_two_ge_q_add_two_sub_one
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k)
    (hDef :
      bhzCriticalDigitDefect P (k + 2) = 1)
    (hAOne :
      criticalBHZa (k + 2) = 1)
    (hFloor :
      criticalBHZq k - 1 ≤
        bhzCriticalResidualBudget P (k + 1)) :
    criticalBHZq (k + 2) - 1 ≤
      bhzCriticalResidualBudget P (k + 2) := by
  have hRec :=
    bhzCriticalResidualBudget_succ P (k + 1)

  have hStep :
      k + 1 + 1 = k + 2 := by
    omega

  rw [hStep, hDef] at hRec
  simp only [one_mul] at hRec

  have hQRec :
      criticalBHZq (k + 2) =
        criticalBHZq (k + 1) + criticalBHZq k :=
    criticalBHZq_add_two_eq_q_add_of_a_one
      hk hAOne

  rw [hRec, hQRec]
  omega

/--
現在の residual が `q_k-1` 以上で、次の defect が positive なら、
次の residual は `2q_k-1` 以上。
-/
theorem bhzCriticalResidual_succ_ge_two_q_sub_one
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hFloor :
      criticalBHZq k - 1 ≤
        bhzCriticalResidualBudget P k)
    (hDefNextPos :
      0 < bhzCriticalDigitDefect P (k + 1)) :
    2 * criticalBHZq k - 1 ≤
      bhzCriticalResidualBudget P (k + 1) := by
  have hRec :=
    bhzCriticalResidualBudget_succ P k

  have hOne :
      1 ≤ bhzCriticalDigitDefect P (k + 1) := by
    omega

  have hTerm :
      criticalBHZq k ≤
        bhzCriticalDigitDefect P (k + 1) *
          criticalBHZq k := by
    simpa [one_mul] using
      Nat.mul_le_mul_right
        (criticalBHZq k) hOne

  rw [hRec]
  omega

/--
次段 residual 自体が `2q_k-1` を覆えば、
standard candidate は自動的に one-short eligible。
indicator の寄与は非負なので不要。
-/
theorem bhzCriticalStandardOneShortEligible_of_residual
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hResidual :
      2 * criticalBHZq k - 1 ≤
        bhzCriticalResidualBudget P (k + 1)) :
    BHZStandardOneShortEligible P k := by
  unfold BHZStandardOneShortEligible
  unfold bhzCriticalStandardRoot
  unfold bhzCriticalStandardPowerNumerator
  omega

/--
`defect_(k+2)=1` かつ `a_(k+2)≥2` なら、
一段前の residual floor から semistandard one-short eligibility を得る。
-/
theorem bhzCriticalSemistandardOneShortEligible_add_two
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k)
    (hALarge :
      2 ≤ criticalBHZa (k + 2))
    (hDef :
      bhzCriticalDigitDefect P (k + 2) = 1)
    (hFloor :
      criticalBHZq k - 1 ≤
        bhzCriticalResidualBudget P (k + 1)) :
    BHZSemistandardOneShortEligible P (k + 2) := by
  have hDigitLe :=
    P.digit_le_a (k + 2)

  have hDefRaw :
      criticalBHZa (k + 2) - P.digit (k + 2) = 1 := by
    simpa [bhzCriticalDigitDefect] using hDef

  have hDigitPos :
      0 < P.digit (k + 2) := by
    omega

  have hDigitLt :
      P.digit (k + 2) < criticalBHZa (k + 2) := by
    omega

  have hRootEq :=
    bhzCriticalSemistandardRoot_add_two_eq_q_add
      P hk hDef

  have hRec :=
    bhzCriticalResidualBudget_succ P (k + 1)

  have hStep :
      k + 1 + 1 = k + 2 := by
    omega

  rw [hStep, hDef] at hRec
  simp only [one_mul] at hRec

  have hOneShortLen :
      2 * bhzCriticalSemistandardRoot P (k + 2) - 1 ≤
        bhzCriticalSemistandardPowerNumerator P (k + 2) := by
    unfold bhzCriticalSemistandardPowerNumerator
    rw [hRootEq, hRec]
    omega

  exact
    ⟨hDigitPos, hDigitLt, hOneShortLen⟩

/--
exact local one-short selector。
Rhin はまだ使わない。
-/
theorem actualBHZCritical_exists_oneShort_between_q_and_two_q_add_one
    {s k : ℕ}
    (P : CriticalBHZPhasePacket s)
    (hk : 2 ≤ k) :
    ∃ r : ℕ,
      criticalBHZq k ≤ r ∧
      r ≤ 2 * criticalBHZq (k + 1) ∧
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
