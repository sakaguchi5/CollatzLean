import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ShiftedCorrectedChristoffelDictionary

/-!
# Pure B checkpoint: shifted consecutive blocks の corrected Wronskian elimination

同じ positive shift `l` から consecutive standard lengths `P_j`, `P_(j+1)` を読む。
Stage 8B.3 の odd/even corrected dictionary を交差消去すると、common prefix defect
`E_l(y)` は exact に消え、

  2^β(l) * [ Γ_(j+1) F_j(l,y) - Γ_j F_(j+1)(l,y) ]
    = 3^(l-1) * Wcorr_j

だけが残る。

従って standard aligned pair では arbitrary high 3-adic approximation を新たに
Baker/Yu で評価する必要はなく、valuation source は既存 corrected Wronskian に
既に exact に露出している。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- odd index では corrected Q は raw power gap の負。 -/
private theorem actualCorrectedQ_eq_neg_rawGap_of_odd
    {j : ℕ}
    (hjOdd : j % 2 = 1) :
    correctedChristoffelQ
        actualCriticalContinuedFractionData j =
      - actualCriticalRawPowerGap j := by
  rw [
    correctedChristoffelQ_odd
      actualCriticalContinuedFractionData hjOdd
  ]
  unfold actualCriticalRawPowerGap
  change
    (3 : ℤ) ^ criticalPowerP j -
        (2 : ℤ) ^ criticalPowerQ j =
      -(
        (2 : ℤ) ^ criticalPowerQ j -
          (3 : ℤ) ^ criticalPowerP j
      )
  ring


/-- even index では corrected Q は raw power gap の 3 倍。 -/
private theorem actualCorrectedQ_eq_three_mul_rawGap_of_even
    {j : ℕ}
    (hjEven : j % 2 = 0) :
    correctedChristoffelQ
        actualCriticalContinuedFractionData j =
      3 * actualCriticalRawPowerGap j := by
  rw [
    correctedChristoffelQ_even
      actualCriticalContinuedFractionData hjEven
  ]
  unfold actualCriticalRawPowerGap
  rfl

/--
shifted adjacent elimination の odd → even branch。

可変係数による linear combination は `congrArg` で明示的に作る。
-/
private theorem shiftedAdjacentCorrectedWronskianElimination_of_odd
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hl : 0 < l)
    (hjOdd : j % 2 = 1)
    (hRangeJ :
      l + criticalPowerP j <
        criticalPowerP (j + 1))
    (hRangeNext :
      l + criticalPowerP (j + 1) <
        criticalPowerP (j + 2))
    (y : ℤ) :
    (2 : ℤ) ^ beattyIndex l *
        (
          actualCriticalRawPowerGap (j + 1) *
              criticalIntervalDefectZ
                l (l + criticalPowerP j) y -
            actualCriticalRawPowerGap j *
              criticalIntervalDefectZ
                l (l + criticalPowerP (j + 1)) y
        ) =
      (3 : ℤ) ^ (l - 1) *
        correctedChristoffelWronskianNext
          actualCriticalContinuedFractionData j := by
  have hNextEven :
      (j + 1) % 2 = 0 := by
    have hmod :
        j % 2 < 2 :=
      Nat.mod_lt j (by decide)
    omega
  have hThree :
      (3 : ℤ) ^ l =
        (3 : ℤ) ^ (l - 1) * 3 := by
    have hExp :
        l = (l - 1) + 1 := by
      omega
    rw [hExp, pow_succ]
    simp
  have hJ :=
    shiftedDefect_correctedDictionary_of_odd
      hj hjOdd hRangeJ y
  have hNext :=
    shiftedDefect_correctedDictionary_of_even
      (j := j + 1)
      (l := l)
      (by omega)
      hNextEven
      hl
      (by
        simpa [Nat.add_assoc] using hRangeNext)
      y
  have hCross :=
    actualCorrectedChristoffelLinearForm_cross_eq_wronskian
      j y
  have hQJ :
      correctedChristoffelQ
          actualCriticalContinuedFractionData j =
        - actualCriticalRawPowerGap j :=
    actualCorrectedQ_eq_neg_rawGap_of_odd hjOdd
  have hQNext :
      correctedChristoffelQ
          actualCriticalContinuedFractionData (j + 1) =
        3 * actualCriticalRawPowerGap (j + 1) :=
    actualCorrectedQ_eq_three_mul_rawGap_of_even
      hNextEven
  rw [hQJ, hQNext] at hCross
  /-
  odd dictionary 側の 3^l を、
  common factor 3^(l-1) に揃える。
  -/
  rw [hThree] at hJ
  /-
  linear_combination に可変係数を渡さず、
  必要な三つの scaled equality を先に構成する。
  -/
  have hJScaled :=
    congrArg
      (fun z : ℤ =>
        actualCriticalRawPowerGap (j + 1) * z)
      hJ
  have hNextScaled :=
    congrArg
      (fun z : ℤ =>
        actualCriticalRawPowerGap j * z)
      hNext
  have hCrossScaled :=
    congrArg
      (fun z : ℤ =>
        (3 : ℤ) ^ (l - 1) * z)
      hCross
  /-
  ここではすでに必要な可変係数積は等式の中に入っている。
  ring_nf は積順序・分配だけを canonicalize し、
  linarith は三つの等式の固定係数線形結合だけを担当する。
  -/
  ring_nf at hJScaled hNextScaled hCrossScaled ⊢
  linarith

/--
shifted adjacent elimination の even → odd branch。
-/
private theorem shiftedAdjacentCorrectedWronskianElimination_of_even
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hl : 0 < l)
    (hjEven : j % 2 = 0)
    (hRangeJ :
      l + criticalPowerP j <
        criticalPowerP (j + 1))
    (hRangeNext :
      l + criticalPowerP (j + 1) <
        criticalPowerP (j + 2))
    (y : ℤ) :
    (2 : ℤ) ^ beattyIndex l *
        (
          actualCriticalRawPowerGap (j + 1) *
              criticalIntervalDefectZ
                l (l + criticalPowerP j) y -
            actualCriticalRawPowerGap j *
              criticalIntervalDefectZ
                l (l + criticalPowerP (j + 1)) y
        ) =
      (3 : ℤ) ^ (l - 1) *
        correctedChristoffelWronskianNext
          actualCriticalContinuedFractionData j := by
  have hNextOdd :
      (j + 1) % 2 = 1 := by
    have hmod :
        j % 2 < 2 :=
      Nat.mod_lt j (by decide)
    omega
  have hThree :
      (3 : ℤ) ^ l =
        (3 : ℤ) ^ (l - 1) * 3 := by
    have hExp :
        l = (l - 1) + 1 := by
      omega
    rw [hExp, pow_succ]
    simp
  have hJ :=
    shiftedDefect_correctedDictionary_of_even
      hj hjEven hl hRangeJ y
  have hNext :=
    shiftedDefect_correctedDictionary_of_odd
      (j := j + 1)
      (l := l)
      (by omega)
      hNextOdd
      (by
        simpa [Nat.add_assoc] using hRangeNext)
      y
  have hCross :=
    actualCorrectedChristoffelLinearForm_cross_eq_wronskian
      j y
  have hQJ :
      correctedChristoffelQ
          actualCriticalContinuedFractionData j =
        3 * actualCriticalRawPowerGap j :=
    actualCorrectedQ_eq_three_mul_rawGap_of_even
      hjEven
  have hQNext :
      correctedChristoffelQ
          actualCriticalContinuedFractionData (j + 1) =
        - actualCriticalRawPowerGap (j + 1) :=
    actualCorrectedQ_eq_neg_rawGap_of_odd
      hNextOdd
  rw [hQJ, hQNext] at hCross
  /-
  今度は next = odd 側が 3^l を持つ。
  -/
  rw [hThree] at hNext
  have hJScaled :=
    congrArg
      (fun z : ℤ =>
        actualCriticalRawPowerGap (j + 1) * z)
      hJ
  have hNextScaled :=
    congrArg
      (fun z : ℤ =>
        actualCriticalRawPowerGap j * z)
      hNext
  have hCrossScaled :=
    congrArg
      (fun z : ℤ =>
        (3 : ℤ) ^ (l - 1) * z)
      hCross
  ring_nf at hJScaled hNextScaled hCrossScaled ⊢
  linarith

/--
consecutive shifted standard blocks の
phase term を exact に消去した identity。
-/
theorem shiftedAdjacentCorrectedWronskianElimination
    {j l : ℕ}
    (hj : 9 ≤ j)
    (hl : 0 < l)
    (hRangeJ :
      l + criticalPowerP j <
        criticalPowerP (j + 1))
    (hRangeNext :
      l + criticalPowerP (j + 1) <
        criticalPowerP (j + 2))
    (y : ℤ) :
    (2 : ℤ) ^ beattyIndex l *
        (
          actualCriticalRawPowerGap (j + 1) *
              criticalIntervalDefectZ
                l (l + criticalPowerP j) y -
            actualCriticalRawPowerGap j *
              criticalIntervalDefectZ
                l (l + criticalPowerP (j + 1)) y
        ) =
      (3 : ℤ) ^ (l - 1) *
        correctedChristoffelWronskianNext
          actualCriticalContinuedFractionData j := by
  have hmod :
      j % 2 < 2 :=
    Nat.mod_lt j (by decide)
  by_cases hjOdd : j % 2 = 1
  · exact
      shiftedAdjacentCorrectedWronskianElimination_of_odd
        hj hl hjOdd hRangeJ hRangeNext y
  · have hjEven :
        j % 2 = 0 := by
      omega
    exact
      shiftedAdjacentCorrectedWronskianElimination_of_even
        hj hl hjEven hRangeJ hRangeNext y

end ExternalArithmetic
end CSTMicro
end Collatz2
