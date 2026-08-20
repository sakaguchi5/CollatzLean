import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBRelativeShiftedDictionaryOdd

/-!
# Pure B relative bridge 4: even standard block の relative shifted dictionary

even branch は origin first-flat correction を持つため `0 < a` を仮定する。
既存 Stage 8B.3 の二つの shifted dictionary と prefix decomposition を比較すると、
odd branch と同じ relative raw identity

  2^(β(l)-β(a)) F[l,l+P_j](y)
    = 3^(l-a) F[a,a+P_j](y)
      + Γ_j F[a,l](y)

が exact に得られる。

absolute formula にあった `3^(l-1)` と `3^(a-1)` は比を取ることで `3^(l-a)` へ戻る。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- even corridor の positive phase でも interval gap は raw power gap。 -/
theorem criticalIntervalGapZ_add_currentP_eq_rawGap_of_even
    {j a : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (haPos : 0 < a)
    (hRange :
      a + criticalPowerP j <
        criticalPowerP (j + 1)) :
    criticalIntervalGapZ a (a + criticalPowerP j) =
      actualCriticalRawPowerGap j := by
  have hShift0 :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_even
      (j := j)
      (x := a)
      hj
      hjEven
      haPos
      (by omega :
        criticalPowerP j + a < criticalPowerP (j + 1))
  have hShift :
      beattyIndex (a + criticalPowerP j) =
        criticalPowerQ j + beattyIndex a := by
    rw [Nat.add_comm a (criticalPowerP j)]
    exact hShift0
  have hBeta :
      criticalPowerQ j + beattyIndex a - beattyIndex a =
        criticalPowerQ j := by
    omega
  have hLen :
      a + criticalPowerP j - a = criticalPowerP j := by
    omega
  unfold criticalIntervalGapZ actualCriticalRawPowerGap
  rw [hShift, hBeta, hLen]

/--
even standard block の relative shifted dictionary。
-/
theorem relativeShiftedDefectDictionary_of_even
    {j a l : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (haPos : 0 < a)
    (hal : a ≤ l)
    (hRange :
      l + criticalPowerP j <
        criticalPowerP (j + 1))
    (y : ℤ) :
    (2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
        criticalIntervalDefectZ
          l (l + criticalPowerP j) y =
      (3 : ℤ) ^ (l - a) *
          criticalIntervalDefectZ
            a (a + criticalPowerP j) y +
        actualCriticalRawPowerGap j *
          criticalIntervalDefectZ a l y := by
  have hlPos : 0 < l := by
    omega
  have hRangeA :
      a + criticalPowerP j <
        criticalPowerP (j + 1) := by
    omega
  have hA :=
    shiftedDefect_correctedDictionary_of_even
      (j := j)
      (l := a)
      hj
      hjEven
      haPos
      hRangeA
      y
  have hL :=
    shiftedDefect_correctedDictionary_of_even
      (j := j)
      (l := l)
      hj
      hjEven
      hlPos
      hRange
      y
  have hPrefix :=
    criticalPrefixDefectZ_endpoint_decomposition
      (a := a) (b := l) hal y
  have hBetaLe : beattyIndex a ≤ beattyIndex l := by
    by_cases hEq : a = l
    · subst l
      exact le_rfl
    · exact le_of_lt (beattyIndex_strictMono (by omega))
  have hBetaSplit :
      beattyIndex l =
        beattyIndex a + (beattyIndex l - beattyIndex a) := by
    omega
  have hTwoSplit :
      (2 : ℤ) ^ beattyIndex l =
        (2 : ℤ) ^ beattyIndex a *
          (2 : ℤ) ^ (beattyIndex l - beattyIndex a) := by
    rw [hBetaSplit, pow_add]
    simp
  have hThreePredExp :
      l - 1 = (l - a) + (a - 1) := by
    omega
  have hThreePredSplit :
      (3 : ℤ) ^ (l - 1) =
        (3 : ℤ) ^ (l - a) * (3 : ℤ) ^ (a - 1) := by
    rw [hThreePredExp, pow_add]
  have hScaled :
      (2 : ℤ) ^ beattyIndex a *
          ((2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
            criticalIntervalDefectZ
              l (l + criticalPowerP j) y) =
        (2 : ℤ) ^ beattyIndex a *
          ((3 : ℤ) ^ (l - a) *
              criticalIntervalDefectZ
                a (a + criticalPowerP j) y +
            actualCriticalRawPowerGap j *
              criticalIntervalDefectZ a l y) := by
    calc
      (2 : ℤ) ^ beattyIndex a *
          ((2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
            criticalIntervalDefectZ
              l (l + criticalPowerP j) y) =
        (2 : ℤ) ^ beattyIndex l *
          criticalIntervalDefectZ
            l (l + criticalPowerP j) y := by
              rw [hTwoSplit]
              ring
      _ =
        - (3 : ℤ) ^ (l - 1) * actualCorrectedChristoffelLinearForm j y +
          actualCriticalRawPowerGap j * criticalPrefixDefectZ l y := hL
      _ =
        (3 : ℤ) ^ (l - a) *
            (- (3 : ℤ) ^ (a - 1) * actualCorrectedChristoffelLinearForm j y +
              actualCriticalRawPowerGap j * criticalPrefixDefectZ a y) +
          actualCriticalRawPowerGap j *
            ((2 : ℤ) ^ beattyIndex a *
              criticalIntervalDefectZ a l y) := by
              rw [hPrefix, hThreePredSplit]
              ring
      _ =
        (3 : ℤ) ^ (l - a) *
            ((2 : ℤ) ^ beattyIndex a *
              criticalIntervalDefectZ
                a (a + criticalPowerP j) y) +
          actualCriticalRawPowerGap j *
            ((2 : ℤ) ^ beattyIndex a *
              criticalIntervalDefectZ a l y) := by
              rw [← hA]
      _ =
        (2 : ℤ) ^ beattyIndex a *
          ((3 : ℤ) ^ (l - a) *
              criticalIntervalDefectZ
                a (a + criticalPowerP j) y +
            actualCriticalRawPowerGap j *
              criticalIntervalDefectZ a l y) := by
              ring
  have hTwoNe : (2 : ℤ) ^ beattyIndex a ≠ 0 :=
    pow_ne_zero _ (by norm_num : (2 : ℤ) ≠ 0)
  exact mul_left_cancel₀ hTwoNe hScaled

end ExternalArithmetic
end CSTMicro
end Collatz2
