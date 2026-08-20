import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBEndpointStateDefect
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ShiftedCorrectedChristoffelDictionary

/-!
# Pure B relative bridge 3: odd standard block の relative shifted dictionary

既存 Stage 8B.3 の shifted corrected dictionary を start `a` と `l` の二箇所で比較する。
origin prefix defect を endpoint decomposition で消去すると、odd branch では

  2^(β(l)-β(a)) F[l,l+P_j](y)
    = 3^(l-a) F[a,a+P_j](y)
      + Γ_j F[a,l](y)

が exact に残る。

ここで `Γ_j = 2^Q_j - 3^P_j`。absolute shift `l` ではなく relative shift `l-a`
だけが 3-power に残ることが後段の要点。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- odd corridor 内では任意 positive/zero phase block の interval gap は raw power gap。 -/
theorem criticalIntervalGapZ_add_currentP_eq_rawGap_of_odd
    {j a : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hRange :
      a + criticalPowerP j <
        criticalPowerP (j + 1)) :
    criticalIntervalGapZ a (a + criticalPowerP j) =
      actualCriticalRawPowerGap j := by
  have hShift0 :=
    actual_beattyIndex_add_currentP_eq_add_Q_of_odd
      (j := j)
      (x := a)
      hj
      hjOdd
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
odd standard block の relative shifted dictionary。
-/
theorem relativeShiftedDefectDictionary_of_odd
    {j a l : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
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
  have hRangeA :
      a + criticalPowerP j <
        criticalPowerP (j + 1) := by
    omega
  have hA :=
    shiftedDefect_correctedDictionary_of_odd
      (j := j)
      (l := a)
      hj
      hjOdd
      hRangeA
      y
  have hL :=
    shiftedDefect_correctedDictionary_of_odd
      (j := j)
      (l := l)
      hj
      hjOdd
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
  have hThreeExp : l = (l - a) + a := by
    omega
  have hThreeSplit :
      (3 : ℤ) ^ l =
        (3 : ℤ) ^ (l - a) * (3 : ℤ) ^ a := by
    rw [hThreeExp, pow_add]
    simp
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
        (3 : ℤ) ^ l * actualCorrectedChristoffelLinearForm j y +
          actualCriticalRawPowerGap j * criticalPrefixDefectZ l y := hL
      _ =
        (3 : ℤ) ^ (l - a) *
            ((3 : ℤ) ^ a * actualCorrectedChristoffelLinearForm j y +
              actualCriticalRawPowerGap j * criticalPrefixDefectZ a y) +
          actualCriticalRawPowerGap j *
            ((2 : ℤ) ^ beattyIndex a *
              criticalIntervalDefectZ a l y) := by
              rw [hPrefix, hThreeSplit]
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
