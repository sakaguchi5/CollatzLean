import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBRelativeSuffixFullDepth

/-!
# Pure B relative bridge 2: arbitrary parameter の endpoint-state identity

integral critical tail の state transport を、任意 parameter `Y` の interval defectへ戻す。

  F[s,t](Y)
    = 3^(t-s) (Y-Z_s)
      - 2^(β(t)-β(s)) (Y-Z_t).

`Y = Z_s` / `Y = Z_t` の既存二公式を一つにまとめる形であり、後段では
relative shifted block の parameter を canonical start state へ collapse する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/--
integral tail 上の interval defect を両 endpoint state から読む exact identity。
-/
theorem criticalIntervalDefectZ_eq_endpointStateDifference
    (P : PureBProfileObstruction)
    {a s t : ℕ}
    (A : IsIntegralCriticalTail P a)
    (has : a ≤ s)
    (hst : s ≤ t)
    (htm : t ≤ P.m)
    (Y : ℤ) :
    criticalIntervalDefectZ s t Y =
      (3 : ℤ) ^ (t - s) *
          (Y -
            P.integralCriticalTailStateInt A s has (by omega)) -
        (2 : ℤ) ^ (beattyIndex t - beattyIndex s) *
          (Y -
            P.integralCriticalTailStateInt A t (by omega) htm) := by
  let r := t - s
  have hsr : s + r = t := by
    dsimp [r]
    omega
  have hend : s + r ≤ P.m := by
    rw [hsr]
    exact htm
  have hRight0 :=
    P.criticalIntervalDefectZ_at_integralRightState
      (A := A)
      (s := s)
      (r := r)
      has
      hend
  have hat : a ≤ t :=
    le_trans has hst
  have hsm : s ≤ P.m :=
    le_trans hst htm
  have hRight :
      criticalIntervalDefectZ s t
          (P.integralCriticalTailStateInt A t hat htm) =
        (3 : ℤ) ^ (t - s) *
          (P.integralCriticalTailStateInt A t hat htm -
            P.integralCriticalTailStateInt A s has hsm) := by
    simpa [hsr, r] using hRight0
  calc
    criticalIntervalDefectZ s t Y =
        criticalIntervalDefectZ s t
            (P.integralCriticalTailStateInt A t (by omega) htm) -
          criticalIntervalGapZ s t *
            (Y -
              P.integralCriticalTailStateInt A t (by omega) htm) := by
      unfold criticalIntervalDefectZ
      ring
    _ =
        (3 : ℤ) ^ (t - s) *
            (Y -
              P.integralCriticalTailStateInt A s has (by omega)) -
          (2 : ℤ) ^ (beattyIndex t - beattyIndex s) *
            (Y -
              P.integralCriticalTailStateInt A t (by omega) htm) := by
      rw [hRight]
      unfold criticalIntervalGapZ
      ring

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
