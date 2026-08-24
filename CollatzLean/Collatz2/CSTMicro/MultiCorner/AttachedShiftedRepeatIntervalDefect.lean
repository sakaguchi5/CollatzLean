import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedRepeatIntervalDefectBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseScaledDifferenceShift

/-!
# Attached terminal-near repeat の end difference -> interval defect

既存 `scaledDifference_zero_eq_integralDefect_fused` は entrance difference `M_0` を扱う。
一方 terminal-near strategy で必要なのは repeated block の右端値 `M_m` である。

free-base identity

  M_m(i,j,Delta) = M_0(i+m,j+m,Delta)

を使い、shifted pair `(i+m,j+m)` に既存 interval-defect/fused formula を
そのまま適用する wrapper を固定する。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
repeated block の右端 scaled difference を、shifted pair における
integral critical interval defect と fused value へ exact に書き換える。
-/
theorem scaledDifference_end_eq_integralDefect_fused
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j m Delta : ℕ}
    (hij : i < j)
    (hjEnd : j + m < A.straightHenselWidth)
    (hBlock :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.SameDeltaOffsetBlock i j m Delta) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let iEnd := i + m
    let jEnd := j + m
    let p := jEnd - iEnd
    let a := A.straightHenselStart + iEnd
    let b := A.straightHenselStart + jEnd
    let I := P.criticalizationStart_spec
    let Z :=
      P.integralCriticalTailStateInt
        I a
        (by
          have hCrit := A.criticalization_le_previous
          dsimp [a, iEnd]
          unfold straightHenselStart
          omega)
        (by
          have hWidth := A.straightHenselStart_add_width
          have hcM := P.terminalCriticalStart_spec.1
          dsimp [a, iEnd]
          omega)
    (2 : ℤ) ^ p * C.scaledDifference i j Delta m =
      -((2 : ℤ) ^ C.delta iEnd) *
          criticalIntervalDefectZ a b Z -
        criticalIntervalGapZ a b *
          attachedCriticalFusedValue
            (C.delta iEnd) Z (C.qOne iEnd) := by
  dsimp at hBlock ⊢
  let C := A.toFreeBaseMonotoneHenselChain hStart
  let iEnd := i + m
  let jEnd := j + m
  have hijEnd : iEnd < jEnd := by
    dsimp [iEnd, jEnd]
    omega
  have hjEnd' : jEnd < A.straightHenselWidth := by
    simpa [jEnd] using hjEnd
  have hDeltaRaw := hBlock m le_rfl
  have hDelta :
      C.delta jEnd = C.delta iEnd + Delta := by
    dsimp [C, iEnd, jEnd]
    simpa [Nat.add_assoc] using hDeltaRaw
  have hCore :=
    A.scaledDifference_zero_eq_integralDefect_fused
      hStart
      (i := iEnd)
      (j := jEnd)
      (Delta := Delta)
      hijEnd
      hjEnd'
      hDelta
  dsimp [C, iEnd, jEnd] at hCore ⊢
  calc
    (2 : ℤ) ^ ((j + m) - (i + m)) *
        (A.toFreeBaseMonotoneHenselChain hStart).scaledDifference
          i j Delta m =
      (2 : ℤ) ^ ((j + m) - (i + m)) *
        (A.toFreeBaseMonotoneHenselChain hStart).scaledDifference
          (i + m) (j + m) Delta 0 := by
            rw [
              (A.toFreeBaseMonotoneHenselChain hStart).scaledDifference_eq_shifted_zero
                i j Delta m
            ]
    _ =
      -((2 : ℤ) ^
          (A.toFreeBaseMonotoneHenselChain hStart).delta (i + m)) *
          criticalIntervalDefectZ
            (A.straightHenselStart + (i + m))
            (A.straightHenselStart + (j + m))
            (P.integralCriticalTailStateInt
              P.criticalizationStart_spec
              (A.straightHenselStart + (i + m))
              (by
                have hCrit := A.criticalization_le_previous
                unfold straightHenselStart
                omega)
              (by
                have hWidth := A.straightHenselStart_add_width
                have hcM := P.terminalCriticalStart_spec.1
                omega)) -
        criticalIntervalGapZ
            (A.straightHenselStart + (i + m))
            (A.straightHenselStart + (j + m)) *
          attachedCriticalFusedValue
            ((A.toFreeBaseMonotoneHenselChain hStart).delta (i + m))
            (P.integralCriticalTailStateInt
              P.criticalizationStart_spec
              (A.straightHenselStart + (i + m))
              (by
                have hCrit := A.criticalization_le_previous
                unfold straightHenselStart
                omega)
              (by
                have hWidth := A.straightHenselStart_add_width
                have hcM := P.terminalCriticalStart_spec.1
                omega))
            ((A.toFreeBaseMonotoneHenselChain hStart).qOne (i + m)) := by
              simpa using hCore

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
