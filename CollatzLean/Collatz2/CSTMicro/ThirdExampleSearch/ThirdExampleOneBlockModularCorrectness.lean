import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCFPacketCertification
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalAffineDefect

/-!
# 第3例探索 B: one-block modular transfer correctness

A の certified corrected packet から、一個の shifted odd standard block が
actual prefix defect を left から right へ exact に送ることを `ZMod M` 上で証明する。

重要:
通常の endpoint decomposition transfer の multiplier は `3^P` だが、
corrected Christoffel dictionary を吸収した高速 transfer の multiplier は `2^Q`。
したがって二つの transfer structure 自体が等しいのではない。

等しいのは actual prefix-defect state に作用させた結果である。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic
open ModularStandardWordPacket
open ModularStandardBlockTransfer

/-- certified corrected packet から作る hot-path one-block transfer。 -/
def thirdExampleCertifiedOddScaleTransferAt
    (M r left : ℕ)
    (y : ZMod M) : ModularStandardBlockTransfer M :=
  (thirdExampleCertifiedScalePacket M r).oddShiftedTransfer left y

/--
certified odd block の高速 transfer は actual prefix defect を exact に更新する。
-/
theorem thirdExampleCertifiedOddScaleTransferAt_apply_actualPrefix
    {M r left : ℕ}
    (C : ThirdExampleActualOddScalePacketCertificate M r)
    (hRange :
      left + criticalPowerP r < criticalPowerP (r + 1))
    (y : ℤ) :
    (thirdExampleCertifiedOddScaleTransferAt
        M r left (y : ZMod M)).apply
        ((criticalPrefixDefectZ left y : ℤ) : ZMod M) =
      ((criticalPrefixDefectZ
          (left + criticalPowerP r) y : ℤ) : ZMod M) := by
  have hEndpoint :=
    criticalPrefixDefectZ_endpoint_decomposition
      (a := left)
      (b := left + criticalPowerP r)
      (by omega : left ≤ left + criticalPowerP r)
      y
  have hDict :=
    shiftedDefect_correctedDictionary_of_odd
      C.nine_le C.odd hRange y
  have hUpdate :
      criticalPrefixDefectZ (left + criticalPowerP r) y =
        (2 : ℤ) ^ criticalPowerQ r *
            criticalPrefixDefectZ left y +
          (3 : ℤ) ^ left *
            actualCorrectedChristoffelLinearForm r y := by
    have hLen :
        left + criticalPowerP r - left = criticalPowerP r := by
      omega
    rw [hLen] at hEndpoint
    rw [hDict] at hEndpoint
    unfold actualCriticalRawPowerGap at hEndpoint
    ring_nf at hEndpoint ⊢
    exact hEndpoint
  have hUpdateMod :=
    congrArg (fun z : ℤ => (z : ZMod M)) hUpdate
  unfold thirdExampleCertifiedOddScaleTransferAt
  rw [ModularStandardWordPacket.oddShiftedTransfer_apply]
  rw [C.rise_eq]
  rw [C.defect_eq_correctedLinearForm y]
  simpa using hUpdateMod.symm

/--
literal P checkpoint で書いた phase corridor から actual corridor を復元する wrapper。
-/
theorem thirdExampleCertifiedOddScaleTransferAt_apply_of_literalRange
    {M r left : ℕ}
    (C : ThirdExampleActualOddScalePacketCertificate M r)
    (hRangeLiteral :
      left + thirdExampleLiteralPowerP r <
        thirdExampleLiteralPowerP (r + 1))
    (y : ℤ) :
    (thirdExampleCertifiedOddScaleTransferAt
        M r left (y : ZMod M)).apply
        ((criticalPrefixDefectZ left y : ℤ) : ZMod M) =
      ((criticalPrefixDefectZ
          (left + thirdExampleLiteralPowerP r) y : ℤ) : ZMod M) := by
  have hRangeActual :
      left + criticalPowerP r < criticalPowerP (r + 1) := by
    rw [C.p_eq, C.next_p_eq]
    exact hRangeLiteral
  have h :=
    thirdExampleCertifiedOddScaleTransferAt_apply_actualPrefix
      C hRangeActual y
  rw [C.p_eq] at h
  exact h

end ThirdExampleSearch
end CSTMicro
end Collatz2
