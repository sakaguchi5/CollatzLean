import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.StandardBlockTransfer
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualOstrowskiBlockDecomposition
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ShiftedCorrectedChristoffelDictionary

/-!
# 第3例探索 次段 7: actual Ostrowski standard block から transfer を作る

既存 `ActualCriticalPhaseBlock` は、actual Ostrowski decomposition の一つの標準 block として

* left / right endpoint,
* scale,
* Beatty rise,
* interval numerator / gap / affine defect

を保持している。

prefix defect の endpoint decomposition

  E_right(y)
    = 3^(right-left) E_left(y)
      + 2^beattyIndex(left) F[left,right](y)

をそのまま

  x |-> mul*x + add

という `StandardBlockTransfer` にする。
これにより標準 block DAG の合成が、既存の actual Ostrowski/Christoffel 算術へ
直接接続される。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/--
actual phase block `B` が固定 global parameter `y` の prefix defect へ作用する transfer。
-/
def standardBlockTransferOfActualPhaseBlock
    (B : ActualCriticalPhaseBlock)
    (y : ℤ) : StandardBlockTransfer :=
  { mul := (3 : ℤ) ^ (B.right - B.left)
    add := (2 : ℤ) ^ beattyIndex B.left * B.defect y }

/--
actual block transfer を左 endpoint の prefix defect に適用すると、右 endpoint の
prefix defectが exact に得られる。
-/
theorem standardBlockTransferOfActualPhaseBlock_apply_prefixDefect
    (B : ActualCriticalPhaseBlock)
    (y : ℤ) :
    (standardBlockTransferOfActualPhaseBlock B y).apply
        (criticalPrefixDefectZ B.left y) =
      criticalPrefixDefectZ B.right y := by
  have hLe : B.left ≤ B.right := by
    unfold ActualCriticalPhaseBlock.right ActualCriticalPhaseBlock.length
    omega
  have hEndpoint :=
    criticalPrefixDefectZ_endpoint_decomposition hLe y
  exact hEndpoint.symm

/--
隣接する actual blocks を generic transfer composition でまとめても、順次適用と同じ。
この定理が Ostrowski standard-block DAG の memoization 用 interface になる。
-/
theorem actualPhaseBlockTransfer_comp_apply
    (B₁ B₂ : ActualCriticalPhaseBlock)
    (y x : ℤ) :
    ((standardBlockTransferOfActualPhaseBlock B₂ y).comp
      (standardBlockTransferOfActualPhaseBlock B₁ y)).apply x =
      (standardBlockTransferOfActualPhaseBlock B₂ y).apply
        ((standardBlockTransferOfActualPhaseBlock B₁ y).apply x) := by
  exact standardBlockTransfer_comp _ _ _

/--
origin に置いた odd standard block では、transfer の additive term は
既存 corrected Christoffel linear formそのものになる。
-/
theorem actualOriginStandardBlockTransfer_add_eq_correctedChristoffel_of_odd
    {r : ℕ}
    (hr : 9 ≤ r)
    (hrOdd : r % 2 = 1)
    (y : ℤ) :
    (standardBlockTransferOfActualPhaseBlock
        (actualCriticalOriginPhaseBlock r) y).add =
      actualCorrectedChristoffelLinearForm r y := by
  have hOrigin :=
    criticalOriginDefect_eq_correctedLinearForm_of_odd hr hrOdd y
  change
    (2 : ℤ) ^ beattyIndex 0 *
        (actualCriticalOriginPhaseBlock r).defect y =
      actualCorrectedChristoffelLinearForm r y
  simp only [beattyIndex_zero, pow_zero, one_mul]
  simpa [ActualCriticalPhaseBlock.defect,
    actualCriticalOriginPhaseBlock,
    ActualCriticalPhaseBlock.right,
    ActualCriticalPhaseBlock.length] using hOrigin

end ThirdExampleSearch
end CSTMicro
end Collatz2
