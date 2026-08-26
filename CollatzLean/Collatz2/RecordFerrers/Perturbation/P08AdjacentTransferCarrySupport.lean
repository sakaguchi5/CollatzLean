import CollatzLean.Collatz2.RecordFerrers.Perturbation.P07FixedSkeletonDistanceAdditivity
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockPermutation

/-!
# Record–Ferrers 摂動理論 8: 隣接長さ移送の carry 支持

隣接する二つの block の全長を保存して長さだけを移すと、
二 block 通過後の開始位置は元に戻る。
したがって、その先の critical carry と、二 block をまとめた外側 carry は変化しない。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- 隣接二 block の全長を保存する純粋な長さ移送。 -/
structure AdjacentLengthTransfer (r s r' s' : ℕ) : Prop where
  total_eq : r + s = r' + s'

namespace AdjacentLengthTransfer

/-- 二 block を通過した後の開始位置は不変。 -/
theorem tailStart_eq
    {r s r' s' : ℕ}
    (T : AdjacentLengthTransfer r s r' s')
    (a : ℕ) :
    (a + r) + s = (a + r') + s' := by
  simpa [Nat.add_assoc] using
    congrArg (fun n : ℕ => a + n) T.total_eq

/-- 二 block より後ろの任意 block に対する critical carry は不変。 -/
theorem tailCarry_eq
    {r s r' s' : ℕ}
    (T : AdjacentLengthTransfer r s r' s')
    (a t : ℕ) :
    criticalCarry ((a + r) + s) t =
      criticalCarry ((a + r') + s') t := by
  rw [T.tailStart_eq a]

/-- 二 block をまとめて見た外側 carry も不変。 -/
theorem outerCarry_eq
    {r s r' s' : ℕ}
    (T : AdjacentLengthTransfer r s r' s')
    (a : ℕ) :
    criticalCarry a (r + s) = criticalCarry a (r' + s') := by
  rw [T.total_eq]

end AdjacentLengthTransfer

end RecordFerrers
end Collatz2
