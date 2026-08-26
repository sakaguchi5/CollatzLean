import CollatzLean.Collatz2.RecordFerrers.Perturbation.P07FixedSkeletonDistanceAdditivity
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockPermutation

/-!
# Record–Ferrers 摂動理論 8: 隣接 length transfer の carry support

隣接二 block の total length を保存して長さだけを移すと、
二 block 通過後の start index は元に戻る。
したがって、その先の raw critical carry は元と exact に同じである。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- 隣接二 block の total length を保存する純 length transfer。 -/
structure AdjacentLengthTransfer (r s r' s' : ℕ) : Prop where
  total_eq : r + s = r' + s'

namespace AdjacentLengthTransfer

/-- 二 block を通過した後の start index は不変。 -/
theorem tailStart_eq
    {r s r' s' : ℕ}
    (T : AdjacentLengthTransfer r s r' s')
    (a : ℕ) :
    (a + r) + s = (a + r') + s' := by
  simpa [Nat.add_assoc] using
    congrArg (fun n : ℕ => a + n) T.total_eq

/-- 二 block より後ろの任意 block に対する raw carry は不変。 -/
theorem tailCarry_eq
    {r s r' s' : ℕ}
    (T : AdjacentLengthTransfer r s r' s')
    (a t : ℕ) :
    criticalCarry ((a + r) + s) t =
      criticalCarry ((a + r') + s') t := by
  rw [T.tailStart_eq a]

/-- 二 block をまとめて見た outer carry も不変。 -/
theorem outerCarry_eq
    {r s r' s' : ℕ}
    (T : AdjacentLengthTransfer r s r' s')
    (a : ℕ) :
    criticalCarry a (r + s) = criticalCarry a (r' + s') := by
  rw [T.total_eq]

end AdjacentLengthTransfer

end RecordFerrers
end Collatz2
