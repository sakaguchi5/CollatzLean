import CollatzLean.Collatz2.RecordFerrers.Perturbation.P07FixedSkeletonDistanceAdditivity
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockPermutation

/-!
# Record–Ferrers 摂動理論 8: 隣接長さ移送の carry 支持

このファイルの `AdjacentLengthTransfer r s r' s'` は、actual `FiberPoint` deformation ではなく、
同じ outer interval を二つに切る長さ座標の変更だけを保持する pure skeleton-level object である。
特に `r',s'` が target の genuine `RecordBlock` 長であることはここでは仮定しない。

全長 `r+s=r'+s'` だけを保存すると、候補二分割を通過した後の開始位置は元に戻る。
したがって、その先の critical carry と、二候補をまとめた外側 carry は変化しない。
actual `BlockReplacement` と target cut からこの object を導出する bridge は P21 で与える。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
同じ outer interval の候補二分割について、total odd length だけを保存する純粋な長さ移送。
actual deformation や target `RecordBlock` の存在はこの structure の意味に含めない。
-/
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
