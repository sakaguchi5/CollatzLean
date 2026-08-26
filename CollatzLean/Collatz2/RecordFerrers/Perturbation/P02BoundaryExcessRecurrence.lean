import CollatzLean.Collatz2.RecordFerrers.Perturbation.P01BoundaryExcess

/-!
# Record–Ferrers 摂動理論 2: 境界 excess の一段更新

末尾へ block を一つ追加したとき、excess は `1 - carry` だけ増える。
carry は 0/1 なので、carry 1 では excess は保存され、carry 0 でちょうど 1 増える。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace Skeleton

/-- 末尾へ一 block 追加したときの exact recurrence。 -/
theorem boundaryExcessInt_snoc
    (start r : ℕ)
    (rs : List ℕ) :
    boundaryExcessInt start (rs ++ [r]) =
      boundaryExcessInt start rs + 1 -
        (criticalCarry (start + rs.sum) r : ℤ) := by
  have hCrit :
      criticalHeight (start + (rs.sum + r)) =
        criticalHeight (start + rs.sum) + criticalHeight r +
          criticalCarry (start + rs.sum) r := by
    simpa [Nat.add_assoc] using
      (criticalHeight_add_eq (start + rs.sum) r)
  unfold boundaryExcessInt localMinimalDepthSum
  simp only [List.map_append, List.sum_append, List.map_singleton,
    List.sum_singleton, List.sum_append, minimalDepth]
  rw [hCrit]
  push_cast
  ring

/-- carry 1 の block を足しても boundary excess は変わらない。 -/
theorem boundaryExcessInt_snoc_of_carry_one
    (start r : ℕ)
    (rs : List ℕ)
    (hCarry : criticalCarry (start + rs.sum) r = 1) :
    boundaryExcessInt start (rs ++ [r]) =
      boundaryExcessInt start rs := by
  rw [boundaryExcessInt_snoc, hCarry]
  norm_num

/-- carry 0 の block を足すと boundary excess はちょうど 1 増える。 -/
theorem boundaryExcessInt_snoc_of_carry_zero
    (start r : ℕ)
    (rs : List ℕ)
    (hCarry : criticalCarry (start + rs.sum) r = 0) :
    boundaryExcessInt start (rs ++ [r]) =
      boundaryExcessInt start rs + 1 := by
  rw [boundaryExcessInt_snoc, hCarry]
  norm_num

end Skeleton

end RecordFerrers
end Collatz2
