import CollatzLean.Collatz2.RecordFerrers.Perturbation.P12BoundaryExcessMonotonicity

/-!
# Record–Ferrers 摂動理論 13: defect 後の旧 block 境界への永久的不帰還

P11 では excess が 1 で、その後の carry がすべて 1 の場合を扱った。
ここでは P12 の一般単調性を使い、excess が一度でも正になれば、
その後どのような carry 列が続いても旧 block-aligned boundary は critical roof に戻れないことを示す。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace Skeleton

/-- 正の boundary excess を持つ境界は critical roof ではない。 -/
theorem old_boundary_not_roof_of_positive_excess
    (start : ℕ)
    (rs : List ℕ)
    (hPos : 0 < boundaryExcessInt start rs) :
    criticalHeight start + localMinimalDepthSum rs ≠
      criticalHeight (start + rs.sum) := by
  intro hRoof
  have hRoofInt :
      (criticalHeight start : ℤ) + (localMinimalDepthSum rs : ℤ) =
        (criticalHeight (start + rs.sum) : ℤ) := by
    exact_mod_cast hRoof
  unfold boundaryExcessInt at hPos
  linarith

/--
一度正の defect が生じた後は、任意 tail の終端でも旧 critical roof に戻れない。
後続 carry に追加の 0 が現れた場合は defect がさらに増えるだけで、修復にはならない。
-/
theorem old_boundary_not_roof_after_any_tail
    (start : ℕ)
    (leftCtx tail : List ℕ)
    (hPos : 0 < boundaryExcessInt start leftCtx) :
    criticalHeight start + localMinimalDepthSum (leftCtx ++ tail) ≠
      criticalHeight (start + (leftCtx ++ tail).sum) := by
  apply old_boundary_not_roof_of_positive_excess
  exact boundaryExcessInt_pos_append_of_pos start leftCtx tail hPos

end Skeleton

/--
roof anchor に minimal blocks を連結した実 word でも、正の skeleton excess は
actual boundary が critical roof でないことを意味する。
-/
theorem assembled_old_boundary_not_roof_of_positive_excess
    (anchor : Word)
    (bs : List Word)
    (hAnchorRoof : twoSteps anchor = criticalHeight (oddSteps anchor))
    (hMinimal : ∀ b ∈ bs, MinimalBlock b)
    (hPos :
      0 < Skeleton.boundaryExcessInt
        (oddSteps anchor) (bs.map oddSteps)) :
    twoSteps (anchor ++ bs.flatten) ≠
      criticalHeight (oddSteps (anchor ++ bs.flatten)) := by
  have hLocal :=
    twoSteps_flatten_eq_localMinimalDepthSum_map bs hMinimal
  have hOdd :
      oddSteps bs.flatten = (bs.map oddSteps).sum := by
    rw [oddSteps_flatten_blocks]
    rfl
  have hNotRoof :=
    Skeleton.old_boundary_not_roof_of_positive_excess
      (oddSteps anchor) (bs.map oddSteps) hPos
  intro hRoof
  apply hNotRoof
  rw [twoSteps_append, oddSteps_append, hAnchorRoof, hLocal, hOdd] at hRoof
  exact hRoof

end RecordFerrers
end Collatz2
