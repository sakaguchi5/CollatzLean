import CollatzLean.Collatz2.RecordFerrers.Perturbation.P10PersistentExcess
import CollatzLean.Collatz2.RecordFerrers.Factorization.RecordFerrersFactorization

/-!
# Record–Ferrers 摂動理論 11: defect 後の旧 record 境界崩壊

boundary excess が 1 なら、その境界の実 depth は critical roof と一致しない。
後続 carry が 1 のままなら excess は持続するため、旧 skeleton の後続境界は
record roof として再利用できず、新しい decomposition では再分割が必要になる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace Skeleton

/-- excess 1 の境界では minimal-depth 累積値は critical roof と一致しない。 -/
theorem old_boundary_not_roof_of_excess_one
    (start : ℕ)
    (rs : List ℕ)
    (hExcess : boundaryExcessInt start rs = 1) :
    criticalHeight start + localMinimalDepthSum rs ≠
      criticalHeight (start + rs.sum) := by
  intro hRoof
  have hRoofInt :
      (criticalHeight start : ℤ) + (localMinimalDepthSum rs : ℤ) =
        (criticalHeight (start + rs.sum) : ℤ) := by
    exact_mod_cast hRoof
  unfold boundaryExcessInt at hExcess
  linarith

/--
一度 excess 1 が生じ、その後が all-carry-one なら、
任意のその tail 終端でも旧 critical roof には戻れない。
-/
theorem old_boundary_not_roof_after_persistent_defect
    (start : ℕ)
    (leftCtx tail : List ℕ)
    (hExcess : boundaryExcessInt start leftCtx = 1)
    (hTail : AllCarryOneFrom (start + leftCtx.sum) tail) :
    criticalHeight start + localMinimalDepthSum (leftCtx ++ tail) ≠
      criticalHeight (start + (leftCtx ++ tail).sum) := by
  apply old_boundary_not_roof_of_excess_one
  exact persistent_excess_after_single_carry_failure
    start leftCtx tail hExcess hTail

end Skeleton

/-- minimal block 列の flatten depth は length 列の minimal-depth sum。 -/
theorem twoSteps_flatten_eq_localMinimalDepthSum_map
    (bs : List Word)
    (hMinimal : ∀ b ∈ bs, MinimalBlock b) :
    twoSteps bs.flatten = localMinimalDepthSum (bs.map oddSteps) := by
  induction bs with
  | nil =>
      simp [localMinimalDepthSum]
  | cons b bs ih =>
      have hb : MinimalBlock b := hMinimal b (by simp)
      have hTail : ∀ c ∈ bs, MinimalBlock c := by
        intro c hc
        exact hMinimal c (by simp [hc])
      have hIH := ih hTail
      simp [localMinimalDepthSum, twoSteps_append, hb.minimalDepth, hIH]
      rfl

/--
roof anchor に minimal blocks を付けた実 word でも、skeleton excess 1 は
actual boundary が critical roof でないことを意味する。
-/
theorem assembled_old_boundary_not_roof_of_excess_one
    (anchor : Word)
    (bs : List Word)
    (hAnchorRoof : twoSteps anchor = criticalHeight (oddSteps anchor))
    (hMinimal : ∀ b ∈ bs, MinimalBlock b)
    (hExcess :
      Skeleton.boundaryExcessInt
        (oddSteps anchor) (bs.map oddSteps) = 1) :
    twoSteps (anchor ++ bs.flatten) ≠
      criticalHeight (oddSteps (anchor ++ bs.flatten)) := by
  have hLocal :=
    twoSteps_flatten_eq_localMinimalDepthSum_map bs hMinimal
  have hOdd :
      oddSteps bs.flatten = (bs.map oddSteps).sum := by
    rw [oddSteps_flatten_blocks]
    rfl
  have hNotRoof :=
    Skeleton.old_boundary_not_roof_of_excess_one
      (oddSteps anchor) (bs.map oddSteps) hExcess
  intro hRoof
  apply hNotRoof
  rw [twoSteps_append, oddSteps_append, hAnchorRoof, hLocal, hOdd] at hRoof
  exact hRoof

end RecordFerrers
end Collatz2
