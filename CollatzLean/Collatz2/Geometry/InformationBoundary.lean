import CollatzLean.Collatz2.Geometry.FerrersReconstruction
import CollatzLean.Collatz2.Geometry.RecordFerrersFactorization
import CollatzLean.Collatz2.Geometry.BlockFerrersDeficit
import Mathlib.Tactic.NormNum

/-!
# Collatz2 Geometry: lossless / lossy information boundary

どの表現が word を完全復元し、どの projection で情報が落ちるかを API として明示する。
-/

namespace Collatz2
namespace Word

/-- `(p,H,B)` は valid word 上で lossless。 -/
theorem word_eq_of_same_losslessTriple
    {u v : Word}
    (hu : Valid u)
    (hv : Valid v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hB : affineConst u = affineConst v) :
    u = v :=
  valid_word_unique_of_oddSteps_twoSteps_affineConst hu hv hp hH hB

/-- full Ferrers profile + global chord も valid FirstCrossing word 上で lossless。 -/
theorem word_eq_of_same_fullFerrersData
    {u v : Word}
    (hu : Valid u)
    (hv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hProfile :
      ∀ k : ℕ, k < oddSteps u →
        ferrersCoordinate u k = ferrersCoordinate v k) :
    u = v :=
  word_eq_of_same_ferrersProfile hu hv hFu hFv hp hH hProfile

/-- `(p,H)` だけでは内部順序を失う explicit collision。 -/
theorem exponentPair_projection_is_lossy :
    oddSteps ([1, 3] : Word) = oddSteps ([2, 2] : Word) ∧
    twoSteps ([1, 3] : Word) = twoSteps ([2, 2] : Word) ∧
    ([1, 3] : Word) ≠ ([2, 2] : Word) := by
  norm_num [oddSteps, twoSteps]

/-- 同じ `(p,H)` collision を exact `B` が区別する。 -/
theorem affineConst_separates_exponentPair_collision :
    affineConst ([1, 3] : Word) ≠ affineConst ([2, 2] : Word) := by
  norm_num [affineConst]

/-- block length + total depth だけでも内部 word は一意ではない。 -/
theorem blockSkeleton_projection_is_lossy :
    oddSteps ([1, 1, 3] : Word) = oddSteps ([1, 2, 2] : Word) ∧
    twoSteps ([1, 1, 3] : Word) = twoSteps ([1, 2, 2] : Word) ∧
    ([1, 1, 3] : Word) ≠ ([1, 2, 2] : Word) := by
  norm_num [oddSteps, twoSteps]

/-- exact `B` は上の同-skeleton decorations も区別する。 -/
theorem affineConst_separates_blockSkeleton_collision :
    affineConst ([1, 1, 3] : Word) ≠ affineConst ([1, 2, 2] : Word) := by
  norm_num [affineConst]


/-- total integer Ferrers deficit 一個だけでは word を復元できない explicit collision。 -/
theorem integerFerrersDeficit_projection_is_lossy :
    integerFerrersDeficit ([2] : Word) = integerFerrersDeficit ([3] : Word) ∧
      ([2] : Word) ≠ ([3] : Word) := by
  norm_num [integerFerrersDeficit, integerFerrersDeficitTerm,
    criticalAffineTerm, affinePathTerm, oddSteps, prefixTwoDepth,
    criticalHeight]

/-- 上の deficit collision は total two-depth `H` を保持すれば区別される。 -/
theorem twoSteps_separates_integerFerrersDeficit_collision :
    twoSteps ([2] : Word) ≠ twoSteps ([3] : Word) := by
  norm_num [twoSteps]

end Word
end Collatz2
