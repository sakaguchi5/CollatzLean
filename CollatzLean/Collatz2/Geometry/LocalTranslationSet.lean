import CollatzLean.Collatz2.Geometry.FerrersReconstruction
import CollatzLean.Collatz2.Geometry.MinimalCrossingBlock
import Mathlib.Data.Set.Basic

/-!
# Collatz2 Geometry: local translation spectrum

固定 record-block length `r` に対し、valid minimal-crossing decorations が取り得る
exact affine translation `B` の集合を保持する。
-/

namespace Collatz2
namespace Word

/-- length `r` の valid minimal-crossing block が取り得る exact `B`。 -/
def localTranslationSet (r : ℕ) : Set ℕ :=
  {B | ∃ w : Word,
      ValidMinimalCrossingBlock w ∧
      oddSteps w = r ∧
      affineConst w = B}

/-- concrete valid minimal block は local spectrum に入る。 -/
theorem affineConst_mem_localTranslationSet
    {w : Word}
    (M : ValidMinimalCrossingBlock w) :
    affineConst w ∈ localTranslationSet (oddSteps w) := by
  exact ⟨w, M, rfl, rfl⟩

/-- fixed length の local `B` は valid minimal block を一意に符号化する。 -/
theorem validMinimalBlock_unique_of_same_length_affineConst
    {u v : Word}
    (Mu : ValidMinimalCrossingBlock u)
    (Mv : ValidMinimalCrossingBlock v)
    (hp : oddSteps u = oddSteps v)
    (hB : affineConst u = affineConst v) :
    u = v := by
  have hHu : twoSteps u = criticalHeight (oddSteps u) + 1 :=
    Mu.toMinimalCrossingBlock.minimalDepth
  have hHv : twoSteps v = criticalHeight (oddSteps v) + 1 :=
    Mv.toMinimalCrossingBlock.minimalDepth
  have hH : twoSteps u = twoSteps v := by
    rw [hHu, hHv, hp]
  exact valid_word_unique_of_oddSteps_twoSteps_affineConst
    Mu.valid Mv.valid hp hH hB

/-- fixed `r` では local spectrum の一つの値に二つの valid decorations は乗らない。 -/
theorem localTranslationSet_fiber_unique
    {r B : ℕ}
    {u v : Word}
    (Mu : ValidMinimalCrossingBlock u)
    (Mv : ValidMinimalCrossingBlock v)
    (huLen : oddSteps u = r)
    (hvLen : oddSteps v = r)
    (huB : affineConst u = B)
    (hvB : affineConst v = B) :
    u = v := by
  apply validMinimalBlock_unique_of_same_length_affineConst Mu Mv
  · exact huLen.trans hvLen.symm
  · exact huB.trans hvB.symm

end Word
end Collatz2
