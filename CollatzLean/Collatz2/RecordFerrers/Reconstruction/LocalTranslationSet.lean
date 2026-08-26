import CollatzLean.Collatz2.RecordFerrers.Reconstruction.FerrersReconstruction
import Mathlib.Data.Set.Basic

/-!
# Record–Ferrers Phase A: local translation spectrum

固定 block length `r` に対し、valid minimal blocks が取り得る exact affine translation
`B` の集合を保持する。fixed length では minimal depth が自動的に固定されるため、
`B` 一個で local decoration を一意に復号できる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- length `r` の valid minimal block が取り得る exact affine translation。 -/
def localTranslationSet (r : ℕ) : Set ℕ :=
  {B | ∃ w : Word,
      ValidMinimalBlock w ∧
      oddSteps w = r ∧
      affineConst w = B}

/-- concrete valid minimal block は local spectrum に入る。 -/
theorem affineConst_mem_localTranslationSet
    {w : Word}
    (M : ValidMinimalBlock w) :
    affineConst w ∈ localTranslationSet (oddSteps w) := by
  exact ⟨w, M, rfl, rfl⟩

/-- fixed length の same affineConst は valid minimal block を一意に決める。 -/
theorem validMinimalBlock_unique_of_same_length_affineConst
    {u v : Word}
    (Mu : ValidMinimalBlock u)
    (Mv : ValidMinimalBlock v)
    (hp : oddSteps u = oddSteps v)
    (hB : affineConst u = affineConst v) :
    u = v := by
  have hHu : twoSteps u = minimalDepth (oddSteps u) := by
    unfold minimalDepth
    exact Mu.toMinimalBlock.minimalDepth
  have hHv : twoSteps v = minimalDepth (oddSteps v) := by
    unfold minimalDepth
    exact Mv.toMinimalBlock.minimalDepth
  have hH : twoSteps u = twoSteps v := by
    rw [hHu, hHv, hp]
  exact
    valid_word_unique_of_oddSteps_twoSteps_affineConst
      Mu.valid Mv.valid hp hH hB

/-- local spectrum の一つの value に二つの valid decorations は乗らない。 -/
theorem localTranslationSet_fiber_unique
    {r B : ℕ}
    {u v : Word}
    (Mu : ValidMinimalBlock u)
    (Mv : ValidMinimalBlock v)
    (huLen : oddSteps u = r)
    (hvLen : oddSteps v = r)
    (huB : affineConst u = B)
    (hvB : affineConst v = B) :
    u = v := by
  apply validMinimalBlock_unique_of_same_length_affineConst Mu Mv
  · exact huLen.trans hvLen.symm
  · exact huB.trans hvB.symm

end RecordFerrers
end Collatz2
