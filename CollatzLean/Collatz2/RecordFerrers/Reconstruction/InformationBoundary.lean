import CollatzLean.Collatz2.RecordFerrers.Reconstruction.LocalTranslationSet
import Mathlib.Tactic.NormNum

/-!
# Record–Ferrers Phase A: lossless / lossy information boundary

fixed-chord Ferrers layer で何を保持すれば word が完全復元でき、どの projection で
情報が落ちるかを explicit collision とともに整理する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- `(p,H,B)` は valid words 上で lossless。 -/
theorem word_eq_of_same_losslessTriple
    {u v : Word}
    (hu : Valid u)
    (hv : Valid v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hB : affineConst u = affineConst v) :
    u = v :=
  valid_word_unique_of_oddSteps_twoSteps_affineConst hu hv hp hH hB

/-- full fixed-chord Ferrers shape も lossless。 -/
theorem word_eq_of_same_fullFerrersShape
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hShape : x.toFerrersShape = y.toFerrersShape) :
    x.word = y.word :=
  word_eq_of_same_shape hShape

/-- same `(p,H)` だけでは内部 exponent order を失う explicit collision。 -/
theorem exponentPair_projection_is_lossy :
    oddSteps ([1, 3] : Word) = oddSteps ([2, 2] : Word) ∧
    twoSteps ([1, 3] : Word) = twoSteps ([2, 2] : Word) ∧
    ([1, 3] : Word) ≠ ([2, 2] : Word) := by
  norm_num [oddSteps, twoSteps]

/-- exact affine translation は上の same-chord collision を区別する。 -/
theorem affineConst_separates_exponentPair_collision :
    affineConst ([1, 3] : Word) ≠ affineConst ([2, 2] : Word) := by
  norm_num [affineConst]

/-- total block length + total depth だけでも internal decoration は一意ではない。 -/
theorem blockTotals_projection_is_lossy :
    oddSteps ([1, 1, 3] : Word) = oddSteps ([1, 2, 2] : Word) ∧
    twoSteps ([1, 1, 3] : Word) = twoSteps ([1, 2, 2] : Word) ∧
    ([1, 1, 3] : Word) ≠ ([1, 2, 2] : Word) := by
  norm_num [oddSteps, twoSteps]

/-- exact `B` は same-total local decorations を区別する。 -/
theorem affineConst_separates_blockTotals_collision :
    affineConst ([1, 1, 3] : Word) ≠ affineConst ([1, 2, 2] : Word) := by
  norm_num [affineConst]

/-- full Ferrers shape equality は distance zero の強い形である。 -/
theorem ferrersShape_eq_implies_distance_zero
    {p : ℕ}
    {A B : FerrersShape p}
    (h : A = B) :
    FerrersShape.distance A B = 0 := by
  subst B
  simp

end RecordFerrers
end Collatz2
