import CollatzLean.Collatz2.Matrix.Representation
import CollatzLean.Collatz2.Local.Defect

/-!
# Collatz2 Matrix: defect の wedge 表現

`DisplacementForm.eval` を正本とし、affine point と homogeneous image の wedge が
その符号付き評価と一致することだけを Matrix shadow として記録する。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/-- Homogeneous point of the projective affine chart. -/
abbrev HomPoint := Fin 2 → ℤ

/-- Embed natural `x` as homogeneous point `(x,1)`. -/
def affinePoint (x : ℕ) : HomPoint :=
  ![(x : ℤ), 1]

/-- Oriented wedge of two 2-vectors. -/
def wedge (p q : HomPoint) : ℤ :=
  p 0 * q 1 - p 1 * q 0

/-- Homogeneous matrix image of an affine point. -/
def imagePoint (T : AffineTransfer) (x : ℕ) : HomPoint :=
  representation T *ᵥ affinePoint x

/-- Matrix image is `(Cx+B,A)`. -/
theorem imagePoint_eq
    (T : AffineTransfer)
    (x : ℕ) :
    imagePoint T x =
      ![(T.oddCoeff : ℤ) * (x : ℤ) + (T.translate : ℤ),
        (T.twoCoeff : ℤ)] := by
  funext i
  fin_cases i <;>
    simp [imagePoint, affinePoint, representation,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]

/-- Start defect/displacement evaluation is the negative oriented wedge. -/
theorem startDefect_eq_neg_wedge
    (T : AffineTransfer)
    (x : ℕ) :
    T.startDefect x = -wedge (affinePoint x) (imagePoint T x) := by
  rw [imagePoint_eq]
  simp [wedge, affinePoint, AffineTransfer.startDefect,
    DisplacementForm.eval, AffineTransfer.displacementForm,
    AffineTransfer.determinant]
  ring

/-- Positive displacement evaluation is negative wedge orientation. -/
theorem startDefect_pos_iff_wedge_neg
    (T : AffineTransfer)
    (x : ℕ) :
    0 < T.startDefect x ↔
      wedge (affinePoint x) (imagePoint T x) < 0 := by
  rw [startDefect_eq_neg_wedge]
  omega

end MatrixAnalysis
end Collatz2
