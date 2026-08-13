import CollatzLean.Collatz2.Matrix.DefectGeometry
import CollatzLean.Collatz2.Matrix.Commutator

/-!
# Collatz2 Matrix: displacement root の homogeneous vector

finite fixed-point vector `(B,A-C)` は `Δ_T(X)=B+(C-A)X` の homogeneous root vector。
matrix eigenvector theorem は同じ displacement root の derived view として扱う。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/-- Homogeneous vector `(B,A-C)` representing the root of the displacement form. -/
def fixedPointVector (T : AffineTransfer) : HomPoint :=
  ![T.displacementForm.constant, -T.displacementForm.slope]

@[simp] theorem fixedPointVector_zero (T : AffineTransfer) :
    fixedPointVector T 0 = (T.translate : ℤ) := rfl

@[simp] theorem fixedPointVector_one (T : AffineTransfer) :
    fixedPointVector T 1 = -T.determinant := rfl

/-- The root vector is the `twoCoeff` eigenvector of the transfer matrix. -/
theorem fixedPointVector_eigen
    (T : AffineTransfer) :
    representation T *ᵥ fixedPointVector T =
      (T.twoCoeff : ℤ) • fixedPointVector T := by
  funext i
  fin_cases i <;>
    simp [fixedPointVector, representation,
      AffineTransfer.displacementForm,
      AffineTransfer.determinant,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  ring

/-- Nonzero slope gives a nonzero homogeneous root vector. -/
theorem fixedPointVector_ne_zero_of_determinant_ne_zero
    {T : AffineTransfer}
    (hdet : T.determinant ≠ 0) :
    fixedPointVector T ≠ 0 := by
  intro hzero
  have hsecond :=
    congrArg (fun p : HomPoint => p 1) hzero
  simp only [fixedPointVector, AffineTransfer.displacementForm,
    Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Pi.zero_apply, neg_eq_zero] at hsecond
  exact hdet hsecond

/-- The root-vector wedge is the negative displacement-form separation. -/
theorem fixedPoint_wedge_eq_neg_separation
    (T U : AffineTransfer) :
    wedge (fixedPointVector T) (fixedPointVector U) =
      -T.separation U := by
  simp [wedge, fixedPointVector,
    AffineTransfer.displacementForm,
    AffineTransfer.separation,
    DisplacementForm.resultant]
  ring

/-- Historical `omega` statement as a compatibility corollary. -/
theorem fixedPoint_wedge_eq_neg_omega
    (T U : AffineTransfer) :
    wedge (fixedPointVector T) (fixedPointVector U) =
      -omega T U := by
  exact fixedPoint_wedge_eq_neg_separation T U

/-- Same center is exactly projective proportionality of root vectors. -/
theorem sameCenter_iff_fixedPoint_wedge_zero
    (T U : AffineTransfer) :
    T.SameCenter U ↔
      wedge (fixedPointVector T) (fixedPointVector U) = 0 := by
  rw [T.sameCenter_iff_separation_eq_zero U,
    fixedPoint_wedge_eq_neg_separation]
  simp

/-- Start defect is the negative wedge of affine point and center root vector. -/
theorem wedge_fixedPointVector_eq_neg_startDefect
    (T : AffineTransfer)
    (x : ℕ) :
    wedge (affinePoint x) (fixedPointVector T) =
      -T.startDefect x := by
  simp [wedge, affinePoint, fixedPointVector,
    AffineTransfer.startDefect,
    DisplacementForm.eval,
    AffineTransfer.displacementForm]
  ring

end MatrixAnalysis
end Collatz2
