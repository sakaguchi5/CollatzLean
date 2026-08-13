import CollatzLean.Collatz2.Matrix.DefectGeometry

/-!
# Collatz2 Matrix: homogeneous fixed-point geometry

fixed point を最初から有理数 `B/(A-C)` として除算しない。
まず homogeneous vector `(B, A-C)` を使う。
これは transfer matrix の `A`-eigenvector であり、determinant 非零なら affine chart の固定点を表す。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/--
transfer の homogeneous fixed-point vector `(B, A-C)`。
`A-C = -determinant` として符号付き整数のまま保持する。
-/
def fixedPointVector (T : AffineTransfer) : HomPoint :=
  ![(T.translate : ℤ), -T.determinant]

@[simp] theorem fixedPointVector_zero (T : AffineTransfer) :
    fixedPointVector T 0 = (T.translate : ℤ) := rfl

@[simp] theorem fixedPointVector_one (T : AffineTransfer) :
    fixedPointVector T 1 = -T.determinant := rfl

/-- fixed-point vector は transfer matrix の `twoCoeff`-eigenvector。 -/
theorem fixedPointVector_eigen
    (T : AffineTransfer) :
    representation T *ᵥ fixedPointVector T =
      (T.twoCoeff : ℤ) • fixedPointVector T := by
  funext i
  fin_cases i <;>
    simp [fixedPointVector, representation,
      AffineTransfer.determinant,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  ring

/-- determinant 非零なら homogeneous fixed-point vector も非零。 -/
theorem fixedPointVector_ne_zero_of_determinant_ne_zero
    {T : AffineTransfer}
    (hdet : T.determinant ≠ 0) :
    fixedPointVector T ≠ 0 := by
  intro hzero
  have hsecond :=
    congrArg (fun p : HomPoint => p 1) hzero
  simp only [fixedPointVector, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one,
     Pi.zero_apply,neg_eq_zero] at hsecond
  exact hdet hsecond

/--
start defect は affine point と homogeneous fixed-point vector の wedge でも測れる。
従って fixed-point ordering と defect sign は同じ幾何を見ている。
-/
theorem wedge_fixedPointVector_eq_neg_startDefect
    (T : AffineTransfer)
    (x : ℕ) :
    wedge (affinePoint x) (fixedPointVector T) =
      -T.startDefect x := by
  simp [wedge, affinePoint, fixedPointVector,
    AffineTransfer.startDefect, AffineTransfer.determinant]
  ring

end MatrixAnalysis
end Collatz2
