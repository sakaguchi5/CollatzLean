import CollatzLean.Collatz2.Matrix.CenterTransport

/-!
# Collatz2 Matrix: displacement-root geometry の projective shadow

finite center/root と `CenterBeyond` の正本は `Geometry.Center` に移す。
ここには infinity eigenline など Matrix 固有の projective statement と旧 API 互換 view だけを残す。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/-- Projective infinity vector of the affine chart. -/
def infinityVector : HomPoint :=
  ![1, 0]

/-- Infinity is the `oddCoeff` eigenline. -/
theorem infinityVector_eigen
    (T : AffineTransfer) :
    representation T *ᵥ infinityVector =
      (T.oddCoeff : ℤ) • infinityVector := by
  funext i
  fin_cases i <;>
    simp [infinityVector, representation,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]

/-- Infinity versus finite root wedge is `A-C=-determinant`. -/
theorem wedge_infinity_fixedPointVector
    (T : AffineTransfer) :
    wedge infinityVector (fixedPointVector T) =
      -T.determinant := by
  simp [wedge, infinityVector, fixedPointVector,
    AffineTransfer.displacementForm]

/-- Reverse wedge is the signed slope/determinant. -/
theorem wedge_fixedPointVector_infinity
    (T : AffineTransfer) :
    wedge (fixedPointVector T) infinityVector =
      T.determinant := by
  simp [wedge, infinityVector, fixedPointVector,
    AffineTransfer.displacementForm]

/-- Historical Matrix-facing name for the core center-root ordering property. -/
abbrev CenterBeyond (T : AffineTransfer) (x : ℕ) : Prop :=
  T.CenterBeyond x

/-- Compatibility characterization by start-defect sign. -/
theorem centerBeyond_iff_startDefect_pos
    (T : AffineTransfer)
    (x : ℕ)
    (hneg : T.determinant < 0) :
    CenterBeyond T x ↔ 0 < T.startDefect x :=
  T.centerBeyond_iff_startDefect_pos x hneg

end MatrixAnalysis
end Collatz2
