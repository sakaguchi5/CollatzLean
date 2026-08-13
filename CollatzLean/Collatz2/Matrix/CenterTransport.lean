import CollatzLean.Collatz2.Matrix.FixedPoint

/-!
# Collatz2 Matrix: root-vector transport

primary transport law は Core の

  `Δ_(T;U) = C_U Δ_T + A_T Δ_U`

である。このファイルでは homogeneous matrix shadow だけを記録し、旧 `omega` 名は
separation transport の compatibility corollary として残す。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/-- Homogeneous center/root-vector image of displacement-form composition. -/
theorem fixedPointVector_followedBy
    (T U : AffineTransfer) :
    fixedPointVector (T.followedBy U) =
      (U.oddCoeff : ℤ) • fixedPointVector T +
        (T.twoCoeff : ℤ) • fixedPointVector U := by
  funext i
  fin_cases i
  · simp [fixedPointVector, AffineTransfer.displacementForm,
      AffineTransfer.followedBy]
  · simp [fixedPointVector, AffineTransfer.displacementForm,
      AffineTransfer.determinant_followedBy]
    ring

/-- Primary prefix-side separation transport. -/
theorem separation_left_followedBy
    (T U : AffineTransfer) :
    T.separation (T.followedBy U) =
      (T.twoCoeff : ℤ) * T.separation U :=
  AffineTransfer.separation_left_followedBy T U

/-- Primary suffix-side separation transport. -/
theorem separation_followedBy_right
    (T U : AffineTransfer) :
    (T.followedBy U).separation U =
      (U.oddCoeff : ℤ) * T.separation U :=
  AffineTransfer.separation_followedBy_right T U

/-- Historical prefix-side `omega` theorem. -/
theorem omega_left_followedBy
    (T U : AffineTransfer) :
    omega T (T.followedBy U) =
      (T.twoCoeff : ℤ) * omega T U := by
  exact separation_left_followedBy T U

/-- Historical suffix-side `omega` theorem. -/
theorem omega_followedBy_right
    (T U : AffineTransfer) :
    omega (T.followedBy U) U =
      (U.oddCoeff : ℤ) * omega T U := by
  exact separation_followedBy_right T U

/-- Zero separation is preserved under prefix transport. -/
theorem separation_left_followedBy_eq_zero_of_eq_zero
    {T U : AffineTransfer}
    (h : T.separation U = 0) :
    T.separation (T.followedBy U) = 0 := by
  rw [separation_left_followedBy, h]
  ring

/-- Zero separation is preserved under suffix transport. -/
theorem separation_followedBy_right_eq_zero_of_eq_zero
    {T U : AffineTransfer}
    (h : T.separation U = 0) :
    (T.followedBy U).separation U = 0 := by
  rw [separation_followedBy_right, h]
  ring

/-- Historical zero-omega prefix transport. -/
theorem omega_left_followedBy_eq_zero_of_eq_zero
    {T U : AffineTransfer}
    (h : omega T U = 0) :
    omega T (T.followedBy U) = 0 :=
  separation_left_followedBy_eq_zero_of_eq_zero h

/-- Historical zero-omega suffix transport. -/
theorem omega_followedBy_right_eq_zero_of_eq_zero
    {T U : AffineTransfer}
    (h : omega T U = 0) :
    omega (T.followedBy U) U = 0 :=
  separation_followedBy_right_eq_zero_of_eq_zero h

end MatrixAnalysis
end Collatz2
