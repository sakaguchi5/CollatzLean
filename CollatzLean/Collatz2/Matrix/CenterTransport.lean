import CollatzLean.Collatz2.Matrix.Commutator
import CollatzLean.Collatz2.Matrix.FixedPoint

/-!
# Collatz2 Matrix: center-vector transport

homogeneous fixed-point vector `(B, A-C)` は composition で新しい独立 data を作らない。
二つの fixed-point vectors の正係数線形結合として exact に transport される。

同時に commutator scalar `omega` は prefix 側では `A`、suffix 側では `C` によって
exact に scale する。word transfer ではこれは2冪・3冪 transport の源になる。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/--
fixed-point vector の composition law。
`T` の後に `U` を実行すると、composite center vector は
`C_U * V_T + A_T * V_U`。
-/
theorem fixedPointVector_followedBy
    (T U : AffineTransfer) :
    fixedPointVector (T.followedBy U) =
      (U.oddCoeff : ℤ) • fixedPointVector T +
        (T.twoCoeff : ℤ) • fixedPointVector U := by
  funext i
  fin_cases i
  · simp [fixedPointVector, AffineTransfer.followedBy]
  · simp [fixedPointVector, AffineTransfer.determinant_followedBy]
    ring

/--
`T` と composite `T followedBy U` の commutator scalar は
元の `omega(T,U)` の `A_T` 倍。
-/
theorem omega_left_followedBy
    (T U : AffineTransfer) :
    omega T (T.followedBy U) =
      (T.twoCoeff : ℤ) * omega T U := by
  simp only [omega]
  rw [AffineTransfer.determinant_followedBy]
  simp only [AffineTransfer.followedBy, Nat.cast_add, Nat.cast_mul]
  ring_nf

/--
composite `T followedBy U` と `U` の commutator scalar は
元の `omega(T,U)` の `C_U` 倍。
-/
theorem omega_followedBy_right
    (T U : AffineTransfer) :
    omega (T.followedBy U) U =
      (U.oddCoeff : ℤ) * omega T U := by
  simp only [omega]
  rw [AffineTransfer.determinant_followedBy]
  simp only [AffineTransfer.followedBy, Nat.cast_add, Nat.cast_mul]
  ring_nf

/-- zero commutator は prefix-side transport で保存される。 -/
theorem omega_left_followedBy_eq_zero_of_eq_zero
    {T U : AffineTransfer}
    (h : omega T U = 0) :
    omega T (T.followedBy U) = 0 := by
  rw [omega_left_followedBy, h]
  ring

/-- zero commutator は suffix-side transport でも保存される。 -/
theorem omega_followedBy_right_eq_zero_of_eq_zero
    {T U : AffineTransfer}
    (h : omega T U = 0) :
    omega (T.followedBy U) U = 0 := by
  rw [omega_followedBy_right, h]
  ring

end MatrixAnalysis
end Collatz2
