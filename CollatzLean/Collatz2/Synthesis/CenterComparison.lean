import CollatzLean.Collatz2.Matrix.Commutator
import CollatzLean.Collatz2.Matrix.FixedPoint

/-!
# Collatz2 Synthesis: center comparison

Native coefficient geometry と Matrix geometry をここでだけ合流させる。

`SameCenter` は `(B, A-C)` の projective proportionalityという薄い Prop とし、
それが fixed-point vector の wedge zero、旧 `omega` 型 scalar zero、
matrix commutativity とすべて同値であることを示す。
-/

namespace Collatz2
namespace Synthesis

open MatrixAnalysis

/--
二 transfer の homogeneous center `(B, A-C)` が同じ projective point を表す。
除算を使わない cross-multiplication 版。
-/
def SameCenter (T U : AffineTransfer) : Prop :=
  (T.translate : ℤ) * (-U.determinant) =
    (U.translate : ℤ) * (-T.determinant)

/-- fixed-point vectors の wedge は commutator scalar `omega` の負号。 -/
theorem fixedPoint_wedge_eq_neg_omega
    (T U : AffineTransfer) :
    wedge (fixedPointVector T) (fixedPointVector U) =
      -MatrixAnalysis.omega T U := by
  simp [wedge, fixedPointVector, MatrixAnalysis.omega]
  ring

/-- SameCenter は commutator scalar `omega = 0` と同値。 -/
theorem sameCenter_iff_omega_eq_zero
    (T U : AffineTransfer) :
    SameCenter T U ↔ MatrixAnalysis.omega T U = 0 := by
  constructor
  · intro h
    unfold SameCenter at h
    unfold MatrixAnalysis.omega
    calc
      (T.translate : ℤ) * U.determinant -
            (U.translate : ℤ) * T.determinant
          =
          -((T.translate : ℤ) * (-U.determinant)) +
            (U.translate : ℤ) * (-T.determinant) := by ring
      _ = 0 := by rw [h]; ring
  · intro h
    unfold MatrixAnalysis.omega at h
    have hEq :
        (T.translate : ℤ) * U.determinant =
          (U.translate : ℤ) * T.determinant :=
      sub_eq_zero.mp h
    unfold SameCenter
    calc
      (T.translate : ℤ) * (-U.determinant)
          = -((T.translate : ℤ) * U.determinant) := by ring
      _ = -((U.translate : ℤ) * T.determinant) := by rw [hEq]
      _ = (U.translate : ℤ) * (-T.determinant) := by ring

/-- SameCenter は fixed-point vectors の projective wedge zero と同値。 -/
theorem sameCenter_iff_fixedPoint_wedge_zero
    (T U : AffineTransfer) :
    SameCenter T U ↔
      wedge (fixedPointVector T) (fixedPointVector U) = 0 := by
  rw [sameCenter_iff_omega_eq_zero, fixedPoint_wedge_eq_neg_omega]
  simp

/--
同一 center と matrix 可換性は exact に同値。
`determinant ≠ 0` の場合には両 fixed-point vectors が affine chart の実際の center を表す。
-/
theorem sameCenter_iff_matrix_commute
    (T U : AffineTransfer) :
    SameCenter T U ↔
      representation U * representation T =
        representation T * representation U := by
  rw [sameCenter_iff_omega_eq_zero]
  exact MatrixAnalysis.omega_eq_zero_iff_commute T U

end Synthesis
end Collatz2
