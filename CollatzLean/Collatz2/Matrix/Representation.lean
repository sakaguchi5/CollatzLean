import CollatzLean.Collatz2.Core.AffineTransfer
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Collatz2 Matrix: affine-transfer representation

Matrix 側の正本を新設しない。
既存 `AffineTransfer` を upper-triangular 2x2 integer matrix として読む view だけを置く。

`T.followedBy U` は first `T`, then `U` なので、matrix product の順序は `M_U * M_T`。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/-- affine transfer の homogeneous 2x2 integer matrix。 -/
abbrev TransferMatrix := Matrix (Fin 2) (Fin 2) ℤ

/--
`A*y = C*x+B` を homogeneous vector `(x,1)` 上で
`(Cx+B, A)` に送る upper-triangular matrix として表す。
-/
def representation (T : AffineTransfer) : TransferMatrix :=
  !![(T.oddCoeff : ℤ), (T.translate : ℤ);
     0,                  (T.twoCoeff : ℤ)]

@[simp] theorem representation_zero_zero (T : AffineTransfer) :
    representation T 0 0 = (T.oddCoeff : ℤ) := rfl

@[simp] theorem representation_zero_one (T : AffineTransfer) :
    representation T 0 1 = (T.translate : ℤ) := rfl

@[simp] theorem representation_one_zero (T : AffineTransfer) :
    representation T 1 0 = 0 := rfl

@[simp] theorem representation_one_one (T : AffineTransfer) :
    representation T 1 1 = (T.twoCoeff : ℤ) := rfl

/-- temporal composition は reverse-order matrix multiplication。 -/
theorem representation_followedBy
    (T U : AffineTransfer) :
    representation (T.followedBy U) =
      representation U * representation T := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [representation, AffineTransfer.followedBy,
      Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- word append も同じ matrix multiplication law を持つ。 -/
theorem representation_ofWord_append
    (u v : Word) :
    representation (AffineTransfer.ofWord (u ++ v)) =
      representation (AffineTransfer.ofWord v) *
        representation (AffineTransfer.ofWord u) := by
  rw [AffineTransfer.ofWord_append, representation_followedBy]

end MatrixAnalysis
end Collatz2
