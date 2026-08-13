import CollatzLean.Collatz2.Matrix.Representation

/-!
# Collatz2 Matrix: transfer commutator

旧 center-comparison 型の scalar を primitive に置かず、
二つの affine-transfer matrices の commutator の唯一の非零候補成分として導く。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/--
二 transfer の signed commutator scalar。
`d_T = C_T-A_T` とすると `B_T*d_U-B_U*d_T`。
-/
def omega (T U : AffineTransfer) : ℤ :=
  (T.translate : ℤ) * U.determinant -
    (U.translate : ℤ) * T.determinant

/-- temporal-order matrices の additive commutator。 -/
def commutator (T U : AffineTransfer) : TransferMatrix :=
  representation U * representation T -
    representation T * representation U

/-- commutator は右上成分 `omega` だけを持つ。 -/
theorem commutator_eq
    (T U : AffineTransfer) :
    commutator T U =
      !![0, omega T U;
         0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, representation, omega,
      AffineTransfer.determinant] <;> ring

/-- `omega = 0` は二 transfer matrices の可換性と exact に同値。 -/
theorem omega_eq_zero_iff_commute
    (T U : AffineTransfer) :
    omega T U = 0 ↔
      representation U * representation T =
        representation T * representation U := by
  constructor
  · intro hω
    have hc := commutator_eq T U
    rw [hω] at hc
    have hsub :
        representation U * representation T -
            representation T * representation U = 0 := by
      calc
        representation U * representation T -
              representation T * representation U
            = commutator T U := rfl
        _ = !![0, 0; 0, 0] := by simpa using hc
        _ = 0 := by
          ext i j
          fin_cases i <;> fin_cases j <;> rfl
    exact sub_eq_zero.mp hsub
  · intro hcomm
    have hsub : commutator T U = 0 := by
      unfold commutator
      exact sub_eq_zero.mpr hcomm
    rw [commutator_eq] at hsub
    have hentry :=
      congrArg (fun M : TransferMatrix => M 0 1) hsub
    simpa using hentry

end MatrixAnalysis
end Collatz2
