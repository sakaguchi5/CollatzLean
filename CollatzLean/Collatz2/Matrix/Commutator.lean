import CollatzLean.Collatz2.Matrix.Representation
import CollatzLean.Collatz2.Geometry.Center

/-!
# Collatz2 Matrix: displacement separation の commutator shadow

旧 `omega` を Matrix 側の primitive scalar としては扱わない。
正本は二つの displacement form の resultant `AffineTransfer.separation` であり、
matrix commutator はその derived representation theorem とする。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/-- Compatibility name: matrix `omega` is displacement-form separation. -/
abbrev omega (T U : AffineTransfer) : ℤ :=
  T.separation U

/-- Temporal-order matrices' additive commutator. -/
def commutator (T U : AffineTransfer) : TransferMatrix :=
  representation U * representation T -
    representation T * representation U

/-- The commutator has only the separation/resultant in the upper-right entry. -/
theorem commutator_eq
    (T U : AffineTransfer) :
    commutator T U =
      !![0, T.separation U;
         0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [commutator, representation,
      AffineTransfer.separation,
      DisplacementForm.resultant,
      AffineTransfer.displacementForm,
      AffineTransfer.determinant] <;> ring

/-- Compatibility form using the old name `omega`. -/
theorem commutator_eq_omega
    (T U : AffineTransfer) :
    commutator T U =
      !![0, omega T U;
         0, 0] := by
  simpa using commutator_eq T U

/-- Zero separation is exactly matrix commutativity. -/
theorem separation_eq_zero_iff_commute
    (T U : AffineTransfer) :
    T.separation U = 0 ↔
      representation U * representation T =
        representation T * representation U := by
  constructor
  · intro hsep
    have hc := commutator_eq T U
    rw [hsep] at hc
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

/-- Historical theorem name retained as a compatibility corollary. -/
theorem omega_eq_zero_iff_commute
    (T U : AffineTransfer) :
    omega T U = 0 ↔
      representation U * representation T =
        representation T * representation U := by
  exact separation_eq_zero_iff_commute T U

/-- Historical center/omega-zero characterization, now a direct separation corollary. -/
theorem sameCenter_iff_omega_eq_zero
    (T U : AffineTransfer) :
    T.SameCenter U ↔ omega T U = 0 := by
  exact T.sameCenter_iff_separation_eq_zero U

/-- Same displacement root/center is exactly matrix commutativity. -/
theorem sameCenter_iff_matrix_commute
    (T U : AffineTransfer) :
    T.SameCenter U ↔
      representation U * representation T =
        representation T * representation U := by
  rw [T.sameCenter_iff_separation_eq_zero U]
  exact separation_eq_zero_iff_commute T U

end MatrixAnalysis
end Collatz2
