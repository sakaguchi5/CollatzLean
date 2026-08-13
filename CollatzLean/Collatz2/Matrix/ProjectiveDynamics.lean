import CollatzLean.Collatz2.Matrix.CenterTransport
import Mathlib.Tactic.Linarith

/-!
# Collatz2 Matrix: projective fixed-point dynamics

upper-triangular transfer には常に infinity eigenline `(1,0)` がある。
finite fixed-point vector `(B,A-C)` はもう一方の eigenline を表す。

contracting positive return では finite center が actual endpoint より右にあることを、
有理数除算を使わず `(-determinant) * endpoint < translate` として表す。
-/

namespace Collatz2
namespace MatrixAnalysis

open scoped Matrix

/-- affine chart の projective infinity vector。 -/
def infinityVector : HomPoint :=
  ![1, 0]

/-- infinity vector は `oddCoeff`-eigenvector。 -/
theorem infinityVector_eigen
    (T : AffineTransfer) :
    representation T *ᵥ infinityVector =
      (T.oddCoeff : ℤ) • infinityVector := by
  funext i
  fin_cases i <;>
    simp [infinityVector, representation,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]

/-- infinity と finite fixed-point vector の wedge は `A-C = -determinant`。 -/
theorem wedge_infinity_fixedPointVector
    (T : AffineTransfer) :
    wedge infinityVector (fixedPointVector T) =
      -T.determinant := by
  simp [wedge, infinityVector, fixedPointVector]

/-- finite fixed-point vector と infinity の逆向き wedge は determinant。 -/
theorem wedge_fixedPointVector_infinity
    (T : AffineTransfer) :
    wedge (fixedPointVector T) infinityVector =
      T.determinant := by
  simp [wedge, infinityVector, fixedPointVector]

/--
`CenterBeyond T x` は finite center `B/(A-C)` が `x` より右にあることの
除算を使わない homogeneous 条件。
-/
def CenterBeyond (T : AffineTransfer) (x : ℕ) : Prop :=
  0 < -T.determinant ∧
    (-T.determinant) * (x : ℤ) < (T.translate : ℤ)

/-- contracting transfer では positive start defect と center ordering は同値。 -/
theorem centerBeyond_iff_startDefect_pos
    (T : AffineTransfer)
    (x : ℕ)
    (hneg : T.determinant < 0) :
    CenterBeyond T x ↔ 0 < T.startDefect x := by
  constructor
  · rintro ⟨_, hx⟩
    unfold AffineTransfer.startDefect
    linarith
  · intro hdef
    constructor
    · omega
    · unfold AffineTransfer.startDefect at hdef
      linarith

/--
contracting transfer が actual strict positive return `x < y` を実現するなら、
finite center は endpoint `y` よりさらに右にある。
-/
theorem AffineTransfer.Realizes.centerBeyond_end_of_negative_of_increasing
    {T : AffineTransfer} {x y : ℕ}
    (h : T.Realizes x y)
    (hneg : T.determinant < 0)
    (hxy : x < y)
    (hoddCoeff : 0 < T.oddCoeff) :
    CenterBeyond T y := by
  have hcz : (0 : ℤ) < (T.oddCoeff : ℤ) := by
    exact_mod_cast hoddCoeff
  have hdiff : (x : ℤ) - (y : ℤ) < 0 := by
    omega
  have hprod :
      (T.oddCoeff : ℤ) * ((x : ℤ) - (y : ℤ)) < 0 :=
    mul_neg_of_pos_of_neg hcz hdiff
  have hend : T.endpointDefect y < 0 := by
    rw [h.endpointDefect_eq_reverseDisplacement]
    exact hprod
  constructor
  · omega
  · unfold AffineTransfer.endpointDefect at hend
    linarith

end MatrixAnalysis
end Collatz2
