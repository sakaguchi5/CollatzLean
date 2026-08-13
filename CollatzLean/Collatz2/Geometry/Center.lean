import CollatzLean.Collatz2.Local.Defect
import Mathlib.Tactic.Linarith

/-!
# Collatz2 Geometry: displacement form の center

finite center は primitive data ではなく、

  `Δ_T(X) = B + (C-A)X`

の projective root である。center comparison は除算せず cross product で保持し、
二 root の equality / orientation は `AffineTransfer.separation` の符号として読む。
-/

namespace Collatz2
namespace AffineTransfer

/-- Natural positive gap `A-C` used on the negative-determinant branch. -/
def centerGap (T : AffineTransfer) : ℕ :=
  T.twoCoeff - T.oddCoeff

/-- Negative determinant gives a positive natural center gap. -/
theorem centerGap_pos_of_negative
    {T : AffineTransfer}
    (hneg : T.determinant < 0) :
    0 < T.centerGap := by
  unfold centerGap determinant at *
  omega

/-- On the negative branch the signed slope is `-centerGap`. -/
theorem determinant_eq_neg_centerGap
    {T : AffineTransfer}
    (hneg : T.determinant < 0) :
    T.determinant = -(T.centerGap : ℤ) := by
  have hle : T.oddCoeff ≤ T.twoCoeff := by
    unfold determinant at hneg
    omega
  unfold centerGap determinant
  rw [Nat.cast_sub hle]
  ring

/-- Same finite/projective center, expressed as equality of displacement roots. -/
def SameCenter (T U : AffineTransfer) : Prop :=
  DisplacementForm.SameRoot T.displacementForm U.displacementForm

/-- Same center is exactly zero separation. -/
theorem sameCenter_iff_separation_eq_zero
    (T U : AffineTransfer) :
    T.SameCenter U ↔ T.separation U = 0 := by
  exact T.sameDisplacementRoot_iff_separation_eq_zero U

/-- Division-free weak order of two finite centers. -/
def CenterLe (T U : AffineTransfer) : Prop :=
  (T.translate : ℤ) * (-U.determinant) ≤
    (U.translate : ℤ) * (-T.determinant)

/-- Division-free strict center rise. -/
def CenterRises (T U : AffineTransfer) : Prop :=
  (T.translate : ℤ) * (-U.determinant) <
    (U.translate : ℤ) * (-T.determinant)

/-- Strict center rise is positive displacement-form separation. -/
theorem centerRises_iff_separation_pos
    (T U : AffineTransfer) :
    T.CenterRises U ↔ 0 < T.separation U := by
  unfold CenterRises separation DisplacementForm.resultant displacementForm
  constructor <;> intro h <;> nlinarith

/--
If `T`'s center is strictly below `U`'s center, the center of `T followedBy U`
lies strictly between them.  This is a direct corollary of separation transport.
-/
theorem centerRises_followedBy_between
    {T U : AffineTransfer}
    (hRise : T.CenterRises U)
    (hA : 0 < T.twoCoeff)
    (hC : 0 < U.oddCoeff) :
    T.CenterRises (T.followedBy U) ∧
      (T.followedBy U).CenterRises U := by
  have hsep : 0 < T.separation U :=
    (T.centerRises_iff_separation_pos U).1 hRise
  constructor
  · apply (T.centerRises_iff_separation_pos (T.followedBy U)).2
    rw [T.separation_left_followedBy U]
    have hAz : (0 : ℤ) < (T.twoCoeff : ℤ) := by exact_mod_cast hA
    exact mul_pos hAz hsep
  · apply ((T.followedBy U).centerRises_iff_separation_pos U).2
    rw [T.separation_followedBy_right U]
    have hCz : (0 : ℤ) < (U.oddCoeff : ℤ) := by exact_mod_cast hC
    exact mul_pos hCz hsep

/-- Nonpositive separation reverses the weak center order. -/
theorem centerLe_reverse_of_separation_nonpos
    {T U : AffineTransfer}
    (hsep : T.separation U ≤ 0) :
    U.CenterLe T := by
  unfold CenterLe separation DisplacementForm.resultant displacementForm at *
  nlinarith

/-- Weak center order is reflexive. -/
theorem centerLe_refl (T : AffineTransfer) : T.CenterLe T := by
  unfold CenterLe
  exact le_rfl

/-- Weak center order is transitive when all three centers are finite negative-slope roots. -/
theorem centerLe_trans_of_negative
    {T U V : AffineTransfer}
    (hT : T.determinant < 0)
    (hU : U.determinant < 0)
    (hV : V.determinant < 0)
    (hTU : T.CenterLe U)
    (hUV : U.CenterLe V) :
    T.CenterLe V := by
  have gT : 0 < -T.determinant := by omega
  have gU : 0 < -U.determinant := by omega
  have gV : 0 < -V.determinant := by omega
  unfold CenterLe at hTU hUV ⊢
  have h1 := mul_le_mul_of_nonneg_right hTU (le_of_lt gV)
  have h2 := mul_le_mul_of_nonneg_right hUV (le_of_lt gT)
  have hchain :
      (T.translate : ℤ) * (-U.determinant) * (-V.determinant) ≤
        (V.translate : ℤ) * (-U.determinant) * (-T.determinant) := by
    calc
      (T.translate : ℤ) * (-U.determinant) * (-V.determinant)
          ≤ (U.translate : ℤ) * (-T.determinant) * (-V.determinant) := h1
      _ = (U.translate : ℤ) * (-V.determinant) * (-T.determinant) := by ring
      _ ≤ (V.translate : ℤ) * (-U.determinant) * (-T.determinant) := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using h2
  have hcancel :
      (-U.determinant) *
          ((T.translate : ℤ) * (-V.determinant)) ≤
        (-U.determinant) *
          ((V.translate : ℤ) * (-T.determinant)) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hchain
  exact (Int.mul_le_mul_left gU).mp hcancel

/--
`CenterBeyond T x` says the negative-slope root of `Δ_T` lies to the right of `x`.
Equivalently, the slope is negative and `Δ_T(x)>0`.
-/
def CenterBeyond (T : AffineTransfer) (x : ℕ) : Prop :=
  0 < -T.determinant ∧ 0 < T.displacementForm.eval (x : ℤ)

/-- On a negative transfer, center-beyond is exactly positive start defect. -/
theorem centerBeyond_iff_startDefect_pos
    (T : AffineTransfer)
    (x : ℕ)
    (hneg : T.determinant < 0) :
    T.CenterBeyond x ↔ 0 < T.startDefect x := by
  simp [CenterBeyond, startDefect]
  omega

/-- Historical division-free inequality form of `CenterBeyond`. -/
theorem centerBeyond_iff_gap_mul_lt_translate
    (T : AffineTransfer)
    (x : ℕ) :
    T.CenterBeyond x ↔
      0 < -T.determinant ∧
        (-T.determinant) * (x : ℤ) < (T.translate : ℤ) := by
  unfold CenterBeyond DisplacementForm.eval displacementForm
  constructor <;> rintro ⟨hgap, h⟩ <;> constructor
  · exact hgap
  · linarith
  · exact hgap
  · linarith

/--
A negative transfer realizing a strict positive return has its finite center
strictly to the right of the actual endpoint.
-/
theorem Realizes.centerBeyond_end_of_negative_of_increasing
    {T : AffineTransfer} {x y : ℕ}
    (h : T.Realizes x y)
    (hneg : T.determinant < 0)
    (hxy : x < y)
    (hoddCoeff : 0 < T.oddCoeff) :
    T.CenterBeyond y := by
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
  have heval : 0 < T.displacementForm.eval (y : ℤ) := by
    simpa [endpointDefect] using (neg_pos.mpr hend)
  exact ⟨by omega, heval⟩

end AffineTransfer
end Collatz2
