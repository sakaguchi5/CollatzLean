import CollatzLean.Collatz2.Geometry.Center
import Mathlib.Data.Nat.GCD.Basic

/-!
# Collatz2 Geometry: primitive negative displacement form

negative transfer では

  `Δ(X) = B - G X`,  `G=A-C>0`

となる。係数 pair `(B,G)` の content `gcd(B,G)` を除いて primitive center direction
を作り、二 primitive root の separation を generic に扱う。
future-minimum 固有の `alpha`, return-gap, `kappa` は Global 側で導く。
-/

namespace Collatz2
namespace AffineTransfer

/-- Content of the negative-center coefficient pair `(B,G)`. -/
def centerContent (T : AffineTransfer) : ℕ :=
  Nat.gcd T.translate T.centerGap

/-- Primitive numerator `B / content`. -/
def primitiveCenterNumerator (T : AffineTransfer) : ℕ :=
  T.translate / T.centerContent

/-- Primitive denominator `G / content`. -/
def primitiveCenterDenominator (T : AffineTransfer) : ℕ :=
  T.centerGap / T.centerContent

/-- Content divides the translation. -/
theorem centerContent_dvd_translate (T : AffineTransfer) :
    T.centerContent ∣ T.translate := by
  unfold centerContent
  exact Nat.gcd_dvd_left _ _

/-- Content divides the natural center gap. -/
theorem centerContent_dvd_centerGap (T : AffineTransfer) :
    T.centerContent ∣ T.centerGap := by
  unfold centerContent
  exact Nat.gcd_dvd_right _ _

/-- `B = h*b`. -/
theorem centerContent_mul_primitiveCenterNumerator
    (T : AffineTransfer) :
    T.centerContent * T.primitiveCenterNumerator = T.translate := by
  unfold primitiveCenterNumerator
  exact Nat.mul_div_cancel' T.centerContent_dvd_translate

/-- `G = h*d`. -/
theorem centerContent_mul_primitiveCenterDenominator
    (T : AffineTransfer) :
    T.centerContent * T.primitiveCenterDenominator = T.centerGap := by
  unfold primitiveCenterDenominator
  exact Nat.mul_div_cancel' T.centerContent_dvd_centerGap

/-- Negative transfer has positive content. -/
theorem centerContent_pos_of_negative
    {T : AffineTransfer}
    (hneg : T.determinant < 0) :
    0 < T.centerContent := by
  have hG : 0 < T.centerGap := T.centerGap_pos_of_negative hneg
  unfold centerContent
  exact Nat.gcd_pos_of_pos_right _ hG

/-- Primitive numerator and denominator are coprime on the negative branch. -/
theorem primitiveCenterNumerator_coprime_denominator_of_negative
    {T : AffineTransfer}
    (hneg : T.determinant < 0) :
    Nat.Coprime T.primitiveCenterNumerator T.primitiveCenterDenominator := by
  have hG : 0 < T.centerGap := T.centerGap_pos_of_negative hneg
  have hgcd :=
    Nat.gcd_div_gcd_div_gcd_of_pos_right
      (n := T.translate)
      (m := T.centerGap)
      hG
  simpa [centerContent, primitiveCenterNumerator,
    primitiveCenterDenominator, Nat.Coprime] using hgcd


/-- Signed separation of the two primitive center directions. -/
def primitiveRootSeparation (T U : AffineTransfer) : ℤ :=
  (T.primitiveCenterDenominator : ℤ) *
      (U.primitiveCenterNumerator : ℤ) -
    (U.primitiveCenterDenominator : ℤ) *
      (T.primitiveCenterNumerator : ℤ)

/--
On two negative transfers, full displacement separation factors into the two
integer contents and the primitive projective separation.
-/
theorem separation_eq_contents_mul_primitiveRootSeparation
    {T U : AffineTransfer}
    (hT : T.determinant < 0)
    (hU : U.determinant < 0) :
    T.separation U =
      (T.centerContent : ℤ) * (U.centerContent : ℤ) *
        T.primitiveRootSeparation U := by
  have hBT :
      (T.translate : ℤ) =
        (T.centerContent : ℤ) *
          (T.primitiveCenterNumerator : ℤ) := by
    exact_mod_cast T.centerContent_mul_primitiveCenterNumerator.symm
  have hBU :
      (U.translate : ℤ) =
        (U.centerContent : ℤ) *
          (U.primitiveCenterNumerator : ℤ) := by
    exact_mod_cast U.centerContent_mul_primitiveCenterNumerator.symm
  have hGT :
      (T.centerGap : ℤ) =
        (T.centerContent : ℤ) *
          (T.primitiveCenterDenominator : ℤ) := by
    exact_mod_cast T.centerContent_mul_primitiveCenterDenominator.symm
  have hGU :
      (U.centerGap : ℤ) =
        (U.centerContent : ℤ) *
          (U.primitiveCenterDenominator : ℤ) := by
    exact_mod_cast U.centerContent_mul_primitiveCenterDenominator.symm
  rw [AffineTransfer.separation_eq,
    T.determinant_eq_neg_centerGap hT,
    U.determinant_eq_neg_centerGap hU,
    hBT, hBU, hGT, hGU]
  unfold primitiveRootSeparation
  ring

end AffineTransfer
end Collatz2
