import CollatzLean.Collatz3.Arithmetic.Pow23
import Mathlib.Data.ZMod.Basic

/-!
# Collatz3 Arithmetic: 3冪法上の `2^E` 線形合同式

既存 `ModTwoPow` の 2/3 を交換した companion。
`ZMod` はこの arithmetic 層に閉じ込め、後段では inverse の存在と一意性だけを使う。
-/

namespace Collatz3
namespace Arithmetic

/-- 3冪法。 -/
def threePowModulus (K : ℕ) : ℕ :=
  3 ^ K

@[simp] theorem threePowModulus_pos (K : ℕ) :
    0 < threePowModulus K := by
  simp [threePowModulus]

/-- `ZMod (3^K)` における `2^E` の単元。 -/
def twoPowUnit (E K : ℕ) : (ZMod (threePowModulus K))ˣ :=
  ZMod.unitOfCoprime
    (2 ^ E)
    (by
      simpa [threePowModulus] using
        (coprime_threePow_twoPow K E).symm)

/-- `2^E * y = rhs (mod 3^K)` の一意解。 -/
def solveTwoPow
    (E K : ℕ)
    (rhs : ZMod (threePowModulus K)) :
    ZMod (threePowModulus K) :=
  (↑((twoPowUnit E K)⁻¹) : ZMod (threePowModulus K)) * rhs

/-- `solveTwoPow` は defining congruence を満たす。 -/
theorem twoPow_mul_solveTwoPow
    (E K : ℕ)
    (rhs : ZMod (threePowModulus K)) :
    (((2 ^ E : ℕ) : ZMod (threePowModulus K)) *
        solveTwoPow E K rhs) = rhs := by
  have hleading :
      (((2 ^ E : ℕ) : ZMod (threePowModulus K))) =
        (↑(twoPowUnit E K) : ZMod (threePowModulus K)) := by
    simp [twoPowUnit, threePowModulus]
    rfl
  rw [hleading]
  simp [solveTwoPow]

/-- defining congruence の解は `solveTwoPow` に一意。 -/
theorem solveTwoPow_unique
    (E K : ℕ)
    (rhs y : ZMod (threePowModulus K))
    (hy :
      (((2 ^ E : ℕ) : ZMod (threePowModulus K)) * y) = rhs) :
    y = solveTwoPow E K rhs := by
  have hleading :
      (((2 ^ E : ℕ) : ZMod (threePowModulus K))) =
        (↑(twoPowUnit E K) : ZMod (threePowModulus K)) := by
    simp [twoPowUnit, threePowModulus]
    rfl
  rw [hleading] at hy
  calc
    y =
        (↑((twoPowUnit E K)⁻¹) : ZMod (threePowModulus K)) *
          ((↑(twoPowUnit E K) : ZMod (threePowModulus K)) * y) := by simp
    _ =
        (↑((twoPowUnit E K)⁻¹) : ZMod (threePowModulus K)) * rhs := by
          rw [hy]
    _ = solveTwoPow E K rhs := rfl

end Arithmetic
end Collatz3
