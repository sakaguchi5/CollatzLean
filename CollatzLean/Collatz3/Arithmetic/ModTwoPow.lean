import CollatzLean.Collatz3.Arithmetic.Pow23
import Mathlib.Data.ZMod.Basic

/-!
# Collatz3: 2冪法上の `3^p` 線形合同式

`ZMod` は基礎層全体へ拡散させず、2冪合同式を一意に解くための
証明装置としてこの層に閉じ込める。
-/

namespace Collatz3
namespace Arithmetic

/-- 2冪法。 -/
def twoPowModulus (H : ℕ) : ℕ :=
  2 ^ H

@[simp] theorem twoPowModulus_pos (H : ℕ) :
    0 < twoPowModulus H := by
  simp [twoPowModulus]

/-- `ZMod (2^H)` における `3^p` の単元。 -/
def threePowUnit (p H : ℕ) : (ZMod (twoPowModulus H))ˣ :=
  ZMod.unitOfCoprime
    (3 ^ p)
    (by simpa [twoPowModulus] using coprime_threePow_twoPow p H)

/-- `3^p * x = rhs (mod 2^H)` の一意解。 -/
def solveThreePow
    (p H : ℕ)
    (rhs : ZMod (twoPowModulus H)) :
    ZMod (twoPowModulus H) :=
  (↑((threePowUnit p H)⁻¹) : ZMod (twoPowModulus H)) * rhs

/-- `solveThreePow` は defining congruence を満たす。 -/
theorem threePow_mul_solveThreePow
    (p H : ℕ)
    (rhs : ZMod (twoPowModulus H)) :
    (((3 ^ p : ℕ) : ZMod (twoPowModulus H)) *
        solveThreePow p H rhs) = rhs := by
  have hleading :
      (((3 ^ p : ℕ) : ZMod (twoPowModulus H))) =
        (↑(threePowUnit p H) : ZMod (twoPowModulus H)) := by
    simp [threePowUnit, twoPowModulus]
    rfl
  rw [hleading]
  simp [solveThreePow]

/-- defining congruence の解は `solveThreePow` に一意。 -/
theorem solveThreePow_unique
    (p H : ℕ)
    (rhs x : ZMod (twoPowModulus H))
    (hx :
      (((3 ^ p : ℕ) : ZMod (twoPowModulus H)) * x) = rhs) :
    x = solveThreePow p H rhs := by
  have hleading :
      (((3 ^ p : ℕ) : ZMod (twoPowModulus H))) =
        (↑(threePowUnit p H) : ZMod (twoPowModulus H)) := by
    simp [threePowUnit, twoPowModulus]
    rfl
  rw [hleading] at hx
  calc
    x =
        (↑((threePowUnit p H)⁻¹) : ZMod (twoPowModulus H)) *
          ((↑(threePowUnit p H) : ZMod (twoPowModulus H)) * x) := by simp
    _ =
        (↑((threePowUnit p H)⁻¹) : ZMod (twoPowModulus H)) * rhs := by
          rw [hx]
    _ = solveThreePow p H rhs := rfl

end Arithmetic
end Collatz3
