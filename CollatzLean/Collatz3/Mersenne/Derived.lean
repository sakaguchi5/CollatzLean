import CollatzLean.Collatz3.Mersenne.Basic
import CollatzLean.Collatz3.Mersenne.MacroLine
import CollatzLean.Collatz3.Arithmetic.Pow23

import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: BlockData / affine line の derived facts

`BlockData` に新しい field を増やさず、既存の defining equations から
一意性と affine action の合成則を導く。
-/

namespace Collatz3
namespace Mersenne

namespace BlockData

/-- 同じ `(d,u)` なら source は一意。 -/
theorem start_eq_of_same_parameter
    {d r₁ r₂ u x z y₁ y₂ : ℕ}
    (h₁ : BlockData d r₁ u x y₁)
    (h₂ : BlockData d r₂ u z y₂) :
    x = z := by
  have hEq : x + 1 = z + 1 :=
    h₁.startEquation.trans h₂.startEquation.symm
  omega

/-- 同じ `(d,r,u)` なら macro endpoint は一意。 -/
theorem end_eq_of_same_parameter
    {d r u x₁ x₂ y z : ℕ}
    (h₁ : BlockData d r u x₁ y)
    (h₂ : BlockData d r u x₂ z) :
    y = z := by
  have hEq : 2 ^ r * y + 1 = 2 ^ r * z + 1 :=
    h₁.endEquation.trans h₂.endEquation.symm
  have hMul : 2 ^ r * y = 2 ^ r * z := by
    omega
  exact Nat.mul_left_cancel (Arithmetic.twoPow_pos r) hMul

end BlockData

/-- parameter lift は加法 parameter の action。 -/
theorem blockParameterLift_add
    (r u s t : ℕ) :
    blockParameterLift r (blockParameterLift r u s) t =
      blockParameterLift r u (s + t) := by
  unfold blockParameterLift
  ring

/-- source lift は加法 parameter の action。 -/
theorem blockSourceLift_add
    (d r x s t : ℕ) :
    blockSourceLift d r (blockSourceLift d r x s) t =
      blockSourceLift d r x (s + t) := by
  unfold blockSourceLift
  ring

/-- endpoint lift も同じ加法 parameter の action。 -/
theorem blockEndpointLift_add
    (d y s t : ℕ) :
    blockEndpointLift d (blockEndpointLift d y s) t =
      blockEndpointLift d y (s + t) := by
  unfold blockEndpointLift
  ring

end Mersenne
end Collatz3
