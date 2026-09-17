import CollatzLean.Collatz3.Core.EndpointEquation
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Core: exponent word の有理 fixed point

word `w` の affine endpoint equation

`2^H * y = 3^p * x + C`

を `ℚ` 上へ延長し、`x=y` とした fixed-point equation だけを保存する。

2-adic completion や ghost precision はここでは導入しない。
primitive は rational scale gap と fixed-point candidate だけで、
実際の Collatz orbit semantics とは独立である。
-/

namespace Collatz3
namespace Word

/-- rational scale gap `2^H - 3^p`。 -/
def fixedPointGapQ (w : Word) : ℚ :=
  (2 : ℚ) ^ twoSteps w - (3 : ℚ) ^ oddSteps w

/-- scale gap が 0 でないときの canonical rational fixed-point candidate。 -/
def fixedPointQ (w : Word) : ℚ :=
  (affineConst w : ℚ) / fixedPointGapQ w

/-- word affine transfer の rational fixed-point equation。 -/
def IsFixedPointQ (w : Word) (q : ℚ) : Prop :=
  (2 : ℚ) ^ twoSteps w * q =
    (3 : ℚ) ^ oddSteps w * q + (affineConst w : ℚ)

/-- fixed-point equation は scale gap との積の形に exact に書き換えられる。 -/
theorem isFixedPointQ_iff_gap_mul
    (w : Word) (q : ℚ) :
    IsFixedPointQ w q ↔
      fixedPointGapQ w * q = (affineConst w : ℚ) := by
  unfold IsFixedPointQ fixedPointGapQ
  constructor <;> intro h <;> linarith

/-- gap が 0 でなければ canonical candidate は実際に fixed-point equation を満たす。 -/
theorem fixedPointQ_isFixedPoint
    {w : Word}
    (hGap : fixedPointGapQ w ≠ 0) :
    IsFixedPointQ w (fixedPointQ w) := by
  rw [isFixedPointQ_iff_gap_mul]
  unfold fixedPointQ
  field_simp [hGap]

/-- affine constant が 0 なら canonical candidate も 0。 -/
@[simp] theorem fixedPointQ_eq_zero_of_affineConst_eq_zero
    {w : Word}
    (h : affineConst w = 0) :
    fixedPointQ w = 0 := by
  simp [fixedPointQ, h]

end Word
end Collatz3
