import CollatzLean.Collatz3.Core.WordFixedPoint
import CollatzLean.Collatz3.Arithmetic.Pow23



/-!
# Collatz3 Core: rational fixed point の derived facts

O1 の `fixedPointQ` から一意性と符号だけを導く。
2-adic object はまだ導入しない。
-/

namespace Collatz3
namespace Word

/-- 非空 exponent word の affine constant は正。 -/
theorem affineConst_pos_of_nonempty
    {w : Word}
    (hne : w ≠ []) :
    0 < affineConst w := by
  cases w with
  | nil => contradiction
  | cons e w =>
      rw [affineConst_cons]
      have h3 := Arithmetic.threePow_pos (oddSteps w)
      omega

/-- gap が非零なら rational fixed point は一意。 -/
theorem isFixedPointQ_unique
    {w : Word} {q r : ℚ}
    (hGap : fixedPointGapQ w ≠ 0)
    (hq : IsFixedPointQ w q)
    (hr : IsFixedPointQ w r) :
    q = r := by
  have hq' := (isFixedPointQ_iff_gap_mul w q).1 hq
  have hr' := (isFixedPointQ_iff_gap_mul w r).1 hr
  have hZero : fixedPointGapQ w * (q - r) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hZero with h | h
  · exact False.elim (hGap h)
  · linarith

/-- gap が非零なら任意の fixed point は canonical `fixedPointQ` に一致する。 -/
theorem isFixedPointQ_eq_fixedPointQ
    {w : Word} {q : ℚ}
    (hGap : fixedPointGapQ w ≠ 0)
    (hq : IsFixedPointQ w q) :
    q = fixedPointQ w :=
  isFixedPointQ_unique hGap hq (fixedPointQ_isFixedPoint hGap)

/-- 非空 word で scale gap が負なら canonical rational ghost も負。 -/
theorem fixedPointQ_neg_of_gap_neg_nonempty
    {w : Word}
    (hne : w ≠ [])
    (hGap : fixedPointGapQ w < 0) :
    fixedPointQ w < 0 := by
  have hGapNe : fixedPointGapQ w ≠ 0 := ne_of_lt hGap
  have hFix := fixedPointQ_isFixedPoint hGapNe
  have hMul := (isFixedPointQ_iff_gap_mul w (fixedPointQ w)).1 hFix
  have hConstNat := affineConst_pos_of_nonempty hne
  have hConst : (0 : ℚ) < (affineConst w : ℚ) := by
    exact_mod_cast hConstNat
  nlinarith

/-- 非空 word で scale gap が正なら canonical fixed point は正。 -/
theorem fixedPointQ_pos_of_gap_pos_nonempty
    {w : Word}
    (hne : w ≠ [])
    (hGap : 0 < fixedPointGapQ w) :
    0 < fixedPointQ w := by
  have hGapNe : fixedPointGapQ w ≠ 0 := ne_of_gt hGap
  have hFix := fixedPointQ_isFixedPoint hGapNe
  have hMul := (isFixedPointQ_iff_gap_mul w (fixedPointQ w)).1 hFix
  have hConstNat := affineConst_pos_of_nonempty hne
  have hConst : (0 : ℚ) < (affineConst w : ℚ) := by
    exact_mod_cast hConstNat
  nlinarith

end Word
end Collatz3
