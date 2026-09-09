import CollatzLean.Collatz3.Core.WordTransfer


/-!
# Collatz3: word transfer の正の translation

actual semantics を使わず、非空 exponent word の affine translation `B` が
strict に正であることだけを pure word arithmetic として切り出す。
-/

namespace Collatz3
namespace Word

/-- 非空 word の affine translation `B` は strict に正。 -/
theorem affineConst_pos_of_nonempty
    {w : Word}
    (hne : w ≠ []) :
    0 < affineConst w := by
  cases w with
  | nil => contradiction
  | cons e w =>
      rw [affineConst_cons]
      have hPow : 0 < 3 ^ oddSteps w := by
        exact pow_pos (by decide) _
      omega

end Word
end Collatz3
