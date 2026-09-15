import CollatzLean.Collatz3.Bridge.FerrersAffineCellWeight
import CollatzLean.Collatz3.Bridge.SurvivorCriticalEscapeWeight
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: Ferrers cell weight と critical escape weight の exact 接続

1-cell move

`u ++ [a+1,b] ++ v -> u ++ [a,b+1] ++ v`

の affine numerator 寄与は

`C = 2^(twoSteps u + a) * 3^(oddSteps v)`。

moved row を

`r = oddSteps u + 1`

とする。total odd-step 数は `oddSteps u + 2 + oddSteps v` なので、
`C` を full `3^p` scale で正規化すると suffix の `3` 冪が exact に消えて

`C / 3^p = 2^(twoSteps u+a) / 3^(r+1)`。

さらに moved checkpoint が Beatty roof 以下で、

`d = beattyIndex r - (twoSteps u+a)`

とすると

`C / 3^p = criticalEscapeWeight r / 2^d`。

従って各 Young/Ferrers cell の Collatz affine 寄与は

* row `r` が決める Sturmian/Beatty phase weight
* その cell の roof defect `d` が決める dyadic attenuation

の積へ exact に分解される。
-/

namespace Collatz3
namespace Word

open Bridge

/--
1-cell affine weight を full odd-step `3^p` scale で割ると、suffix は完全に消える。
-/
theorem ferrersCellAffineWeight_div_threePow_total_eq
    (u v : Word)
    (a : ℕ) :
    (ferrersCellAffineWeight u v a : ℝ) /
        (3 : ℝ) ^ (oddSteps u + 2 + oddSteps v) =
      (2 : ℝ) ^ (twoSteps u + a) /
        (3 : ℝ) ^ (oddSteps u + 2) := by
  unfold ferrersCellAffineWeight
  push_cast
  have hThree :
      (3 : ℝ) ^ (oddSteps u + 2 + oddSteps v) =
        (3 : ℝ) ^ (oddSteps u + 2) * (3 : ℝ) ^ oddSteps v := by
    rw [show oddSteps u + 2 + oddSteps v =
        (oddSteps u + 2) + oddSteps v by omega, pow_add]
  rw [hThree]
  field_simp

/--
Ferrers 1-cell の normalized affine weight は critical escape weight を
その row の roof defect scale で割ったものに exact に一致する。

これが「Sturmian phase の exact weight × Ferrers cell の exact weight」の局所 bridge。
-/
theorem ferrersCellAffineWeight_div_threePow_total_eq_criticalEscapeWeight
    (u v : Word)
    (a : ℕ)
    (hRoof :
      twoSteps u + a ≤ Critical.beattyIndex (oddSteps u + 1)) :
    (ferrersCellAffineWeight u v a : ℝ) /
        (3 : ℝ) ^ (oddSteps u + 2 + oddSteps v) =
      criticalEscapeWeight (oddSteps u + 1) /
        (2 : ℝ) ^
          (Critical.beattyIndex (oddSteps u + 1) - (twoSteps u + a)) := by
  rw [ferrersCellAffineWeight_div_threePow_total_eq]
  unfold criticalEscapeWeight
  have hBeatty :
      twoSteps u + a +
          (Critical.beattyIndex (oddSteps u + 1) - (twoSteps u + a)) =
        Critical.beattyIndex (oddSteps u + 1) :=
    Nat.add_sub_of_le hRoof
  have hTwo :
      (2 : ℝ) ^ Critical.beattyIndex (oddSteps u + 1) =
        (2 : ℝ) ^ (twoSteps u + a) *
          (2 : ℝ) ^
            (Critical.beattyIndex (oddSteps u + 1) - (twoSteps u + a)) := by
    rw [← hBeatty, pow_add]
    simp
  rw [hTwo]
  rw [show oddSteps u + 1 + 1 = oddSteps u + 2 by omega]
  field_simp

/--
roof defect が 0 の cell では normalized cell weight は critical phase weight そのもの。
-/
theorem ferrersCellAffineWeight_div_threePow_total_eq_criticalEscapeWeight_of_roof
    (u v : Word)
    (a : ℕ)
    (hRoof :
      twoSteps u + a = Critical.beattyIndex (oddSteps u + 1)) :
    (ferrersCellAffineWeight u v a : ℝ) /
        (3 : ℝ) ^ (oddSteps u + 2 + oddSteps v) =
      criticalEscapeWeight (oddSteps u + 1) := by
  have hLe :
      twoSteps u + a ≤ Critical.beattyIndex (oddSteps u + 1) := hRoof.le
  have h :=
    ferrersCellAffineWeight_div_threePow_total_eq_criticalEscapeWeight
      u v a hLe
  rw [← hRoof] at h
  simp only [tsub_self, pow_zero, div_one] at h
  exact h

end Word
end Collatz3
