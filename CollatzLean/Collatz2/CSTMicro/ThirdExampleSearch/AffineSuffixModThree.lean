import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.ZMod.Basic

/-!
# 第3例探索 3: 右 collar の 3 進切断

full affine 定数を最後の `k` odd blocks と、それより左の部分に分ける。
左部分が `3^k` を因子に持つなら `mod 3^k` では消え、右 collar だけが残る。

第3例探索では `k = 42` を使う。これにより終点候補を巨大整数ではなく
`ZMod (3^42)` の小さい residue として扱える。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
右 `k` odd blocks の affine 定数を `suffixB`、その直前までの two-depth を
`prefixH` とした時の exact な 3 進切断。

仮定

  fullB = 3^k * leftPart + 2^prefixH * suffixB

から

  fullB = 2^prefixH * suffixB  (mod 3^k)

を得る。
-/
theorem affineConst_mod_threePow_of_suffix
    (k fullB leftPart prefixH suffixB : ℕ)
    (hSplit :
      fullB = 3 ^ k * leftPart + 2 ^ prefixH * suffixB) :
    (fullB : ZMod (3 ^ k)) =
      ((2 : ℕ) ^ prefixH : ZMod (3 ^ k)) *
        (suffixB : ZMod (3 ^ k)) := by
  rw [hSplit]
  push_cast
  have hThree :
      (3 : ZMod (3 ^ k)) ^ k = 0 := by
    exact
      ZMod.natCast_pow_eq_zero_of_le
        3 (le_rfl : k ≤ k)
  rw [hThree]
  simp

/-- 右 collar 幅を 42 odd blocks に固定した版。 -/
theorem affineConst_mod_threePow_of_suffix42
    (fullB leftPart prefixH B42 : ℕ)
    (hSplit :
      fullB = 3 ^ 42 * leftPart + 2 ^ prefixH * B42) :
    (fullB : ZMod (3 ^ 42)) =
      ((2 : ℕ) ^ prefixH : ZMod (3 ^ 42)) *
        (B42 : ZMod (3 ^ 42)) := by
  exact affineConst_mod_threePow_of_suffix
    42 fullB leftPart prefixH B42 hSplit

end ThirdExampleSearch
end CSTMicro
end Collatz2
