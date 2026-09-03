import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.AffinePrefixModTwo
import Mathlib.Data.ZMod.Basic

/-!
# 第3例探索 2: 左 68 block から開始値 residue を決める

`2^68` を法にすると 3 は可逆である。
そのため

  3^68 n + B68 = 0  (mod 2^68)

という条件は `n mod 2^68` を一意に決める。

巨大な `G = 2^(H+1) - 3^(p+1)` を作らずに、開始値側を 68 bit collar へ
切り落とすための exact な式である。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- `3^68` の `mod 2^68` における逆元を Nat の代表元で固定する。 -/
def prefix68Inverse : ℕ := 129791399679377382321

/--
上の定数が本当に `3^68` の逆元であることを kernel で確認する。
数値は固定なので、探索中に逆元計算を繰り返す必要はない。
-/
theorem prefix68Inverse_spec :
    ((prefix68Inverse : ZMod (2 ^ 68)) *
        ((3 : ℕ) ^ 68 : ZMod (2 ^ 68))) = 1 := by
  decide

/--
左 68 block が与える affine residue から、開始値の `ZMod (2^68)` 値を exact に復元する。

`hResidue` は full affine equation を `mod 2^68` に落とした時に得られる条件である。
開始値に別の候補はない。
-/
theorem startValue_eq_prefix68Residue
    (n B68 : ℕ)
    (hResidue :
      (((3 : ℕ) ^ 68 : ZMod (2 ^ 68)) * (n : ZMod (2 ^ 68)) +
        (B68 : ZMod (2 ^ 68))) = 0) :
    (n : ZMod (2 ^ 68)) =
      - (prefix68Inverse : ZMod (2 ^ 68)) *
        (B68 : ZMod (2 ^ 68)) := by
  have h3 :
      (((3 : ℕ) ^ 68 : ZMod (2 ^ 68)) * (n : ZMod (2 ^ 68))) =
        - (B68 : ZMod (2 ^ 68)) := by
    calc
      (((3 : ℕ) ^ 68 : ZMod (2 ^ 68)) * (n : ZMod (2 ^ 68))) =
          ((((3 : ℕ) ^ 68 : ZMod (2 ^ 68)) * (n : ZMod (2 ^ 68)) +
            (B68 : ZMod (2 ^ 68))) - (B68 : ZMod (2 ^ 68))) := by ring
      _ = - (B68 : ZMod (2 ^ 68)) := by rw [hResidue]; ring
  calc
    (n : ZMod (2 ^ 68)) =
        1 * (n : ZMod (2 ^ 68)) := by ring
    _ = ((prefix68Inverse : ZMod (2 ^ 68)) *
          ((3 : ℕ) ^ 68 : ZMod (2 ^ 68))) *
          (n : ZMod (2 ^ 68)) := by rw [prefix68Inverse_spec]
    _ = (prefix68Inverse : ZMod (2 ^ 68)) *
          (((3 : ℕ) ^ 68 : ZMod (2 ^ 68)) *
            (n : ZMod (2 ^ 68))) := by ring
    _ = (prefix68Inverse : ZMod (2 ^ 68)) *
          (-(B68 : ZMod (2 ^ 68))) := by rw [h3]
    _ = - (prefix68Inverse : ZMod (2 ^ 68)) *
          (B68 : ZMod (2 ^ 68)) := by ring

end ThirdExampleSearch
end CSTMicro
end Collatz2
