import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.GapOneSuffixHenselBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint

/-!
# 第3例探索: 42段 Hensel recurrence の剰余完全性

`y < 3^42` を仮定して integer `y` 全体を42桁で復元する必要はない。
第3例 verifier が必要とするのが `y mod 3^42` だけなら、
通常の3進 digit を42段積み上げれば、その剰余は任意の大きさの `y` に対して完全に決まる。

このファイルでは

  canonicalLift_r(y) = y mod 3^(r+1)

を上界仮定なしで示し、さらに 0,...,41 の42個の digit を順に積む fold が
exact に `y mod 3^42` へ到達することを証明する。

従って旧 D4 の `y < 3^42` は、42桁 residue verifier の soundness には不要である。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
`r` 桁 prefix と次 digit を合わせた canonical lift は必ず `3^(r+1)` 未満。

これは「mod が同じ」から actual residue の等号へ上げるための小さい範囲補題である。
-/
theorem gapOneCanonicalHenselLift_lt_nextPow
    (y r : ℕ) :
    gapOneCanonicalHenselLift y r < 3 ^ (r + 1) := by
  unfold gapOneCanonicalHenselLift
    gapOneThreeAdicPrefix
    gapOneThreeAdicDigit
  have hPrefix :
      y % 3 ^ r < 3 ^ r := by
    exact Nat.mod_lt _ (by positivity)
  have hDigitLt :
      (y / 3 ^ r) % 3 < 3 := by
    exact Nat.mod_lt _ (by norm_num)
  have hDigitLe :
      (y / 3 ^ r) % 3 ≤ 2 := by
    omega
  have hMul :
      ((y / 3 ^ r) % 3) * 3 ^ r ≤
        2 * 3 ^ r :=
    Nat.mul_le_mul_right (3 ^ r) hDigitLe
  have hSum :
      y % 3 ^ r + ((y / 3 ^ r) % 3) * 3 ^ r <
        3 ^ r + 2 * 3 ^ r :=
    Nat.add_lt_add_of_lt_of_le hPrefix hMul
  rw [pow_succ]
  omega

/--
canonical lift は単に actual `y` の `mod 3^(r+1)` 代表元そのもの。

`y` の大きさには何の上界も仮定しない。
-/
theorem gapOneCanonicalHenselLift_eq_mod_next
    (y r : ℕ) :
    gapOneCanonicalHenselLift y r =
      y % (3 ^ (r + 1)) := by
  have hMod := gapOneCanonicalHenselLift_mod_next y r
  have hLt := gapOneCanonicalHenselLift_lt_nextPow y r
  rw [Nat.mod_eq_of_lt hLt] at hMod
  exact hMod

/--
最初の `r` 個の actual ternary digit を下位から順に積み上げる決定的 fold。

探索器で使う最終形は boundary 側から digit を供給する版になるが、
まず actual integer の digit 列について residue 完全性を固定する。
-/
def gapOneHenselPrefixFold
    (y : ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 =>
      gapOneHenselPrefixFold y r +
        gapOneThreeAdicDigit y r * 3 ^ r

@[simp] theorem gapOneHenselPrefixFold_zero
    (y : ℕ) :
    gapOneHenselPrefixFold y 0 = 0 := rfl

@[simp] theorem gapOneHenselPrefixFold_succ
    (y r : ℕ) :
    gapOneHenselPrefixFold y (r + 1) =
      gapOneHenselPrefixFold y r +
        gapOneThreeAdicDigit y r * 3 ^ r := rfl

/--
`r` 回の決定的 fold は exact に `r` 桁 ternary prefix、すなわち `y mod 3^r`。
-/
theorem gapOneHenselPrefixFold_eq_prefix
    (y r : ℕ) :
    gapOneHenselPrefixFold y r =
      gapOneThreeAdicPrefix y r := by
  induction r with
  | zero =>
      simp [gapOneHenselPrefixFold, gapOneThreeAdicPrefix]
      omega
  | succ r ih =>
      rw [gapOneHenselPrefixFold_succ, ih]
      change
        gapOneCanonicalHenselLift y r =
          gapOneThreeAdicPrefix y (r + 1)
      rw [gapOneCanonicalHenselLift_eq_mod_next]
      rfl

/--
第3例 right collar 用の42段 Hensel residue。

0,...,41 の42 digit を積み上げるだけなので、巨大軌道や巨大 affine constant は生成しない。
-/
def thirdExampleHensel42Residue
    (y : ℕ) : ℕ :=
  gapOneHenselPrefixFold y 42

/-- 42段 fold は exact に `y mod 3^42`。 -/
theorem thirdExampleHensel42Residue_eq_mod
    (y : ℕ) :
    thirdExampleHensel42Residue y =
      y % thirdExampleRightModulus := by
  unfold thirdExampleHensel42Residue
  rw [gapOneHenselPrefixFold_eq_prefix]
  rfl

/-- 42段 fold の結果は canonical representative なので必ず `3^42` 未満。 -/
theorem thirdExampleHensel42Residue_lt_rightModulus
    (y : ℕ) :
    thirdExampleHensel42Residue y <
      thirdExampleRightModulus := by
  rw [thirdExampleHensel42Residue_eq_mod]
  exact Nat.mod_lt _ thirdExampleRightModulus_pos

/--
42段 fold の Nat 値は `ZMod (3^42)` における actual `y` の代表元と一致する。
-/
theorem thirdExampleHensel42Residue_eq_rightZMod_val
    (y : ℕ) :
    thirdExampleHensel42Residue y =
      (y : ZMod thirdExampleRightModulus).val := by
  rw [thirdExampleHensel42Residue_eq_mod]
  simp [ZMod.val_natCast]

/--
特に 41 番目の canonical one-step lift だけを見ても、42桁 residue そのものが得られる。
-/
theorem gapOneHenselCandidateValue_fortyOne_eq_mod_fortyTwo
    (y : ℕ) :
    gapOneHenselCandidateValue y 41 =
      y % thirdExampleRightModulus := by
  rw [gapOneHenselCandidateValue_eq]
  simpa [thirdExampleRightModulus] using
    gapOneCanonicalHenselLift_eq_mod_next y 41

end ThirdExampleSearch
end CSTMicro
end Collatz2
