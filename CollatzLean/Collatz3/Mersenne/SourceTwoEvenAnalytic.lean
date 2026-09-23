import CollatzLean.Collatz3.Mersenne.TwoHoleFinalInternal
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Mersenne: source-two even resonance の analytic 前処理

source-two の唯一の even low resonance `(a,b)=(1,2)` を、Chim 型 3-adic two-log
estimate に渡す直前の exact 算術まで公開 theorem として固定する。

既存 `TwoHoleFinalInternal` では最終的に `2^392 ∣ k` まで証明しているが、その証明途中の

* M₄ class から `r=3` を exact に固定すること、
* 元 equation を `3^k (2^n-7) = 2^(L+3)-7` へ正規化すること、

は public API になっていなかった。

この二本を分離しておくと、次段の p-adic theorem は Collatz の six-term equation を直接
読む必要がなく、`2^(L+3)` が 7 に 3-adically 深く接近する形だけを処理すればよい。

このファイルでは新しい外部数論仮定を導入しない。
-/

namespace Collatz3
namespace Mersenne

/--
even low resonance `(a,b)=(1,2)`, `k≥7` では exit depth は exact に `r=3`。

M₄ classification の `r ≡ 3 (mod 486)` を mod 16 の元 equation と組み合わせ、
`r≥4` を排除する。
-/
theorem SourceTwoHoleEquation.evenLowResonance_exitDepth_eq_three
    {k n r L : ℕ}
    (hk7 : 7 ≤ k)
    (hEq : SourceTwoHoleEquation k n r L 1 2) :
    r = 3 := by
  have hClass :=
    hEq.evenLowResonance_m4_classification (by omega : 6 ≤ k)
  rcases hClass with ⟨hK, hN, hR, hT⟩
  have hr3le : 3 ≤ r := by
    have hle := Nat.mod_le r 486
    omega
  by_contra hne
  have hr4 : 4 ≤ r := by omega
  have hMod := hEq.to_mod 16
  unfold SourceTwoHoleModEquation at hMod
  have hKdecomp := Nat.mod_add_div (k - 6) 972
  rw [hK] at hKdecomp
  have hkForm :
      k = 972 * ((k - 6) / 972 + 1) := by
    omega
  have hk4 : k % 4 = 0 := by
    rw [hkForm]
    simp [Nat.mul_mod]
  have hThreePeriod : (3 : ZMod 16) ^ 4 = 1 := by decide
  have hThree : (3 : ZMod 16) ^ k = 1 := by
    rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 16) (e := k) hThreePeriod]
    simp [hk4]
  have hn394 : 394 ≤ n := by
    have hle := Nat.mod_le n 486
    omega
  have hL391 : 391 ≤ L := by
    have hle := Nat.mod_le L 486
    omega
  have hNZero : (2 : ZMod 16) ^ n = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : 4 ≤ n)
  have hLZero : (2 : ZMod 16) ^ L = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : 4 ≤ L)
  have hRZero : (2 : ZMod 16) ^ r = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 hr4
  rw [hThree, hNZero, hLZero, hRZero] at hMod
  norm_num at hMod
  exact (by decide : (-7 : ZMod 16) ≠ 1) hMod

/--
even low resonance の exact p-adic target identity。

`r=3` を元の source-two equation に代入すると

`3^k (2^n - 7) = 2^(L+3) - 7`

となる。次段では右辺の 3-adic valuation を Chim 型 two-log estimate で抑える。
-/
theorem SourceTwoHoleEquation.evenLowResonance_integer_identity
    {k n r L : ℕ}
    (hk7 : 7 ≤ k)
    (hEq : SourceTwoHoleEquation k n r L 1 2) :
    (3 : ℤ) ^ k * ((2 : ℤ) ^ n - 7) =
      (2 : ℤ) ^ (L + 3) - 7 := by
  have hr3 := hEq.evenLowResonance_exitDepth_eq_three hk7
  unfold SourceTwoHoleEquation at hEq
  rw [hr3] at hEq
  norm_num at hEq
  rw [pow_add]
  norm_num
  linear_combination hEq

end Mersenne
end Collatz3
