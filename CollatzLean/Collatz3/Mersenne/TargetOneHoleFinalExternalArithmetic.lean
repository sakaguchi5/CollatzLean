import CollatzLean.Collatz3.Mersenne.TargetOneHoleQOneArithmetic
import CollatzLean.Collatz3.Mersenne.TargetOneHoleQGeTwoArithmetic
import CollatzLean.Collatz3.Mersenne.AtMostOneHoleExternalClosure

/-!
# Collatz3 Mersenne: A1 の最終外部算術 interface

A1 の四枝

* A: even, `q = 1`
* B: even, `q ≥ 2`
* C: odd,  `q = 1`
* D: odd,  `q ≥ 2`

の解析的 depth bound はすべて repo 内へ移した。

* A/C (`q=1`): exact three-log identity + Baker--Wüstholz から `k<10^23`。
* B/D (`q≥2`): top/bottom 二本の exact three-log identity + Baker--Wüstholz から
  gcd 仮定なしで `k<2^101`。

A/C の bounded residual は既存 M₄ certificate ですでに内部排除済み。
従ってこの final external package に残るのは B/D (`q≥2`) の
bounded finite sieve 二本だけである。

旧 `TargetOneHoleExternalArithmetic` は互換性のため derived theorem として再構成する。
旧 API の `k<10^45` bound は、内部 `k<2^101` を弱めて返す。
旧 finite-sieve field に `k<10^45` が渡された場合も、その仮定には依存せず
内部 theorem から `k<2^101` を再構成して sharpened sieve を呼ぶ。
-/

namespace Collatz3
namespace Mersenne

/-- 旧コード向けの互換名。A/C の bound 自体は repo 内で証明される。 -/
abbrev targetOneQOneExternalDepthBound : ℕ :=
  targetOneQOneInternalDepthBound

/-- final A1 で B/D finite sieve に渡す sharpened bound。 -/
abbrev targetOneQGeTwoExternalDepthBound : ℕ :=
  targetOneQGeTwoInternalDepthBound

/--
A1 の最終外部算術 package。

A/C は解析・有限部分とも内部化済み。
B/D も解析 bound は内部化済みなので、外部 field として残るのは
`k<2^101` の bounded residual を排除する finite certificate だけである。
-/
structure TargetOneHoleFinalExternalArithmetic : Prop where
  /-- B (`even,q≥2`) の `k<2^101` bounded residual を排除する finite certificate。 -/
  even_q_ge_two_finite_sieve :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 1 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 0 →
      h.q < h.t →
      2 ≤ h.q →
      Nat.gcd h.q h.t = 1 →
      k < targetOneQGeTwoExternalDepthBound →
      False

  /-- D (`odd,q≥2`) の `k<2^101` bounded residual を排除する finite certificate。 -/
  odd_q_ge_two_finite_sieve :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 2 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 1 →
      h.q < h.t →
      2 ≤ h.q →
      Nat.gcd h.q h.t = 1 →
      k < targetOneQGeTwoExternalDepthBound →
      False

/-! ## 四枝 closure: analytic bound は全て内部、B/D finite sieve だけ external -/

/-- A (`even,q=1`) は final package に依存せず内部 theorem で閉じる。 -/
theorem TargetOneHoleFinalExternalArithmetic.even_q_one_impossible
    (_A : TargetOneHoleFinalExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hqOne : h.q = 1) :
    False :=
  h.even_q_one_impossible_internal hk hn hkEven hqt hqOne

/--
B (`even,q≥2`) は gcd 仮定なしの内部 `k<2^101` bound と
bounded finite sieve の合成で閉じる。
-/
theorem TargetOneHoleFinalExternalArithmetic.even_q_ge_two_impossible
    (A : TargetOneHoleFinalExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hGcd : Nat.gcd h.q h.t = 1) :
    False := by
  have hBound :=
    h.even_q_ge_two_internal_depth_bound hk hn hkEven hqt hqTwo
  exact
    A.even_q_ge_two_finite_sieve
      h hk hn hkEven hqt hqTwo hGcd hBound

/-- C (`odd,q=1`) も final package に依存せず内部 theorem で閉じる。 -/
theorem TargetOneHoleFinalExternalArithmetic.odd_q_one_impossible
    (_A : TargetOneHoleFinalExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hqOne : h.q = 1) :
    False :=
  h.odd_q_one_impossible_internal hk hn hkOdd hqt hqOne

/--
D (`odd,q≥2`) も gcd 仮定なしの内部 `k<2^101` bound と
bounded finite sieve の合成で閉じる。
-/
theorem TargetOneHoleFinalExternalArithmetic.odd_q_ge_two_impossible
    (A : TargetOneHoleFinalExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hGcd : Nat.gcd h.q h.t = 1) :
    False := by
  have hBound :=
    h.odd_q_ge_two_internal_depth_bound hk hn hkOdd hqt hqTwo
  exact
    A.odd_q_ge_two_finite_sieve
      h hk hn hkOdd hqt hqTwo hGcd hBound

/-! ## 旧 A1 interface への互換 bridge -/

/-- `2^101 < 10^45`。旧 external API の bound へ弱めるための数値 bridge。 -/
private theorem qGeTwoInternalDepthBound_lt_oldExternal :
    targetOneQGeTwoInternalDepthBound < targetOneExternalDepthBound := by
  norm_num [targetOneQGeTwoInternalDepthBound, targetOneExternalDepthBound]

/--
最終 A1 package から従来の `TargetOneHoleExternalArithmetic` を構成する。

A/C は internal theorem で埋める。
B/D の旧 `k<10^45` field は内部 `k<2^101` theorem を弱めて埋める。
旧 finite-sieve field に渡される `k<10^45` は使用せず、内部 sharpened bound を再計算する。
-/
theorem TargetOneHoleFinalExternalArithmetic.toExternalArithmetic
    (A : TargetOneHoleFinalExternalArithmetic) :
    TargetOneHoleExternalArithmetic where
  even_q_one_impossible := by
    intro k n L b h hk hn hkEven hqt hqOne
    exact h.even_q_one_impossible_internal hk hn hkEven hqt hqOne
  odd_q_one_impossible := by
    intro k n L b h hk hn hkOdd hqt hqOne
    exact h.odd_q_one_impossible_internal hk hn hkOdd hqt hqOne
  even_q_ge_two_bound := by
    intro k n L b h hk hn hkEven hqt hqTwo _hGcd
    exact lt_trans
      (h.even_q_ge_two_internal_depth_bound hk hn hkEven hqt hqTwo)
      qGeTwoInternalDepthBound_lt_oldExternal
  odd_q_ge_two_bound := by
    intro k n L b h hk hn hkOdd hqt hqTwo _hGcd
    exact lt_trans
      (h.odd_q_ge_two_internal_depth_bound hk hn hkOdd hqt hqTwo)
      qGeTwoInternalDepthBound_lt_oldExternal
  even_q_ge_two_finite_sieve := by
    intro k n L b h hk hn hkEven hqt hqTwo hGcd _hOldBound
    have hBound :=
      h.even_q_ge_two_internal_depth_bound hk hn hkEven hqt hqTwo
    exact
      A.even_q_ge_two_finite_sieve
        h hk hn hkEven hqt hqTwo hGcd hBound
  odd_q_ge_two_finite_sieve := by
    intro k n L b h hk hn hkOdd hqt hqTwo hGcd _hOldBound
    have hBound :=
      h.odd_q_ge_two_internal_depth_bound hk hn hkOdd hqt hqTwo
    exact
      A.odd_q_ge_two_finite_sieve
        h hk hn hkOdd hqt hqTwo hGcd hBound

/-! ## final A1 package から既存 closure を一本で回収 -/

/--
最終 A1 package の下では、well-formed target-one equation の depth は `k ≤ 5`。

A/C は完全内部、B/D は内部 three-log bound + final finite sieve で閉じる。
non-primitive `n=3, gcd(q,t)=2` は既存 base-64 descent を通って同じ四枝へ戻る。
-/
theorem TargetOneHoleEquation.depth_le_five_of_final_external
    (A : TargetOneHoleFinalExternalArithmetic)
    {k n r L b : ℕ}
    (hn : 0 < n)
    (hr : 0 < r)
    (hb : 0 < b)
    (hbL : b < L)
    (hEq : TargetOneHoleEquation k n r L b) :
    k ≤ 5 := by
  exact
    hEq.depth_le_five_of_external
      A.toExternalArithmetic hn hr hb hbL

/--
最終 A1 package から `AtMostOneHoleDepthBound` を直接得る。

source-one / no-hole は既存内部証明、target-one の解析 bound も全て内部証明。
外部入力として残るのは B/D の sharpened bounded finite sieve 二本だけである。
-/
theorem atMostOneHoleDepthBound_of_final_external
    (A : TargetOneHoleFinalExternalArithmetic) :
    AtMostOneHoleDepthBound := by
  exact atMostOneHoleDepthBound_of_external A.toExternalArithmetic

end Mersenne
end Collatz3
