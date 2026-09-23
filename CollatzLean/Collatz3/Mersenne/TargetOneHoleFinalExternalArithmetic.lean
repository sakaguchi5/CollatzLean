import CollatzLean.Collatz3.Mersenne.TargetOneHoleQOneArithmetic
import CollatzLean.Collatz3.Mersenne.TargetOneHoleQGeTwoArithmetic
import CollatzLean.Collatz3.Mersenne.TargetOneHoleQGeTwoFinite
import CollatzLean.Collatz3.Mersenne.AtMostOneHoleExternalClosure

/-!
# Collatz3 Mersenne: A1 の完全内部化と旧 external API 互換層

A1 の四枝

* A: even, `q = 1`
* B: even, `q ≥ 2`
* C: odd,  `q = 1`
* D: odd,  `q ≥ 2`

はすべて repo 内で閉じた。

* A/C: exact three-log identity + Baker--Wüstholz + M₄ finite certificate。
* B/D: top/bottom exact three-log identityから `k<2^101`、その後 M₄ 上で
  `nq,nt` の位相を独立な 486 通り全部まで自由化した finite certificate。

B/D の解析 bound だけでなく finite sieve も `gcd(q,t)=1` を必要としない。
従って A1 固有の外部算術 field は 0 個になった。

このファイルでは旧 API との互換性のため
`TargetOneHoleFinalExternalArithmetic` という型名と dot-notation を残すが、
中身は引数なし constructor だけで、旧 `TargetOneHoleExternalArithmetic` を
内部 theorem だけから再構成する。
-/

namespace Collatz3
namespace Mersenne

/-- 旧コード向けの互換名。A/C の bound は repo 内で証明される。 -/
abbrev targetOneQOneExternalDepthBound : ℕ :=
  targetOneQOneInternalDepthBound

/-- 旧コード向けの互換名。B/D の sharpened bound は `2^101`。 -/
abbrev targetOneQGeTwoExternalDepthBound : ℕ :=
  targetOneQGeTwoInternalDepthBound

/--
A1 の最終 package はもはや外部算術 field を持たない。

型名と dot-notation API を維持するため、引数なし constructor だけを残す。
-/
inductive TargetOneHoleFinalExternalArithmetic : Prop where
  | intro : TargetOneHoleFinalExternalArithmetic

/-- A1 の最終 package の canonical internal witness。 -/
theorem targetOneHoleFinalExternalArithmetic_internal :
    TargetOneHoleFinalExternalArithmetic :=
  TargetOneHoleFinalExternalArithmetic.intro

/-! ## 旧 finite-sieve field 名の互換 theorem -/

/--
旧 final package の B finite-sieve field と同じ呼び出し形を維持する。
現在は package field ではなく内部 M₄ theorem の wrapper。
-/
theorem TargetOneHoleFinalExternalArithmetic.even_q_ge_two_finite_sieve
    (_A : TargetOneHoleFinalExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (_hGcd : Nat.gcd h.q h.t = 1)
    (hBound : k < targetOneQGeTwoExternalDepthBound) :
    False :=
  h.even_q_ge_two_internal_finite_sieve
    hk hn hkEven hqt hqTwo hBound

/-- 旧 final package の D finite-sieve field 名も同様に維持する。 -/
theorem TargetOneHoleFinalExternalArithmetic.odd_q_ge_two_finite_sieve
    (_A : TargetOneHoleFinalExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (_hGcd : Nat.gcd h.q h.t = 1)
    (hBound : k < targetOneQGeTwoExternalDepthBound) :
    False :=
  h.odd_q_ge_two_internal_finite_sieve
    hk hn hkOdd hqt hqTwo hBound

/-! ## 四枝 closure: A/B/C/D 全て internal -/

/-- A (`even,q=1`) は内部 theorem だけで閉じる。 -/
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

/-- B (`even,q≥2`) も内部 three-log + M₄ sieve だけで閉じる。 -/
theorem TargetOneHoleFinalExternalArithmetic.even_q_ge_two_impossible
    (_A : TargetOneHoleFinalExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (_hGcd : Nat.gcd h.q h.t = 1) :
    False :=
  h.even_q_ge_two_impossible_internal hk hn hkEven hqt hqTwo

/-- C (`odd,q=1`) も内部 theorem だけで閉じる。 -/
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

/-- D (`odd,q≥2`) も内部 three-log + M₄ sieve だけで閉じる。 -/
theorem TargetOneHoleFinalExternalArithmetic.odd_q_ge_two_impossible
    (_A : TargetOneHoleFinalExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (_hGcd : Nat.gcd h.q h.t = 1) :
    False :=
  h.odd_q_ge_two_impossible_internal hk hn hkOdd hqt hqTwo

/-! ## 旧 A1 external interface への完全内部 bridge -/

/-- `2^101 < 10^45`。旧 external API の bound へ弱めるための数値 bridge。 -/
private theorem qGeTwoInternalDepthBound_lt_oldExternal :
    targetOneQGeTwoInternalDepthBound < targetOneExternalDepthBound := by
  norm_num [targetOneQGeTwoInternalDepthBound, targetOneExternalDepthBound]

/--
従来の `TargetOneHoleExternalArithmetic` を外部入力なしで構成する。

A/C は既存 internal closure、B/D は今回の internal depth bound + finite sieve で埋める。
旧 API の `k<10^45` は内部 `k<2^101` を弱めて返す。
-/
theorem TargetOneHoleFinalExternalArithmetic.toExternalArithmetic
    (_A : TargetOneHoleFinalExternalArithmetic) :
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
    intro k n L b h hk hn hkEven hqt hqTwo _hGcd _hOldBound
    exact h.even_q_ge_two_impossible_internal hk hn hkEven hqt hqTwo
  odd_q_ge_two_finite_sieve := by
    intro k n L b h hk hn hkOdd hqt hqTwo _hGcd _hOldBound
    exact h.odd_q_ge_two_impossible_internal hk hn hkOdd hqt hqTwo

/-- 旧 A1 interface の canonical internal witness。 -/
theorem targetOneHoleExternalArithmetic_internal :
    TargetOneHoleExternalArithmetic :=
  TargetOneHoleFinalExternalArithmetic.toExternalArithmetic
    targetOneHoleFinalExternalArithmetic_internal

/-! ## A1 完全内部 closure -/

/--
互換 package を引数に取る旧 theorem を経由して、target-one の `k≤5` を無条件に回収する。
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
      (TargetOneHoleFinalExternalArithmetic.toExternalArithmetic A)
      hn hr hb hbL

/-- well-formed target-one equation の depth は外部 package なしで `k≤5`。 -/
theorem TargetOneHoleEquation.depth_le_five_internal
    {k n r L b : ℕ}
    (hn : 0 < n)
    (hr : 0 < r)
    (hb : 0 < b)
    (hbL : b < L)
    (hEq : TargetOneHoleEquation k n r L b) :
    k ≤ 5 := by
  exact hEq.depth_le_five_of_final_external
    targetOneHoleFinalExternalArithmetic_internal hn hr hb hbL

/--
旧 final package API から `AtMostOneHoleDepthBound` を回収する互換 theorem。
package 自体はデータを持たないので数学的仮定は増えない。
-/
theorem atMostOneHoleDepthBound_of_final_external
    (A : TargetOneHoleFinalExternalArithmetic) :
    AtMostOneHoleDepthBound := by
  exact atMostOneHoleDepthBound_of_external
    (TargetOneHoleFinalExternalArithmetic.toExternalArithmetic A)

/-- A1 全体の depth bound は外部算術仮定なしで成立する。 -/
theorem atMostOneHoleDepthBound_internal :
    AtMostOneHoleDepthBound := by
  exact atMostOneHoleDepthBound_of_external
    targetOneHoleExternalArithmetic_internal

end Mersenne
end Collatz3
