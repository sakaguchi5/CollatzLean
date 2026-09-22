import CollatzLean.Collatz3.Mersenne.AtMostOneHoleExternalClosure

/-!
# Collatz3 Mersenne: A1 の最終外部算術 interface

従来の `TargetOneHoleExternalArithmetic` では、target-one の四枝

* A: even, `q = 1`
* B: even, `q ≥ 2`
* C: odd,  `q = 1`
* D: odd,  `q ≥ 2`

のうち A/C を generalized Ramanujan--Nagell 型 uniqueness で直接排除する
interface にしていた。

しかし現在の geometric equation では、`q = 1` の右辺に現れる
`G_t(2^n)` は一般には prime power ではない。そのため A/C を
Bugeaud--Shorey 型 uniqueness へ直接送る説明は採用しない。

最終 A1 では四枝すべてを同じ二段構成に統一する。

1. `baseBlock_normalForm` が与える定数 block run に Stephan の periodic-run
   estimate (Baker--Wüstholz 型 explicit lower bound) を適用し、depth `k` を
   明示的な有限上界未満へ落とす。
2. その有限範囲を bounded finite certificate で排除する。

安全側の absolute bound は現在の算術設計に合わせて

* A/C (`q = 1`): `k < 10^23`
* B/D (`q ≥ 2`): `k < 10^45`

とする。

`q = 1` では一つの長い periodic run を直接使う。
`q ≥ 2` では lower / upper の二つの periodic run に estimate を順に適用する。

このファイルは Stephan/Baker--Wüstholz の解析的数論そのものを再形式化しない。
外部 theorem の役割を「explicit bound」と「bounded finite sieve」に分けて
Lean の型に露出させ、その二つから従来の A1 package を derived theorem として
再構成する。
-/

namespace Collatz3
namespace Mersenne

/--
A/C (`q = 1`) に対する安全側の explicit depth bound。

period `n` の長い一つの定数 block run と valuation lock
`n = O(log k)` を組み合わせると `k = O((log k)^3)` へ落ちる。
現在の安全側の finite cut は `10^23`。
-/
def targetOneQOneExternalDepthBound : ℕ := 10 ^ 23

/--
B/D (`q ≥ 2`) の bound は従来の `targetOneExternalDepthBound = 10^45` を使う。

二つの定数 block run に periodic-run estimate を二回適用することで
`k = O((log k)^5)` 型の explicit bound を得る設計である。
-/
abbrev targetOneQGeTwoExternalDepthBound : ℕ :=
  targetOneExternalDepthBound

/--
A1 の最終外部算術 package。

四枝すべてが

`periodic-run explicit bound + bounded finite sieve`

という同じ形を持つ。A/C に direct uniqueness 仮定は置かない。
-/
structure TargetOneHoleFinalExternalArithmetic : Prop where
  /-- A: even / `q=1`。一つの periodic run から `k < 10^23`。 -/
  even_q_one_periodic_run_bound :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 1 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 0 →
      h.q < h.t →
      h.q = 1 →
      k < targetOneQOneExternalDepthBound

  /-- A の `k < 10^23` bounded residual を排除する finite certificate。 -/
  even_q_one_finite_sieve :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 1 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 0 →
      h.q < h.t →
      h.q = 1 →
      k < targetOneQOneExternalDepthBound →
      False

  /-- B: even / `q≥2`。二つの periodic run から `k < 10^45`。 -/
  even_q_ge_two_periodic_run_bound :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 1 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 0 →
      h.q < h.t →
      2 ≤ h.q →
      Nat.gcd h.q h.t = 1 →
      k < targetOneQGeTwoExternalDepthBound

  /-- B の bounded residual を排除する finite certificate。 -/
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

  /-- C: odd / `q=1`。一つの periodic run から `k < 10^23`。 -/
  odd_q_one_periodic_run_bound :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 2 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 1 →
      h.q < h.t →
      h.q = 1 →
      k < targetOneQOneExternalDepthBound

  /-- C の `k < 10^23` bounded residual を排除する finite certificate。 -/
  odd_q_one_finite_sieve :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 2 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 1 →
      h.q < h.t →
      h.q = 1 →
      k < targetOneQOneExternalDepthBound →
      False

  /-- D: odd / `q≥2`。二つの periodic run から `k < 10^45`。 -/
  odd_q_ge_two_periodic_run_bound :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 2 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 1 →
      h.q < h.t →
      2 ≤ h.q →
      Nat.gcd h.q h.t = 1 →
      k < targetOneQGeTwoExternalDepthBound

  /-- D の bounded residual を排除する finite certificate。 -/
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

/-! ## 四枝を bound + finite sieve で閉じる -/

/-- A は periodic-run bound と bounded finite sieve の合成で閉じる。 -/
theorem TargetOneHoleFinalExternalArithmetic.even_q_one_impossible
    (A : TargetOneHoleFinalExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hqOne : h.q = 1) :
    False := by
  have hBound :=
    A.even_q_one_periodic_run_bound h hk hn hkEven hqt hqOne
  exact
    A.even_q_one_finite_sieve
      h hk hn hkEven hqt hqOne hBound

/-- B も二本の periodic-run bound と bounded finite sieve の合成で閉じる。 -/
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
    A.even_q_ge_two_periodic_run_bound
      h hk hn hkEven hqt hqTwo hGcd
  exact
    A.even_q_ge_two_finite_sieve
      h hk hn hkEven hqt hqTwo hGcd hBound

/-- C は periodic-run bound と bounded finite sieve の合成で閉じる。 -/
theorem TargetOneHoleFinalExternalArithmetic.odd_q_one_impossible
    (A : TargetOneHoleFinalExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hqOne : h.q = 1) :
    False := by
  have hBound :=
    A.odd_q_one_periodic_run_bound h hk hn hkOdd hqt hqOne
  exact
    A.odd_q_one_finite_sieve
      h hk hn hkOdd hqt hqOne hBound

/-- D も二本の periodic-run bound と bounded finite sieve の合成で閉じる。 -/
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
    A.odd_q_ge_two_periodic_run_bound
      h hk hn hkOdd hqt hqTwo hGcd
  exact
    A.odd_q_ge_two_finite_sieve
      h hk hn hkOdd hqt hqTwo hGcd hBound

/-! ## 旧 A1 interface への互換 bridge -/

/--
最終 A1 package から従来の `TargetOneHoleExternalArithmetic` を構成する。

旧 package の A/C direct-impossible field は、ここでは uniqueness 仮定ではなく
`periodic-run bound + bounded finite sieve` から導かれる theorem である。
B/D の旧 bound/sieve field も final package の同じ二段構成からそのまま回収する。
-/
theorem TargetOneHoleFinalExternalArithmetic.toExternalArithmetic
    (A : TargetOneHoleFinalExternalArithmetic) :
    TargetOneHoleExternalArithmetic where
  even_q_one_impossible := by
    intro k n L b h hk hn hkEven hqt hqOne
    exact A.even_q_one_impossible h hk hn hkEven hqt hqOne
  odd_q_one_impossible := by
    intro k n L b h hk hn hkOdd hqt hqOne
    exact A.odd_q_one_impossible h hk hn hkOdd hqt hqOne
  even_q_ge_two_bound := by
    intro k n L b h hk hn hkEven hqt hqTwo hGcd
    exact
      A.even_q_ge_two_periodic_run_bound
        h hk hn hkEven hqt hqTwo hGcd
  odd_q_ge_two_bound := by
    intro k n L b h hk hn hkOdd hqt hqTwo hGcd
    exact
      A.odd_q_ge_two_periodic_run_bound
        h hk hn hkOdd hqt hqTwo hGcd
  even_q_ge_two_finite_sieve := by
    intro k n L b h hk hn hkEven hqt hqTwo hGcd hBound
    exact
      A.even_q_ge_two_finite_sieve
        h hk hn hkEven hqt hqTwo hGcd hBound
  odd_q_ge_two_finite_sieve := by
    intro k n L b h hk hn hkOdd hqt hqTwo hGcd hBound
    exact
      A.odd_q_ge_two_finite_sieve
        h hk hn hkOdd hqt hqTwo hGcd hBound

/-! ## final A1 package から既存 closure を一本で回収 -/

/--
最終 A1 package の下では、well-formed target-one equation の depth は `k ≤ 5`。

四枝 A/B/C/D は final package 内で同一の bound+sieve 方式で閉じ、
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

source-one / no-hole は既存内部証明をそのまま使い、target-one だけを
上の final A1 bridge で閉じる。
-/
theorem atMostOneHoleDepthBound_of_final_external
    (A : TargetOneHoleFinalExternalArithmetic) :
    AtMostOneHoleDepthBound := by
  exact atMostOneHoleDepthBound_of_external A.toExternalArithmetic

end Mersenne
end Collatz3
