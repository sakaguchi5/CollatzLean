import CollatzLean.Collatz3.Mersenne.TargetOneHoleQOneArithmetic
import CollatzLean.Collatz3.Mersenne.AtMostOneHoleExternalClosure

/-!
# Collatz3 Mersenne: A1 の最終外部算術 interface

A1 の四枝

* A: even, `q = 1`
* B: even, `q ≥ 2`
* C: odd,  `q = 1`
* D: odd,  `q ≥ 2`

のうち A/C は `TargetOneHoleQOneArithmetic` で内部化した。

`q=1` では geometric data から exact three-log identity を作り、
Baker--Wüstholz [BW93] の既知定理を直接特殊化して `k<10^23` を証明する。
その bounded residual は既存 M₄ tail/loop modulus の `native_decide`
certificate で survivor 0 まで閉じる。

従ってこの最終 external package に残るのは B/D (`q≥2`) だけである。
両枝は従来どおり

1. 二つの periodic run から explicit bound `k<10^45` を得る。
2. bounded finite certificate で残りを排除する。

という二段を外部入力として受け取る。

旧 `TargetOneHoleExternalArithmetic` は互換性のため derived theorem として
再構成する。その A/C field は external package からではなく、内部 theorem
`even_q_one_impossible_internal` / `odd_q_one_impossible_internal` で埋める。
-/

namespace Collatz3
namespace Mersenne

/--
旧コード向けの互換名。A/C の bound 自体は現在 repo 内で証明される。
-/
abbrev targetOneQOneExternalDepthBound : ℕ :=
  targetOneQOneInternalDepthBound

/--
B/D (`q ≥ 2`) の安全側 bound は従来の `targetOneExternalDepthBound = 10^45`。
-/
abbrev targetOneQGeTwoExternalDepthBound : ℕ :=
  targetOneExternalDepthBound

/--
A1 の最終外部算術 package。

A/C (`q=1`) は無条件 theorem になったため field を持たない。
残る B/D (`q≥2`) だけが

`periodic-run explicit bound + bounded finite sieve`

を要求する。
-/
structure TargetOneHoleFinalExternalArithmetic : Prop where
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

/-! ## 四枝 closure: A/C は内部、B/D だけ external -/

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

/-- B は periodic-run bound と bounded finite sieve の合成で閉じる。 -/
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

/-- D は periodic-run bound と bounded finite sieve の合成で閉じる。 -/
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

旧 A/C direct-impossible field は internal theorem で埋まる。
B/D の bound/sieve field だけを final external package から受け取る。
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

A/C は内部 theorem、B/D は final package で閉じる。
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

source-one / no-hole は既存内部証明、target-one の A/C は今回の内部 theorem、
B/D だけを final package から使う。
-/
theorem atMostOneHoleDepthBound_of_final_external
    (A : TargetOneHoleFinalExternalArithmetic) :
    AtMostOneHoleDepthBound := by
  exact atMostOneHoleDepthBound_of_external A.toExternalArithmetic

end Mersenne
end Collatz3
