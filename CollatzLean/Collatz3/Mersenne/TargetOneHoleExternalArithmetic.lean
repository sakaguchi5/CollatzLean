import CollatzLean.Collatz3.Mersenne.TargetOneHoleBase64Descent


/-!
# Collatz3 Mersenne: target-one の外部算術 interface

このファイルでは target-one の最後の四枝 A/B/C/D に必要な外部算術を
明示的な proposition-valued structure として隔離する。

内部で既に証明済みなのは geometric reduction / valuation / gcd dichotomy /
Beatty lock / two-adic cut / base-64 descent までである。

ここで仮定する外部入力は次の六項目だけ。

* A: even, `q=1` を generalized Ramanujan--Nagell uniqueness で排除する。
* C: odd,  `q=1` を同じ uniqueness theorem で排除する。
* B: even, `q>=2`, primitive `gcd(q,t)=1` に Stephan/Baker--Wustholz 型の
  explicit large-depth bound `k < 10^45` を与える。
* D: odd 側も同じ bound を与える。
* B/D の bounded residual を Hensel lift + cyclotomic/discrete-log/CRT
  finite certificate で排除する。

外部定理そのものをこの repository で再形式化することは要求しない。
その代わり、どの箇所から外部入力を使うかを theorem type に露出させる。
-/

namespace Collatz3
namespace Mersenne

/-- Stephan/Baker--Wustholz 側から得る安全側の absolute depth bound。 -/
def targetOneExternalDepthBound : ℕ := 10 ^ 45

/--
target-one の最後の四枝を閉じるための外部算術 package。

`k >= 4` としているのは、元の `k >= 6` exceptional gcd-two branch を
base-64 descent すると depth が `k-2` へ下がるためである。
-/
structure TargetOneHoleExternalArithmetic : Prop where
  /-- A: even / q=1。Bugeaud--Shorey 型 uniqueness を想定する interface。 -/
  even_q_one_impossible :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 1 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 0 →
      h.q < h.t →
      h.q = 1 →
      False

  /-- C: odd / q=1。Bugeaud--Shorey 型 uniqueness を想定する interface。 -/
  odd_q_one_impossible :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 2 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 1 →
      h.q < h.t →
      h.q = 1 →
      False

  /-- B: even / q>=2 primitive branch に対する Stephan 型 explicit bound。 -/
  even_q_ge_two_bound :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 1 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 0 →
      h.q < h.t →
      2 ≤ h.q →
      Nat.gcd h.q h.t = 1 →
      k < targetOneExternalDepthBound

  /-- D: odd / q>=2 primitive branch に対する Stephan 型 explicit bound。 -/
  odd_q_ge_two_bound :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 2 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 1 →
      h.q < h.t →
      2 ≤ h.q →
      Nat.gcd h.q h.t = 1 →
      k < targetOneExternalDepthBound

  /--
  B の bounded residual に対する finite certificate。

  数学的内容は two-adic Hensel residue、`x+1` order sieve、
  `G_q(2^n)` の cyclotomic factor、discrete-log/CRT certificate をまとめたもの。
  -/
  even_q_ge_two_finite_sieve :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 1 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 0 →
      h.q < h.t →
      2 ≤ h.q →
      Nat.gcd h.q h.t = 1 →
      k < targetOneExternalDepthBound →
      False

  /-- D の bounded residual に対する Hensel--cyclotomic finite certificate。 -/
  odd_q_ge_two_finite_sieve :
    ∀ {k n L b : ℕ}
      (h : TargetOneHoleGeometricData k n 2 L b),
      4 ≤ k →
      3 ≤ n →
      k % 2 = 1 →
      h.q < h.t →
      2 ≤ h.q →
      Nat.gcd h.q h.t = 1 →
      k < targetOneExternalDepthBound →
      False

/-- B は Stephan bound と finite certificate の合成で閉じる。 -/
theorem TargetOneHoleExternalArithmetic.even_q_ge_two_impossible
    (A : TargetOneHoleExternalArithmetic)
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
    A.even_q_ge_two_bound h hk hn hkEven hqt hqTwo hGcd
  exact
    A.even_q_ge_two_finite_sieve
      h hk hn hkEven hqt hqTwo hGcd hBound

/-- D も Stephan bound と finite certificate の合成で閉じる。 -/
theorem TargetOneHoleExternalArithmetic.odd_q_ge_two_impossible
    (A : TargetOneHoleExternalArithmetic)
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
    A.odd_q_ge_two_bound h hk hn hkOdd hqt hqTwo hGcd
  exact
    A.odd_q_ge_two_finite_sieve
      h hk hn hkOdd hqt hqTwo hGcd hBound

end Mersenne
end Collatz3
