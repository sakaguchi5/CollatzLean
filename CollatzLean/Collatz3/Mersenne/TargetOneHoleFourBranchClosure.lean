import CollatzLean.Collatz3.Mersenne.TargetOneHoleExternalArithmetic

import Mathlib.Tactic.NormNum

/-!
# Collatz3 Mersenne: target-one 四枝 A/B/C/D の closure

外部算術 interface を仮定すれば、primitive `gcd(q,t)=1` residual は

* A: even, `q=1`
* B: even, `q>=2`
* C: odd,  `q=1`
* D: odd,  `q>=2`

の四枝で完全に閉じる。

唯一の non-primitive branch `n=3, gcd(q,t)=2` は既存 base-64 descent で
`k -> k-2`, `n -> 6`, `gcd=1` へ戻し、同じ四枝 closure を再利用する。
-/

namespace Collatz3
namespace Mersenne

/-- A: even / q=1。 -/
theorem TargetOneHoleGeometricData.branchA_even_q_one_impossible
    (A : TargetOneHoleExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hq : h.q = 1) :
    False :=
  A.even_q_one_impossible h hk hn hkEven hqt hq

/-- B: even / q>=2。Stephan bound と finite Hensel--cyclotomic sieve の合成。 -/
theorem TargetOneHoleGeometricData.branchB_even_q_ge_two_impossible
    (A : TargetOneHoleExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hGcd : Nat.gcd h.q h.t = 1) :
    False :=
  A.even_q_ge_two_impossible h hk hn hkEven hqt hqTwo hGcd

/-- C: odd / q=1。 -/
theorem TargetOneHoleGeometricData.branchC_odd_q_one_impossible
    (A : TargetOneHoleExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hq : h.q = 1) :
    False :=
  A.odd_q_one_impossible h hk hn hkOdd hqt hq

/-- D: odd / q>=2。Stephan bound と finite Hensel--cyclotomic sieve の合成。 -/
theorem TargetOneHoleGeometricData.branchD_odd_q_ge_two_impossible
    (A : TargetOneHoleExternalArithmetic)
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hGcd : Nat.gcd h.q h.t = 1) :
    False :=
  A.odd_q_ge_two_impossible h hk hn hkOdd hqt hqTwo hGcd

/--
primitive `gcd(q,t)=1` residual は A/B/C/D の四枝で完全に閉じる。
-/
theorem TargetOneHoleGeometricData.primitive_four_branch_impossible
    (A : TargetOneHoleExternalArithmetic)
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hqt : h.q < h.t)
    (hGcd : Nat.gcd h.q h.t = 1)
    (hExit :
      (k % 2 = 0 ∧ r = 1) ∨
      (k % 2 = 1 ∧ r = 2)) :
    False := by
  have hqCases : h.q = 1 ∨ 2 ≤ h.q := by
    have hqPos : 0 < h.q := h.q_pos
    omega
  rcases hExit with hEven | hOdd
  · rcases hEven with ⟨hkEven, hr⟩
    subst r
    rcases hqCases with hqOne | hqTwo
    · exact h.branchA_even_q_one_impossible A hk hn hkEven hqt hqOne
    · exact h.branchB_even_q_ge_two_impossible A hk hn hkEven hqt hqTwo hGcd
  · rcases hOdd with ⟨hkOdd, hr⟩
    subst r
    rcases hqCases with hqOne | hqTwo
    · exact h.branchC_odd_q_one_impossible A hk hn hkOdd hqt hqOne
    · exact h.branchD_odd_q_ge_two_impossible A hk hn hkOdd hqt hqTwo hGcd

/-- `k -> k-2` は `k>=6` では parity を保存する。 -/
private theorem mod_two_sub_two_eq
    {k : ℕ}
    (hk : 6 ≤ k) :
    (k - 2) % 2 = k % 2 := by
  omega

/--
外部算術 package を仮定すると、well-formed target-one は `k>=6` を持てない。

primitive branch は直接 A/B/C/D で閉じ、exceptional `n=3,gcd=2` は
base-64 primitive data へ descent して同じ theorem をもう一度適用する。
-/
theorem TargetOneHoleEquation.largeDepth_impossible_of_external
    (A : TargetOneHoleExternalArithmetic)
    {k n r L b : ℕ}
    (hk6 : 6 ≤ k)
    (hn : 0 < n)
    (hr : 0 < r)
    (hb : 0 < b)
    (hbL : b < L)
    (hEq : TargetOneHoleEquation k n r L b) :
    False := by
  rcases hEq.largeDepth_shape hk6 hn hr hb hbL with
    ⟨hn3, hExit⟩
  rcases hEq.exists_geometricData_q_lt_of_largeDepth
      hk6 hn hr hb hbL with
    ⟨hData, hqt⟩
  rcases hData.gcd_dichotomy hn3 with hPrimitive | hExceptional
  · exact hData.primitive_four_branch_impossible
      A (by omega) hn3 hqt hPrimitive hExit
  · rcases hExceptional with ⟨hnEq, hGcdTwo⟩
    subst n
    have hr12 : r = 1 ∨ r = 2 := by
      rcases hExit with ⟨_, hr1⟩ | ⟨_, hr2⟩
      · exact Or.inl hr1
      · exact Or.inr hr2
    rcases hData.gcd_two_base64_geometricData
        hk6 hr12 hqt hGcdTwo with
      ⟨q', t', hqEq, htEq, hGcd', hData', hq', ht', hqt'⟩
    have hGcdData' : Nat.gcd hData'.q hData'.t = 1 := by
      rw [hq', ht']
      exact hGcd'
    have hParity : (k - 2) % 2 = k % 2 :=
      mod_two_sub_two_eq hk6
    have hExit' :
        ((k - 2) % 2 = 0 ∧ r = 1) ∨
        ((k - 2) % 2 = 1 ∧ r = 2) := by
      rcases hExit with ⟨hkEven, hr1⟩ | ⟨hkOdd, hr2⟩
      · exact Or.inl ⟨by omega, hr1⟩
      · exact Or.inr ⟨by omega, hr2⟩
    exact hData'.primitive_four_branch_impossible
      A (by omega) (by norm_num) hqt' hGcdData' hExit'

/--
外部算術 package の下で、well-formed target-one の depth は `k<=5`。
-/
theorem TargetOneHoleEquation.depth_le_five_of_external
    (A : TargetOneHoleExternalArithmetic)
    {k n r L b : ℕ}
    (hn : 0 < n)
    (hr : 0 < r)
    (hb : 0 < b)
    (hbL : b < L)
    (hEq : TargetOneHoleEquation k n r L b) :
    k ≤ 5 := by
  by_contra hNot
  have hk6 : 6 ≤ k := by omega
  exact hEq.largeDepth_impossible_of_external A hk6 hn hr hb hbL

end Mersenne
end Collatz3
