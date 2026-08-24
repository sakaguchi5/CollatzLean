import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# `3^p - 2^H` の elementary arithmetic

zero Hensel cycle の denominator

  D = 3^p - 2^H

に必要な 2/3-coprimality と `D=1` の elementary classification をまとめる。
Catalan/Mihăilescu は使わない。base 3 固定なので偶奇と平方差だけで十分。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- zero cycle denominator。 -/
def twoThreeCycleDenominator (p H : ℕ) : ℤ :=
  (3 : ℤ) ^ p - (2 : ℤ) ^ H

/-- `p>0`, `H>0` なら denominator は 2 と coprime。 -/
theorem twoThreeCycleDenominator_isCoprime_two
    {p H : ℕ}
    (hH : 0 < H) :
    IsCoprime (twoThreeCycleDenominator p H) (2 : ℤ) := by
  have h32 : IsCoprime (3 : ℤ) (2 : ℤ) := by
    refine ⟨-1, 2, ?_⟩
    norm_num
  have hPow : IsCoprime ((3 : ℤ) ^ p) (2 : ℤ) :=
    h32.pow_left
  rcases hPow with ⟨a, b, hab⟩
  obtain ⟨h, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hH)
  refine ⟨a, a * (2 : ℤ) ^ h + b, ?_⟩
  unfold twoThreeCycleDenominator
  rw [pow_succ]
  linear_combination hab

/-- `p>0`, `H>0` なら denominator は 3 と coprime。 -/
theorem twoThreeCycleDenominator_isCoprime_three
    {p H : ℕ}
    (hp : 0 < p) :
    IsCoprime (twoThreeCycleDenominator p H) (3 : ℤ) := by
  have h23 : IsCoprime (2 : ℤ) (3 : ℤ) := by
    refine ⟨-1, 1, ?_⟩
    norm_num
  have hPow : IsCoprime ((2 : ℤ) ^ H) (3 : ℤ) :=
    h23.pow_left
  rcases hPow with ⟨a, b, hab⟩
  obtain ⟨p0, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  refine ⟨-a, a * (3 : ℤ) ^ p0 + b, ?_⟩
  unfold twoThreeCycleDenominator
  rw [pow_succ]
  linear_combination hab

/-- positive integer unit は `1`。 -/
theorem int_eq_one_of_isUnit_of_pos
    {z : ℤ}
    (hzUnit : IsUnit z)
    (hzPos : 0 < z) :
    z = 1 := by
  rcases (Int.isUnit_iff.mp hzUnit) with hz | hz
  · exact hz
  · rw [hz] at hzPos
    norm_num at hzPos

/--
`p ≥ 3`, `H ≥ 3` かつ

  3^p = 2^H + 1

なら `p` は偶数。

`p` が奇数なら `3^p ≡ 3 (mod 8)` だが、
`H ≥ 3` では `2^H + 1 ≡ 1 (mod 8)` なので矛盾する。
-/
private theorem even_of_threePow_eq_twoPow_add_one
    {p H : ℕ}
    (hHThree : 3 ≤ H)
    (hEq : 3 ^ p = 2 ^ H + 1) :
    Even p := by
  by_contra hNotEven
  have hOdd : Odd p :=
    Nat.not_even_iff_odd.mp hNotEven
  rcases hOdd with ⟨q, hq⟩
  have hL :
      3 ^ p % 8 = 3 := by
    rw [hq, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  have h8dvd :
      8 ∣ 2 ^ H := by
    change 2 ^ 3 ∣ 2 ^ H
    exact pow_dvd_pow 2 hHThree
  have hR :
      (2 ^ H + 1) % 8 = 1 := by
    rw [Nat.add_mod]
    simp [Nat.mod_eq_zero_of_dvd h8dvd]
  rw [hEq, hR] at hL
  norm_num at hL


/--
偶数指数を `p = 2k` と書いたとき、

  3^(2k) = 2^H + 1

から平方差

  (3^k - 1)(3^k + 1) = 2^H

を得る。

Nat の切り捨て減算を直接 `nlinarith` で展開せず、
既存の平方差恒等式 `Nat.sq_sub_sq` を使う。
-/
private theorem threePow_factor_eq_twoPow
    {k H : ℕ}
    (hEq :
      3 ^ (k + k) = 2 ^ H + 1) :
    (3 ^ k - 1) * (3 ^ k + 1) = 2 ^ H := by
  have hSq :
      (3 ^ k) ^ 2 = 2 ^ H + 1 := by
    simpa [pow_add, pow_two] using hEq
  calc
    (3 ^ k - 1) * (3 ^ k + 1)
        =
      (3 ^ k + 1) * (3 ^ k - 1) := by
        exact Nat.mul_comm _ _
    _ =
      (3 ^ k) ^ 2 - 1 ^ 2 := by
        exact (Nat.sq_sub_sq (3 ^ k) 1).symm
    _ = 2 ^ H := by
      simp [hSq]


/--
`2^H` の任意の自然数 divisor は、それ自身 `2` の冪である。

これは prime power の divisor classification を base `2` に特殊化したもの。
-/
private theorem exists_twoPow_eq_of_dvd_twoPow
    {n H : ℕ}
    (hDiv : n ∣ 2 ^ H) :
    ∃ a : ℕ, n = 2 ^ a := by
  rcases
      (Nat.dvd_prime_pow
        (by decide)).mp hDiv with
    ⟨a, haH, ha⟩
  exact ⟨a, ha⟩


/--
二つの2冪の差がちょうど `2` で、

  2^b = 2^a + 2,
  a > 0

なら、小さい方は `2` そのもの。

`a ≥ 2` なら `2^a` と `2^b` はともに `4` の倍数になるが、
その差が `2` であることに反する。
-/
private theorem twoPow_eq_two_of_add_two_eq_twoPow
    {a b : ℕ}
    (haPos : 0 < a)
    (hDiff :
      2 ^ b = 2 ^ a + 2) :
    2 ^ a = 2 := by
  have hPowAPos :
      0 < 2 ^ a := by
    positivity
  have hbTwo : 2 ≤ b := by
    by_contra hbNot
    have hbLt : b < 2 := by
      omega
    by_cases hb0 : b = 0
    · subst b
      norm_num at hDiff
    · have hb1 : b = 1 := by
        omega
      subst b
      norm_num at hDiff
  by_cases haOne : a = 1
  · subst a
    norm_num
  · have haTwo : 2 ≤ a := by
      omega
    have h4A :
        4 ∣ 2 ^ a := by
      change 2 ^ 2 ∣ 2 ^ a
      exact pow_dvd_pow 2 haTwo
    have h4B :
        4 ∣ 2 ^ b := by
      change 2 ^ 2 ∣ 2 ^ b
      exact pow_dvd_pow 2 hbTwo
    have hAmod :
        2 ^ a % 4 = 0 :=
      Nat.mod_eq_zero_of_dvd h4A
    have hBmod :
        2 ^ b % 4 = 0 :=
      Nat.mod_eq_zero_of_dvd h4B
    have hMod :=
      congrArg (fun n : ℕ => n % 4) hDiff
    rw [hBmod, Nat.add_mod, hAmod] at hMod
    norm_num at hMod


/--
`k > 0` かつ

  (3^k - 1)(3^k + 1) = 2^H

なら、小さい因子は必ず `2`。

両因子は `2^H` の divisor なので2冪であり、
しかも二つの因子の差はちょうど `2`。
したがって上の「差が2の二つの2冪」の補題が適用できる。
-/
private theorem threePow_sub_one_eq_two_of_factor_eq_twoPow
    {k H : ℕ}
    (hkPos : 0 < k)
    (hFactor :
      (3 ^ k - 1) * (3 ^ k + 1) = 2 ^ H) :
    3 ^ k - 1 = 2 := by
  have hDivA :
      3 ^ k - 1 ∣ 2 ^ H := by
    rw [← hFactor]
    exact dvd_mul_right _ _
  have hDivB :
      3 ^ k + 1 ∣ 2 ^ H := by
    rw [← hFactor]
    exact dvd_mul_left _ _
  rcases exists_twoPow_eq_of_dvd_twoPow hDivA with
    ⟨a, hA⟩
  rcases exists_twoPow_eq_of_dvd_twoPow hDivB with
    ⟨b, hB⟩
  have haPos : 0 < a := by
    by_contra haNot
    have haZero : a = 0 := by
      omega
    rw [haZero] at hA
    norm_num at hA
    obtain ⟨t, hkSucc⟩ :=
      Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt hkPos)
    rw [hkSucc, pow_succ] at hA
    have htPowPos :
        0 < 3 ^ t := by
      positivity
    omega
  have hDiff :
      2 ^ b = 2 ^ a + 2 := by
    have hPowAPos :
        0 < 2 ^ a := by
      positivity
    omega
  have hAVal :
      2 ^ a = 2 :=
    twoPow_eq_two_of_add_two_eq_twoPow
      haPos hDiff
  calc
    3 ^ k - 1 = 2 ^ a := hA
    _ = 2 := hAVal


/--
正の偶数 `p` が

  3^p = 2^H + 1

を満たすなら `p = 2`。

`p = 2k` と書き、平方差で得た二因子のうち
`3^k - 1 = 2` を示すと `3^k = 3`。
base `3 ≥ 2` の冪の injectivity から `k = 1` が従う。
-/
private theorem period_eq_two_of_even_threePow_equation
    {p H : ℕ}
    (hp : 0 < p)
    (hEven : Even p)
    (hEq :
      3 ^ p = 2 ^ H + 1) :
    p = 2 := by
  rcases hEven with ⟨k, hk⟩
  have hkPos : 0 < k := by
    rw [hk] at hp
    omega
  have hEqK :
      3 ^ (k + k) = 2 ^ H + 1 := by
    simpa [hk] using hEq
  have hFactor :
      (3 ^ k - 1) * (3 ^ k + 1) = 2 ^ H :=
    threePow_factor_eq_twoPow hEqK
  have hA :
      3 ^ k - 1 = 2 :=
    threePow_sub_one_eq_two_of_factor_eq_twoPow
      hkPos hFactor
  have h3k :
      3 ^ k = 3 := by
    omega
  have hkOne : k = 1 := by
    apply
      Nat.pow_right_injective
        (by norm_num : 2 ≤ (3 : ℕ))
    simpa using h3k
  rw [hk, hkOne]

/--
`3^p - 2^H = 1`, `0 < p`, `p ≤ H` なら、
可能な period は `p = 1` または `p = 2` だけ。

`p < 3` は直ちに `1` または `2`。

`p ≥ 3` なら `H ≥ 3` でもあるため、mod `8` により `p` は偶数。
偶数の場合は

  (3^k - 1)(3^k + 1) = 2^H

へ因数分解し、差が `2` の二つの2冪を分類することで `k = 1`,
したがって `p = 2` を得る。

Catalan/Mihăilescu は使わず、mod `8` と初等的な平方差だけで閉じる。
-/
theorem period_eq_one_or_two_of_denominator_eq_one
    {p H : ℕ}
    (hp : 0 < p)
    (hpH : p ≤ H)
    (hD : twoThreeCycleDenominator p H = 1) :
    p = 1 ∨ p = 2 := by
  have hEqInt :
      (3 : ℤ) ^ p =
        (2 : ℤ) ^ H + 1 := by
    unfold twoThreeCycleDenominator at hD
    linarith
  have hEqNat :
      3 ^ p = 2 ^ H + 1 := by
    exact_mod_cast hEqInt
  by_cases hpSmall : p < 3
  · omega
  · have hpThree : 3 ≤ p := by
      omega
    have hHThree : 3 ≤ H :=
      le_trans hpThree hpH
    have hEven : Even p :=
      even_of_threePow_eq_twoPow_add_one
        hHThree hEqNat
    right
    exact
      period_eq_two_of_even_threePow_equation
        hp hEven hEqNat

/--
`3^p - 2^(p+e) = 1` の primitive zero-cycle 用の完全分類。

period だけでなく offset まで含めて

* `(p,e) = (1,0)`, または
* `(p,e) = (2,1)`

の二通りに限られる。
-/
theorem period_offset_cases_of_denominator_eq_one
    {p e : ℕ}
    (hp : 0 < p)
    (hD : twoThreeCycleDenominator p (p + e) = 1) :
    (p = 1 ∧ e = 0) ∨ (p = 2 ∧ e = 1) := by
  have hpH : p ≤ p + e := by omega
  rcases period_eq_one_or_two_of_denominator_eq_one hp hpH hD with hpOne | hpTwo
  · left
    refine ⟨hpOne, ?_⟩
    subst p
    have hPowInt : (2 : ℤ) ^ (1 + e) = 2 := by
      unfold twoThreeCycleDenominator at hD
      norm_num at hD ⊢
      linarith
    have hPowNat : (2 : ℕ) ^ (1 + e) = 2 := by
      exact_mod_cast hPowInt
    have hExp : 1 + e = 1 := by
      exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) (by simpa using hPowNat)
    omega
  · right
    refine ⟨hpTwo, ?_⟩
    subst p
    have hPowInt : (2 : ℤ) ^ (2 + e) = 8 := by
      unfold twoThreeCycleDenominator at hD
      norm_num at hD ⊢
      linarith
    have hPowNat : (2 : ℕ) ^ (2 + e) = 8 := by
      exact_mod_cast hPowInt
    have hExp : 2 + e = 3 := by
      exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) (by simpa using hPowNat)
    omega

end ExternalArithmetic
end CSTMicro
end Collatz2
