import CollatzLean.Collatz3.Mersenne.SmallHoleExitDepth
import CollatzLean.Collatz3.Arithmetic.ThreeOrderModTwoPow
import CollatzLean.Collatz3.Arithmetic.TwoOrderModThreePow
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: source-two-hole regular branch の排除

source-two-hole

`3^k (2^n - 1 - 2^a - 2^b) = 2^r (2^L - 1) + 1`

について、低位 resonance を除く regular branch を elementary arithmetic だけで閉じる。

主な内容は次の通り。

* `k>0` では `r=2` は mod 3 で不可能。
* `r=1`, `k>=7` は、low-bit order と mod `3^k` の order を衝突させて不可能。
* 従って `k>=7` の source-two-hole が存在するなら、既存の
  `SourceTwoHoleLowResonance` の二枝に必ず入る。

外部 S-unit 定理や Baker 型評価は使わない。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

/-- source-two-hole でも positive depth と `r=2` は両立しない。 -/
theorem SourceTwoHoleEquation.exitDepth_two_impossible
    {k n L a b : ℕ}
    (hk : 0 < k)
    (hEq : SourceTwoHoleEquation k n 2 L a b) :
    False := by
  have hMod := hEq.to_mod 3
  unfold SourceTwoHoleModEquation at hMod
  have hThree : (3 : ZMod 3) ^ k = 0 := by
    obtain ⟨j, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ]
    have h3 : (3 : ZMod 3) = 0 := by
      decide
    simp [h3]
  have hTwoSq : (2 : ZMod 3) ^ 2 = 1 := by
    decide
  have hZero :
      (0 : ZMod 3) = (2 : ZMod 3) ^ L := by
    rw [hThree] at hMod
    simpa [hTwoSq] using hMod
  have hTwoUnit : IsUnit (2 : ZMod 3) := by
    exact (ZMod.isUnit_iff_coprime 2 3).2 (by decide)
  have hPowNe :
      (2 : ZMod 3) ^ L ≠ 0 :=
    (hTwoUnit.pow L).ne_zero
  exact hPowNe hZero.symm

/-- `a<b<n` なら二つの hole の和は `2^n-1` 以下。 -/
private theorem sourceTwo_hole_sum_le
    {n a b : ℕ}
    (hab : a < b)
    (hbn : b < n) :
    2 ^ a + 2 ^ b ≤ 2 ^ n - 1 := by
  have hPowAB : 2 ^ a < 2 ^ b :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).2 hab
  have hbPred : b ≤ n - 1 := by omega
  have hPowB : 2 ^ b ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hbPred
  have hnPos : 0 < n := by omega
  have hPowN : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring_nf
    simp
  rw [hPowN]
  omega

/-- source-two-hole, `r=1` の整数等式を自然数の `+1` 形へ戻す。 -/
private theorem sourceTwo_exitOne_nat_identity
    {k n L a b : ℕ}
    (hab : a < b)
    (hbn : b < n)
    (hEq : SourceTwoHoleEquation k n 1 L a b) :
    3 ^ k * (2 ^ n - 1 - 2 ^ a - 2 ^ b) + 1 = 2 ^ (L + 1) := by
  have hHoleLe := sourceTwo_hole_sum_le hab hbn
  have hOneLe : 1 ≤ 2 ^ n :=
    Nat.one_le_pow n 2 (by norm_num)
  have hALe : 2 ^ a ≤ 2 ^ n - 1 := by
    exact le_trans (Nat.le_add_right _ _) hHoleLe
  have hBLe : 2 ^ b ≤ 2 ^ n - 1 - 2 ^ a := by
    omega
  let s : ℕ := 2 ^ n - 1 - 2 ^ a - 2 ^ b
  have hsCast :
      (s : ℤ) =
        (2 : ℤ) ^ n - 1 - (2 : ℤ) ^ a - (2 : ℤ) ^ b := by
    dsimp [s]
    rw [Nat.cast_sub hBLe, Nat.cast_sub hALe, Nat.cast_sub hOneLe]
    norm_num
  have hInt :
      (3 : ℤ) ^ k * (s : ℤ) + 1 = (2 : ℤ) ^ (L + 1) := by
    unfold SourceTwoHoleEquation at hEq
    simp only [pow_one] at hEq
    rw [hsCast]
    rw [pow_succ]
    linear_combination hEq
  have hNat :
      3 ^ k * s + 1 = 2 ^ (L + 1) := by
    exact_mod_cast hInt
  simpa [s] using hNat

/-- 二つの hole を最大側へ寄せても source factor は `2^(n-2)-1` 以上残る。 -/
private theorem sourceTwo_factor_lower
    {n a b : ℕ}
    (ha0 : 0 < a)
    (hab : a < b)
    (hbn : b < n) :
    2 ^ (n - 2) - 1 ≤ 2 ^ n - 1 - 2 ^ a - 2 ^ b := by
  have hn3 : 3 ≤ n := by omega
  have haPred : a ≤ n - 2 := by omega
  have hbPred : b ≤ n - 1 := by omega
  have hA : 2 ^ a ≤ 2 ^ (n - 2) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) haPred
  have hB : 2 ^ b ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hbPred
  have hPowPred : 2 ^ (n - 1) = 2 * 2 ^ (n - 2) := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
    ring
  have hPowN : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    ring
  rw [hPowPred] at hB
  rw [hPowN]
  have hSumLe : 2 ^ a + 2 ^ b ≤ 3 * 2 ^ (n - 2) := by
    omega
  omega

/-- `k>=7` の `r=1` branch では source length は target exponent 以下。 -/
private theorem sourceTwo_exitOne_n_le_L
    {k n L a b : ℕ}
    (hk7 : 7 ≤ k)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbn : b < n)
    (hEq : SourceTwoHoleEquation k n 1 L a b) :
    n ≤ L := by
  have hNat := sourceTwo_exitOne_nat_identity hab hbn hEq
  have hFactor := sourceTwo_factor_lower ha0 hab hbn
  have hn3 : 3 ≤ n := by omega
  have hX2 : 2 ≤ 2 ^ (n - 2) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n - 2) :=
        Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
  have hThree : 2187 ≤ 3 ^ k := by
    calc
      2187 = 3 ^ 7 := by norm_num
      _ ≤ 3 ^ k :=
        Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hk7
  have hMul :
      2187 * (2 ^ (n - 2) - 1) ≤
        3 ^ k * (2 ^ n - 1 - 2 ^ a - 2 ^ b) :=
    Nat.mul_le_mul hThree hFactor
  have hPowN : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
    ring
  have hSmall :
      4 * 2 ^ (n - 2) < 2187 * (2 ^ (n - 2) - 1) + 1 := by
    omega
  have hBig :
      2 ^ n < 3 ^ k * (2 ^ n - 1 - 2 ^ a - 2 ^ b) + 1 := by
    calc
      2 ^ n = 4 * 2 ^ (n - 2) := hPowN
      _ < 2187 * (2 ^ (n - 2) - 1) + 1 := hSmall
      _ ≤ 3 ^ k * (2 ^ n - 1 - 2 ^ a - 2 ^ b) + 1 :=
        Nat.add_le_add_right hMul 1
  by_contra hNot
  have hExp : L + 1 ≤ n := by omega
  have hPow : 2 ^ (L + 1) ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hExp
  rw [← hNat] at hPow
  omega

/-- 最初の hole `a>=3` では low-bit congruence が `2^(a-2) | k` を強制する。 -/
private theorem sourceTwo_firstHole_order
    {k n L a b : ℕ}
    (ha3 : 3 ≤ a)
    (hab : a < b)
    (hbn : b < n)
    (hnL : n ≤ L)
    (hEq : SourceTwoHoleEquation k n 1 L a b) :
    2 ^ (a - 2) ∣ k := by
  have hMod := hEq.to_mod (2 ^ a)
  unfold SourceTwoHoleModEquation at hMod
  have hNZero : (2 : ZMod (2 ^ a)) ^ n = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : a ≤ n)
  have hAZero : (2 : ZMod (2 ^ a)) ^ a = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (le_rfl : a ≤ a)
  have hBZero : (2 : ZMod (2 ^ a)) ^ b = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : a ≤ b)
  have hLZero : (2 : ZMod (2 ^ a)) ^ L = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : a ≤ L)
  rw [hNZero, hAZero, hBZero, hLZero] at hMod
  simp only [pow_one] at hMod
  have hPow : (3 : ZMod (2 ^ a)) ^ k = 1 := by
    linear_combination -hMod
  have hCong : 3 ^ k ≡ 1 [MOD 2 ^ a] := by
    simpa [← ZMod.natCast_eq_natCast_iff] using hPow
  exact twoPow_dvd_exponent_of_threePow_modEq_one ha3 hCong

/-- first-hole order から、全 `a>0` について粗い線形上界 `a<=k+2` を得る。 -/
private theorem sourceTwo_firstHole_le_depth_add_two
    {k n L a b : ℕ}
    (hk : 0 < k)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbn : b < n)
    (hnL : n ≤ L)
    (hEq : SourceTwoHoleEquation k n 1 L a b) :
    a ≤ k + 2 := by
  by_cases ha3 : 3 ≤ a
  · have hDvd := sourceTwo_firstHole_order ha3 hab hbn hnL hEq
    have hPowLe : 2 ^ (a - 2) ≤ k :=
      Nat.le_of_dvd hk hDvd
    have hIndexLt : a - 2 < 2 ^ (a - 2) :=
      (a - 2).lt_two_pow_self
    omega
  · omega

/-- `3^k < 2^(2k)`。 -/
private theorem sourceTwo_threePow_lt_twoPow_double
    {k : ℕ}
    (hk : 0 < k) :
    3 ^ k < 2 ^ (2 * k) := by
  have h34 : 3 ^ k < 4 ^ k :=
    Nat.pow_lt_pow_left (by norm_num : 3 < 4) (Nat.ne_of_gt hk)
  calc
    3 ^ k < 4 ^ k := h34
    _ = 2 ^ (2 * k) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]

/-- mod `2^b` から second hole に線形上界を与える correction divisibility。 -/
private theorem sourceTwo_secondHole_dvd_correction
    {k n L a b : ℕ}
    (hbn : b < n)
    (hnL : n ≤ L)
    (hEq : SourceTwoHoleEquation k n 1 L a b) :
    2 ^ b ∣ 3 ^ k * (1 + 2 ^ a) - 1 := by
  have hMod := hEq.to_mod (2 ^ b)
  unfold SourceTwoHoleModEquation at hMod
  have hNZero : (2 : ZMod (2 ^ b)) ^ n = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : b ≤ n)
  have hBZero : (2 : ZMod (2 ^ b)) ^ b = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (le_rfl : b ≤ b)
  have hLZero : (2 : ZMod (2 ^ b)) ^ L = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : b ≤ L)
  rw [hNZero, hBZero, hLZero] at hMod
  simp only [pow_one] at hMod
  have hRel :
      (3 : ZMod (2 ^ b)) ^ k *
          (1 + (2 : ZMod (2 ^ b)) ^ a) = 1 := by
    calc
      (3 : ZMod (2 ^ b)) ^ k *
          (1 + (2 : ZMod (2 ^ b)) ^ a)
          = -((3 : ZMod (2 ^ b)) ^ k *
              (0 - 1 - (2 : ZMod (2 ^ b)) ^ a - 0)) := by ring
      _ = -((2 : ZMod (2 ^ b)) * (0 - 1) + 1) := by rw [hMod]
      _ = 1 := by ring
  have hCong : 3 ^ k * (1 + 2 ^ a) ≡ 1 [MOD 2 ^ b] := by
    simpa [← ZMod.natCast_eq_natCast_iff] using hRel
  have hProdOne : 1 ≤ 3 ^ k * (1 + 2 ^ a) := by
    have hThreePos : 0 < 3 ^ k := Nat.pow_pos (by norm_num)
    have hFactorPos : 0 < 1 + 2 ^ a := by
      simp only [add_pos_iff, Order.lt_one_iff, Order.lt_two_iff, zero_le, pow_pos, or_self]
    exact Nat.mul_pos hThreePos hFactorPos
  exact (Nat.modEq_iff_dvd' hProdOne).mp hCong.symm

/-- second-hole correction から `b < 2k+a+1`。 -/
private theorem sourceTwo_secondHole_lt
    {k a b : ℕ}
    (hk : 0 < k)
    (hDvd : 2 ^ b ∣ 3 ^ k * (1 + 2 ^ a) - 1) :
    b < 2 * k + a + 1 := by
  let B : ℕ := 3 ^ k * (1 + 2 ^ a) - 1
  have hThree : 1 < 3 ^ k :=
    one_lt_pow₀ (by norm_num : (1 : ℕ) < 3) (Nat.ne_of_gt hk)
  have hBPos : 0 < B := by
    dsimp [B]
    have : 1 < 3 ^ k * (1 + 2 ^ a) := by
      calc
        1 < 3 ^ k := hThree
        _ ≤ 3 ^ k * (1 + 2 ^ a) := by
          exact Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hTwoLe : 2 ^ b ≤ B := Nat.le_of_dvd hBPos hDvd
  have hBLt : B < 3 ^ k * (1 + 2 ^ a) := by
    dsimp [B]
    omega
  have hThreeLt := sourceTwo_threePow_lt_twoPow_double hk
  have hSecondLe : 1 + 2 ^ a ≤ 2 ^ (a + 1) := by
    rw [pow_succ]
    have hPos : 0 < 2 ^ a := by positivity
    omega
  have hProdLt :
      3 ^ k * (1 + 2 ^ a) < 2 ^ (2 * k) * 2 ^ (a + 1) := by
    calc
      3 ^ k * (1 + 2 ^ a) <
          2 ^ (2 * k) * (1 + 2 ^ a) :=
        Nat.mul_lt_mul_of_pos_right hThreeLt (by positivity)
      _ ≤ 2 ^ (2 * k) * 2 ^ (a + 1) :=
        Nat.mul_le_mul_left _ hSecondLe
  have hPowLt : 2 ^ b < 2 ^ (2 * k + a + 1) := by
    calc
      2 ^ b ≤ B := hTwoLe
      _ < 3 ^ k * (1 + 2 ^ a) := hBLt
      _ < 2 ^ (2 * k) * 2 ^ (a + 1) := hProdLt
      _ = 2 ^ (2 * k + a + 1) := by
        rw [← pow_add]
        congr 1
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hPowLt

/-- mod `2^n` から source length に線形上界を与える correction divisibility。 -/
private theorem sourceTwo_sourceLength_dvd_correction
    {k n L a b : ℕ}
    (hnL : n ≤ L)
    (hEq : SourceTwoHoleEquation k n 1 L a b) :
    2 ^ n ∣ 3 ^ k * (1 + 2 ^ a + 2 ^ b) - 1 := by
  have hMod := hEq.to_mod (2 ^ n)
  unfold SourceTwoHoleModEquation at hMod
  have hNZero : (2 : ZMod (2 ^ n)) ^ n = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (le_rfl : n ≤ n)
  have hLZero : (2 : ZMod (2 ^ n)) ^ L = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 hnL
  rw [hNZero, hLZero] at hMod
  simp only [pow_one] at hMod
  have hRel :
      (3 : ZMod (2 ^ n)) ^ k *
          (1 + (2 : ZMod (2 ^ n)) ^ a + (2 : ZMod (2 ^ n)) ^ b) = 1 := by
    calc
      (3 : ZMod (2 ^ n)) ^ k *
          (1 + (2 : ZMod (2 ^ n)) ^ a + (2 : ZMod (2 ^ n)) ^ b)
          = -((3 : ZMod (2 ^ n)) ^ k *
              (0 - 1 - (2 : ZMod (2 ^ n)) ^ a -
                (2 : ZMod (2 ^ n)) ^ b)) := by ring
      _ = -((2 : ZMod (2 ^ n)) * (0 - 1) + 1) := by rw [hMod]
      _ = 1 := by ring
  have hCong :
      3 ^ k * (1 + 2 ^ a + 2 ^ b) ≡ 1 [MOD 2 ^ n] := by
    simpa [← ZMod.natCast_eq_natCast_iff] using hRel
  have hProdOne : 1 ≤ 3 ^ k * (1 + 2 ^ a + 2 ^ b) := by
    have hThreePos : 0 < 3 ^ k := Nat.pow_pos (by norm_num)
    have hFactorPos : 0 < 1 + 2 ^ a + 2 ^ b := by
      simp only [add_pos_iff, Order.lt_one_iff, Order.lt_two_iff, zero_le, pow_pos, or_self]
    exact Nat.mul_pos hThreePos hFactorPos
  exact (Nat.modEq_iff_dvd' hProdOne).mp hCong.symm

/-- source correction から `n < 2k+b+1`。 -/
private theorem sourceTwo_sourceLength_lt
    {k n a b : ℕ}
    (hk : 0 < k)
    (hab : a < b)
    (hDvd : 2 ^ n ∣ 3 ^ k * (1 + 2 ^ a + 2 ^ b) - 1) :
    n < 2 * k + b + 1 := by
  let B : ℕ := 3 ^ k * (1 + 2 ^ a + 2 ^ b) - 1
  have hThree : 1 < 3 ^ k :=
    one_lt_pow₀ (by norm_num : (1 : ℕ) < 3) (Nat.ne_of_gt hk)
  have hBPos : 0 < B := by
    dsimp [B]
    have : 1 < 3 ^ k * (1 + 2 ^ a + 2 ^ b) := by
      calc
        1 < 3 ^ k := hThree
        _ ≤ 3 ^ k * (1 + 2 ^ a + 2 ^ b) := by
          exact Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hTwoLe : 2 ^ n ≤ B := Nat.le_of_dvd hBPos hDvd
  have hBLt : B < 3 ^ k * (1 + 2 ^ a + 2 ^ b) := by
    dsimp [B]
    omega
  have hThreeLt := sourceTwo_threePow_lt_twoPow_double hk
  have hAB : 1 + 2 ^ a ≤ 2 ^ b := by
    have hPow : 2 ^ (a + 1) ≤ 2 ^ b :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
    have hSmall : 1 + 2 ^ a ≤ 2 ^ (a + 1) := by
      rw [pow_succ]
      have hp : 0 < 2 ^ a := by positivity
      omega
    exact le_trans hSmall hPow
  have hSumLe : 1 + 2 ^ a + 2 ^ b ≤ 2 ^ (b + 1) := by
    rw [pow_succ]
    omega
  have hProdLt :
      3 ^ k * (1 + 2 ^ a + 2 ^ b) <
        2 ^ (2 * k) * 2 ^ (b + 1) := by
    calc
      3 ^ k * (1 + 2 ^ a + 2 ^ b) <
          2 ^ (2 * k) * (1 + 2 ^ a + 2 ^ b) :=
        Nat.mul_lt_mul_of_pos_right hThreeLt (by positivity)
      _ ≤ 2 ^ (2 * k) * 2 ^ (b + 1) :=
        Nat.mul_le_mul_left _ hSumLe
  have hPowLt : 2 ^ n < 2 ^ (2 * k + b + 1) := by
    calc
      2 ^ n ≤ B := hTwoLe
      _ < 3 ^ k * (1 + 2 ^ a + 2 ^ b) := hBLt
      _ < 2 ^ (2 * k) * 2 ^ (b + 1) := hProdLt
      _ = 2 ^ (2 * k + b + 1) := by
        rw [← pow_add]
        congr 1
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hPowLt

/-- 元の `r=1` 等式から `L+1 <= 2k+n`。 -/
private theorem sourceTwo_targetExponent_le
    {k n L a b : ℕ}
    (hk : 0 < k)
    (hab : a < b)
    (hbn : b < n)
    (hEq : SourceTwoHoleEquation k n 1 L a b) :
    L + 1 ≤ 2 * k + n := by
  have hNat := sourceTwo_exitOne_nat_identity hab hbn hEq
  let s : ℕ := 2 ^ n - 1 - 2 ^ a - 2 ^ b
  have hSlt : s < 2 ^ n := by
    dsimp [s]
    have hPos : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
    have hSub : 2 ^ n - 1 < 2 ^ n := by omega
    have hLe : 2 ^ n - 1 - 2 ^ a - 2 ^ b ≤ 2 ^ n - 1 := by
      exact le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
    exact lt_of_le_of_lt hLe hSub
  have hThreeLt := sourceTwo_threePow_lt_twoPow_double hk
  have hProdLt : 3 ^ k * s < 2 ^ (2 * k) * 2 ^ n := by
    by_cases hs0 : s = 0
    · simp [hs0]
    · have hsPos : 0 < s := Nat.pos_of_ne_zero hs0
      calc
        3 ^ k * s < 2 ^ (2 * k) * s :=
          Nat.mul_lt_mul_of_pos_right hThreeLt hsPos
        _ < 2 ^ (2 * k) * 2 ^ n :=
          Nat.mul_lt_mul_of_pos_left hSlt (by positivity)
  have hProdLtPow : 3 ^ k * s < 2 ^ (2 * k + n) := by
    calc
      3 ^ k * s < 2 ^ (2 * k) * 2 ^ n := hProdLt
      _ = 2 ^ (2 * k + n) := by rw [← pow_add]
  have hSuccLe : 3 ^ k * s + 1 ≤ 2 ^ (2 * k + n) := by
    omega
  have hPowLe : 2 ^ (L + 1) ≤ 2 ^ (2 * k + n) := by
    dsimp [s] at hSuccLe
    rw [← hNat]
    exact hSuccLe
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hPowLe

/-- `k>=7` では `2*3^(k-1)` が `7k+3` を上回る。 -/
private theorem seven_mul_add_three_lt_two_mul_threePow_pred
    (k : ℕ)
    (hk : 7 ≤ k) :
    7 * k + 3 < 2 * 3 ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
      rw [show (k + 1) - 1 = k by omega]
      have hkOne : 1 ≤ k := by omega
      have hkEq : k = (k - 1) + 1 := (Nat.sub_add_cancel hkOne).symm
      have hPow : 3 ^ k = 3 ^ (k - 1) * 3 := by
        calc
          3 ^ k = 3 ^ ((k - 1) + 1) :=
            congrArg (fun e : ℕ => 3 ^ e) hkEq
          _ = 3 ^ (k - 1) * 3 := by rw [pow_succ]
      have hPowPos : 0 < 3 ^ (k - 1) := by positivity
      rw [hPow]
      nlinarith

/--
source-two-hole の `r=1` regular equation は `k>=7` では不可能。

二つの low-bit correction から順に `a,b,n,L` を線形に抑え、
`3^k | 2^(L+1)-1` が要求する exponential order と衝突させる。
-/
theorem SourceTwoHoleEquation.largeDepth_exit_one_impossible
    {k n L a b : ℕ}
    (hk7 : 7 ≤ k)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbn : b < n)
    (hL : 0 < L)
    (hEq : SourceTwoHoleEquation k n 1 L a b) :
    False := by
  have hkPos : 0 < k := by omega
  have hnL := sourceTwo_exitOne_n_le_L hk7 ha0 hab hbn hEq
  have haLe :=
    sourceTwo_firstHole_le_depth_add_two
      hkPos ha0 hab hbn hnL hEq
  have hBDvd :=
    sourceTwo_secondHole_dvd_correction hbn hnL hEq
  have hbLt := sourceTwo_secondHole_lt hkPos hBDvd
  have hbLinear : b < 3 * k + 3 := by omega
  have hNDvd :=
    sourceTwo_sourceLength_dvd_correction hnL hEq
  have hnLt := sourceTwo_sourceLength_lt hkPos hab hNDvd
  have hnLinear : n < 5 * k + 3 := by omega
  have hTargetLe := sourceTwo_targetExponent_le hkPos hab hbn hEq
  have hTargetLinear : L + 1 < 7 * k + 3 := by omega
  have hMod := hEq.to_mod (3 ^ k)
  unfold SourceTwoHoleModEquation at hMod
  have hThreeZero : (3 : ZMod (3 ^ k)) ^ k = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 3 (le_rfl : k ≤ k)
  rw [hThreeZero] at hMod
  simp only [pow_one] at hMod
  have hPow : (2 : ZMod (3 ^ k)) ^ (L + 1) = 1 := by
    rw [pow_succ]
    linear_combination -hMod
  have hCong : 2 ^ (L + 1) ≡ 1 [MOD 3 ^ k] := by
    simpa [← ZMod.natCast_eq_natCast_iff] using hPow
  have hOrderDvd : 2 * 3 ^ (k - 1) ∣ L + 1 :=
    two_mul_threePow_pred_dvd_exponent_of_twoPow_modEq_one hkPos hCong
  have hOrderLe : 2 * 3 ^ (k - 1) ≤ L + 1 :=
    Nat.le_of_dvd (by omega : 0 < L + 1) hOrderDvd
  have hExp := seven_mul_add_three_lt_two_mul_threePow_pred k hk7
  omega

/--
`k>=7` の source-two-hole が存在するなら、mod 4/8 で既に同定された
二つの low resonance のどちらかに必ず入る。
-/
theorem SourceTwoHoleEquation.largeDepth_forces_lowResonance
    {k n r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbn : b < n)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : SourceTwoHoleEquation k n r L a b) :
    SourceTwoHoleLowResonance k a b := by
  rcases Nat.mod_two_eq_zero_or_one k with hkEven | hkOdd
  · by_cases ha1 : a = 1
    · subst a
      by_cases hb2 : b = 2
      · exact Or.inl ⟨hkEven, rfl, hb2⟩
      · have hb3 : 3 ≤ b := by omega
        have hr2 :=
          hEq.exitDepth_eq_two_of_even_one_then_three
            hkEven hb3 hbn hr hL
        subst r
        exact (hEq.exitDepth_two_impossible (by omega)).elim
    · have ha2 : 2 ≤ a := by omega
      have hr1 :=
        hEq.exitDepth_eq_one_of_even_of_two_le_firstHole
          hkEven ha2 hab hbn hr
      subst r
      exact
        (hEq.largeDepth_exit_one_impossible
          hk7 ha0 hab hbn hL).elim
  · by_cases ha1 : a = 1
    · subst a
      have hr1 :=
        hEq.exitDepth_eq_one_of_odd_firstHole_one
          hkOdd hbn (by omega) hr
      subst r
      exact
        (hEq.largeDepth_exit_one_impossible
          hk7 (by omega) hab hbn hL).elim
    · by_cases ha2 : a = 2
      · exact Or.inr ⟨hkOdd, ha2⟩
      · have ha3 : 3 ≤ a := by omega
        have hr2 :=
          hEq.exitDepth_eq_two_of_odd_of_three_le_firstHole
            hkOdd ha3 hab hbn hr hL
        subst r
        exact (hEq.exitDepth_two_impossible (by omega)).elim

end Mersenne
end Collatz3
