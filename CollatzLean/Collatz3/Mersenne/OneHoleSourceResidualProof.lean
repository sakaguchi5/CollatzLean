import CollatzLean.Collatz3.Arithmetic.ThreeOrderModTwoPow
import CollatzLean.Collatz3.Arithmetic.TwoOrderModThreePow
import CollatzLean.Collatz3.Mersenne.OneHoleThreeTailLargeDepth

/-!
# Collatz3 Mersenne: one-hole source residual の完全排除

`OneHoleThreeTailLargeDepth` により、`k≥6` の source-one は

* `k` even,
* `3 ≤ a < n`,
* `r = 1`

という一枝 S だけに縮約された。

このファイルでは S

`3^k (2^n - 1 - 2^a) = 2^(L+1) - 1`

を elementary arithmetic で排除する。

核心は二つ。

1. low-bit congruence から `2^(a-2) ∣ k` を得て `a ≤ k+2`。
2. `3^k ∣ 2^(L+1)-1` から `2*3^(k-1) ∣ L+1`。

一方、元の等式から `n < 3k+3`, `L+1 ≤ 2k+n` を得るので
`L+1 < 5k+3`。`k≥6` では `5k+3 < 2*3^(k-1)` となり矛盾する。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

/-- source one-hole, `r=1` の整数等式を自然数の `+1` 形へ戻す。 -/
private theorem sourceOne_exitOne_nat_identity
    {k n L a : ℕ}
    (han : a < n)
    (hEq : SourceOneHoleEquation k n 1 L a) :
    3 ^ k * (2 ^ n - 1 - 2 ^ a) + 1 = 2 ^ (L + 1) := by
  have hPowPos : 0 < 2 ^ n := by
    positivity
  have hOneLe : 1 ≤ 2 ^ n := by
    omega
  have hPowLt : 2 ^ a < 2 ^ n := by
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).2 han
  have hPowLe : 2 ^ a ≤ 2 ^ n - 1 := by omega
  let s : ℕ := 2 ^ n - 1 - 2 ^ a
  have hsCast :
      (s : ℤ) = (2 : ℤ) ^ n - 1 - (2 : ℤ) ^ a := by
    dsimp [s]
    rw [Nat.cast_sub hPowLe, Nat.cast_sub hOneLe]
    norm_num
  have hInt :
      (3 : ℤ) ^ k * (s : ℤ) + 1 = (2 : ℤ) ^ (L + 1) := by
    unfold SourceOneHoleEquation at hEq
    simp only [pow_one] at hEq
    rw [hsCast]
    rw [pow_succ]
    linear_combination hEq
  have hNat :
      3 ^ k * s + 1 = 2 ^ (L + 1) := by
    exact_mod_cast hInt
  simpa [s] using hNat

/-- source factor は `2^(n-1)-1` 以上。 -/
private theorem sourceOne_factor_lower
    {n a : ℕ}
    (ha3 : 3 ≤ a)
    (han : a < n) :
    2 ^ (n - 1) - 1 ≤ 2 ^ n - 1 - 2 ^ a := by
  have hnPos : 0 < n := by omega
  have haLe : a ≤ n - 1 := by omega
  have hPowLe : 2 ^ a ≤ 2 ^ (n - 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) haLe
  have hnOne : 1 ≤ n := by omega
  have hnEq : n = (n - 1) + 1 := (Nat.sub_add_cancel hnOne).symm
  have hPowN : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) :=
        congrArg (fun e : ℕ => 2 ^ e) hnEq
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := by ac_rfl
  rw [hPowN]
  omega

/-- S では source length は target exponent 以下。 -/
private theorem sourceOne_residual_n_le_L
    {k n L a : ℕ}
    (hk6 : 6 ≤ k)
    (ha3 : 3 ≤ a)
    (han : a < n)
    (hEq : SourceOneHoleEquation k n 1 L a) :
    n ≤ L := by
  have hNat := sourceOne_exitOne_nat_identity han hEq
  have hFactor := sourceOne_factor_lower ha3 han
  have hn4 : 4 ≤ n := by omega
  have hX8 : 8 ≤ 2 ^ (n - 1) := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (n - 1) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
  have hThree : 729 ≤ 3 ^ k := by
    calc
      729 = 3 ^ 6 := by norm_num
      _ ≤ 3 ^ k :=
        Nat.pow_le_pow_right (by norm_num : 0 < 3) hk6
  have hMul :
      729 * (2 ^ (n - 1) - 1) ≤
        3 ^ k * (2 ^ n - 1 - 2 ^ a) :=
    Nat.mul_le_mul hThree hFactor
  have hnOne : 1 ≤ n := by omega
  have hnEq : n = (n - 1) + 1 := (Nat.sub_add_cancel hnOne).symm
  have hTwoN : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc
      2 ^ n = 2 ^ ((n - 1) + 1) :=
        congrArg (fun e : ℕ => 2 ^ e) hnEq
      _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (n - 1) := by ac_rfl
  have hSmall :
      2 * 2 ^ (n - 1) < 729 * (2 ^ (n - 1) - 1) + 1 := by
    omega
  have hMulSucc :
      729 * (2 ^ (n - 1) - 1) + 1 ≤
        3 ^ k * (2 ^ n - 1 - 2 ^ a) + 1 :=
    Nat.add_le_add_right hMul 1
  have hBig :
      2 ^ n < 3 ^ k * (2 ^ n - 1 - 2 ^ a) + 1 := by
    calc
      2 ^ n = 2 * 2 ^ (n - 1) := hTwoN
      _ < 729 * (2 ^ (n - 1) - 1) + 1 := hSmall
      _ ≤ 3 ^ k * (2 ^ n - 1 - 2 ^ a) + 1 := hMulSucc
  by_contra hNot
  have hExp : L + 1 ≤ n := by omega
  have hPow : 2 ^ (L + 1) ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hExp
  rw [← hNat] at hPow
  omega

/-- low-bit congruence は `2^(a-2) ∣ k` を強制する。 -/
private theorem sourceOne_residual_twoPow_hole_dvd_depth
    {k n L a : ℕ}
    (ha3 : 3 ≤ a)
    (han : a < n)
    (hnL : n ≤ L)
    (hEq : SourceOneHoleEquation k n 1 L a) :
    2 ^ (a - 2) ∣ k := by
  have hMod := hEq.to_mod (2 ^ a)
  unfold SourceOneHoleModEquation at hMod
  have hNZero : (2 : ZMod (2 ^ a)) ^ n = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : a ≤ n)
  have hAZero : (2 : ZMod (2 ^ a)) ^ a = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (le_rfl : a ≤ a)
  have hLZero : (2 : ZMod (2 ^ a)) ^ L = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (by omega : a ≤ L)
  rw [hNZero, hAZero, hLZero] at hMod
  simp only [pow_one] at hMod
  have hPow : (3 : ZMod (2 ^ a)) ^ k = 1 := by
    linear_combination -hMod
  have hCong : 3 ^ k ≡ 1 [MOD 2 ^ a] := by
    simpa [← ZMod.natCast_eq_natCast_iff] using hPow
  exact twoPow_dvd_exponent_of_threePow_modEq_one ha3 hCong

/-- low-bit divisibility から hole position は線形に抑えられる。 -/
private theorem sourceOne_residual_hole_le_depth_add_two
    {k a : ℕ}
    (hk : 0 < k)
    (ha3 : 3 ≤ a)
    (hDvd : 2 ^ (a - 2) ∣ k) :
    a ≤ k + 2 := by
  have hPowLe : 2 ^ (a - 2) ≤ k :=
    Nat.le_of_dvd hk hDvd
  have hIndexLt : a - 2 < 2 ^ (a - 2) :=
    (a - 2).lt_two_pow_self
  omega

/-- S の等式から `2^n` が low-bit correction を割る。 -/
private theorem sourceOne_residual_twoPow_source_dvd_correction
    {k n L a : ℕ}
    (hnL : n ≤ L)
    (hEq : SourceOneHoleEquation k n 1 L a) :
    2 ^ n ∣ 3 ^ k * (1 + 2 ^ a) - 1 := by
  have hMod := hEq.to_mod (2 ^ n)
  unfold SourceOneHoleModEquation at hMod
  have hNZero : (2 : ZMod (2 ^ n)) ^ n = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (le_rfl : n ≤ n)
  have hLZero : (2 : ZMod (2 ^ n)) ^ L = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 hnL
  rw [hNZero, hLZero] at hMod
  simp only [pow_one] at hMod
  have hRel :
      (3 : ZMod (2 ^ n)) ^ k *
          (1 + (2 : ZMod (2 ^ n)) ^ a) = 1 := by
    calc
      (3 : ZMod (2 ^ n)) ^ k *
          (1 + (2 : ZMod (2 ^ n)) ^ a)
          = -((3 : ZMod (2 ^ n)) ^ k *
              (0 - 1 - (2 : ZMod (2 ^ n)) ^ a)) := by ring
      _ = -((2 : ZMod (2 ^ n)) * (0 - 1) + 1) := by rw [hMod]
      _ = 1 := by ring
  have hCong :
      3 ^ k * (1 + 2 ^ a) ≡ 1 [MOD 2 ^ n] := by
    simpa [← ZMod.natCast_eq_natCast_iff] using hRel
  have hProdPos : 0 < 3 ^ k * (1 + 2 ^ a) := by
    positivity
  have hProdOneLe : 1 ≤ 3 ^ k * (1 + 2 ^ a) := by
    omega
  exact
    (Nat.modEq_iff_dvd' hProdOneLe).mp hCong.symm

/-- `3^k < 2^(2k)`。 -/
private theorem threePow_lt_twoPow_double
    {k : ℕ}
    (hk : 0 < k) :
    3 ^ k < 2 ^ (2 * k) := by
  have h34 : 3 ^ k < 4 ^ k :=
    Nat.pow_lt_pow_left (by norm_num : 3 < 4) (Nat.ne_of_gt hk)
  calc
    3 ^ k < 4 ^ k := h34
    _ = 2 ^ (2 * k) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]

/-- correction の divisibility と `3<4` から `n` を線形に抑える。 -/
private theorem sourceOne_residual_n_lt
    {k n a : ℕ}
    (hk : 0 < k)
    (hDvd : 2 ^ n ∣ 3 ^ k * (1 + 2 ^ a) - 1) :
    n < 2 * k + a + 1 := by
  let B : ℕ := 3 ^ k * (1 + 2 ^ a) - 1
  have hProdGtOne : 1 < 3 ^ k * (1 + 2 ^ a) := by
    have hThree : 1 < 3 ^ k :=
      one_lt_pow₀ (by norm_num : (1 : ℕ) < 3) (Nat.ne_of_gt hk)
    have hSecondOne : 1 ≤ 1 + 2 ^ a := by
      simp
    have hThreeLeProd :
        3 ^ k ≤ 3 ^ k * (1 + 2 ^ a) := by
      simp only [Nat.ofNat_pos, pow_pos, le_mul_iff_one_le_right,
                 le_add_iff_nonneg_right, zero_le]
    exact hThree.trans_le hThreeLeProd
  have hBPos : 0 < B := by
    dsimp [B]
    omega
  have hTwoNLe : 2 ^ n ≤ B :=
    Nat.le_of_dvd hBPos hDvd
  have hBLt : B < 3 ^ k * (1 + 2 ^ a) := by
    dsimp [B]
    omega
  have hThreeLt := threePow_lt_twoPow_double hk
  have hSecondLe : 1 + 2 ^ a ≤ 2 ^ (a + 1) := by
    rw [pow_succ]
    have hPos : 0 < 2 ^ a := by
      positivity
    omega
  have hProdLt :
      3 ^ k * (1 + 2 ^ a) <
        2 ^ (2 * k) * 2 ^ (a + 1) := by
    calc
      3 ^ k * (1 + 2 ^ a) <
          2 ^ (2 * k) * (1 + 2 ^ a) :=
        Nat.mul_lt_mul_of_pos_right hThreeLt (by positivity)
      _ ≤ 2 ^ (2 * k) * 2 ^ (a + 1) :=
        Nat.mul_le_mul_left _ hSecondLe
  have hPowLt : 2 ^ n < 2 ^ (2 * k + a + 1) := by
    calc
      2 ^ n ≤ B := hTwoNLe
      _ < 3 ^ k * (1 + 2 ^ a) := hBLt
      _ < 2 ^ (2 * k) * 2 ^ (a + 1) := hProdLt
      _ = 2 ^ (2 * k + a + 1) := by
        rw [← pow_add]
        congr 1
  exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hPowLt

/-- 元の等式そのものから `L+1 ≤ 2k+n`。 -/
private theorem sourceOne_residual_targetExponent_le
    {k n L a : ℕ}
    (hk : 0 < k)
    (han : a < n)
    (hEq : SourceOneHoleEquation k n 1 L a) :
    L + 1 ≤ 2 * k + n := by
  have hNat := sourceOne_exitOne_nat_identity han hEq
  let s : ℕ := 2 ^ n - 1 - 2 ^ a
  have hSlt : s < 2 ^ n := by
    dsimp [s]
    have hPowPos : 0 < 2 ^ n := by
      positivity
    have hSubOneLt : 2 ^ n - 1 < 2 ^ n := by
      omega
    exact lt_of_le_of_lt (Nat.sub_le _ _) hSubOneLt
  have hThreeLt := threePow_lt_twoPow_double hk
  have hProdLt : 3 ^ k * s < 2 ^ (2 * k) * 2 ^ n := by
    by_cases hs0 : s = 0
    · rw [hs0]
      simp only [mul_zero]
      positivity
    · have hsPos : 0 < s := Nat.pos_of_ne_zero hs0
      calc
        3 ^ k * s < 2 ^ (2 * k) * s :=
          Nat.mul_lt_mul_of_pos_right hThreeLt hsPos
        _ < 2 ^ (2 * k) * 2 ^ n :=
          Nat.mul_lt_mul_of_pos_left hSlt (by positivity)
  have hPowProd : 2 ^ (2 * k) * 2 ^ n = 2 ^ (2 * k + n) := by
    rw [← pow_add]
  have hSuccLe : 3 ^ k * s + 1 ≤ 2 ^ (2 * k + n) := by
    rw [← hPowProd]
    omega
  have hPowLe : 2 ^ (L + 1) ≤ 2 ^ (2 * k + n) := by
    dsimp [s] at hSuccLe
    rw [← hNat]
    exact hSuccLe
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hPowLe

/-- `k≥6` では exponential order lower bound が linear upper bound を上回る。 -/
private theorem five_mul_add_three_lt_two_mul_threePow_pred
    (k : ℕ)
    (hk : 6 ≤ k) :
    5 * k + 3 < 2 * 3 ^ (k - 1) := by
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
      have hPowPos : 0 < 3 ^ (k - 1) := by
        positivity
      rw [hPow]
      nlinarith

/--
残余 S は不可能。

`k≥6`, `k` even, `3≤a<n`, `r=1` を満たす source-one equation は存在しない。
`k` even 自体は証明には不要で、より強い形で排除する。
-/
theorem SourceOneHoleEquation.largeDepth_source_residual_impossible
    {k n L a : ℕ}
    (hk6 : 6 ≤ k)
    (ha3 : 3 ≤ a)
    (han : a < n)
    (hEq : SourceOneHoleEquation k n 1 L a) :
    False := by
  have hkPos : 0 < k := by omega
  have hnL := sourceOne_residual_n_le_L hk6 ha3 han hEq
  have hHoleDvd :=
    sourceOne_residual_twoPow_hole_dvd_depth ha3 han hnL hEq
  have haLe :=
    sourceOne_residual_hole_le_depth_add_two hkPos ha3 hHoleDvd
  have hSourceDvd :=
    sourceOne_residual_twoPow_source_dvd_correction hnL hEq
  have hnLt :=
    sourceOne_residual_n_lt hkPos hSourceDvd
  have hnLinear : n < 3 * k + 3 := by omega
  have hTargetLe :=
    sourceOne_residual_targetExponent_le hkPos han hEq
  have hTargetLinear : L + 1 < 5 * k + 3 := by omega
  have hMod := hEq.to_mod (3 ^ k)
  unfold SourceOneHoleModEquation at hMod
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
  have hExp := five_mul_add_three_lt_two_mul_threePow_pred k hk6
  omega

/--
`OneHoleThreeTailLargeDepth.largeDepth_shape` と S 排除を合成すると、
well-formed な source-one は `k≥6` を持てない。
-/
theorem SourceOneHoleEquation.largeDepth_impossible
    {k n r L a : ℕ}
    (hk6 : 6 ≤ k)
    (ha0 : 0 < a)
    (han : a < n)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : SourceOneHoleEquation k n r L a) :
    False := by
  rcases hEq.largeDepth_shape hk6 ha0 han hr hL with
    ⟨_hkEven, ha3, hr1⟩
  subst r
  exact hEq.largeDepth_source_residual_impossible hk6 ha3 han

/-- well-formed source-one の depth は無条件に `k≤5`。 -/
theorem SourceOneHoleEquation.depth_le_five
    {k n r L a : ℕ}
    (ha0 : 0 < a)
    (han : a < n)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : SourceOneHoleEquation k n r L a) :
    k ≤ 5 := by
  by_contra hNot
  have hk6 : 6 ≤ k := by omega
  exact hEq.largeDepth_impossible hk6 ha0 han hr hL

end Mersenne
end Collatz3
