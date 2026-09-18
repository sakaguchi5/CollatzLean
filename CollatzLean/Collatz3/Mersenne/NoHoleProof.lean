import CollatzLean.Collatz3.Mersenne.SmallHoleModular
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Mersenne: no-hole arithmetic reduction

`NoHoleEquation`

`3^k (2^n - 1) = 2^r (2^L - 1) + 1`

の elementary な部分を可能な限り閉じる。

設計方針は `thin definitions + derived theorems`。

1. `ZMod` と冪の小さな arithmetic helper、
2. `NoHoleEquation` 自身の局所的な帰結、
3. `k=1,2` の小 depth 分類、
4. 二つの residual problem から完全分類、

の順に積み上げる。

このファイルで無条件に証明する主な内容は次の通り。

* mod 3 から `r,L` はともに奇数。
* `n ≥ 3` なら mod 8 から `r=1`, `L≥3`, `k` は偶数。
* `k=1` の全解は `(n,r,L)=(1,1,1),(2,3,1)`。
* `k=2` の全解は `(n,r,L)=(1,3,1),(3,1,5)`。
* `n=1` で `k` が奇数なら必ず `(k,r,L)=(1,1,1)`。

したがって `k≥3` の no-hole problem は、

1. 偶数 exponent の `3^m = 2^r(2^L-1)+1`、
2. 偶数 `k≥4` の `3^k(2^n-1)=2^(L+1)-1`, `n≥3`,

という二つの residual arithmetic problem に縮約される。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

/-! ## Layer 0: generic arithmetic helpers -/

/--
`e ≥ n` なら、`ZMod (2^n)` において `2^e = 0`。

`2^n` が法そのものなので、指数 `e` が少なくとも `n` なら
`2^e` は `2^n` の倍数となり、剰余環では 0 に消える。

以下の `mod 4`, `mod 8`, `mod 16` 用補題の共通基礎。
-/
private theorem two_pow_zmod_two_pow_eq_zero_of_le
    {n e : ℕ}
    (h : n ≤ e) :
    (2 : ZMod (2 ^ n)) ^ e = 0 := by
  exact ZMod.natCast_pow_eq_zero_of_le 2 h

/--
指数が 2 以上なら、`2^e` は `ZMod 4` で 0。

`4 = 2^2` に対する
`two_pow_zmod_two_pow_eq_zero_of_le` の特殊化。
-/
private theorem two_pow_zmod4_eq_zero_of_two_le
    {e : ℕ} (h : 2 ≤ e) :
    (2 : ZMod 4) ^ e = 0 := by
  simpa using
    (two_pow_zmod_two_pow_eq_zero_of_le
      (n := 2) (e := e) h)

/--
指数が 3 以上なら、`2^e` は `ZMod 8` で 0。

`8 = 2^3` に対する
`two_pow_zmod_two_pow_eq_zero_of_le` の特殊化。
-/
private theorem two_pow_zmod8_eq_zero_of_three_le
    {e : ℕ} (h : 3 ≤ e) :
    (2 : ZMod 8) ^ e = 0 := by
  simpa using
    (two_pow_zmod_two_pow_eq_zero_of_le
      (n := 3) (e := e) h)

/--
指数が 4 以上なら、`2^e` は `ZMod 16` で 0。

`16 = 2^4` に対する
`two_pow_zmod_two_pow_eq_zero_of_le` の特殊化。
-/
private theorem two_pow_zmod16_eq_zero_of_four_le
    {e : ℕ} (h : 4 ≤ e) :
    (2 : ZMod 16) ^ e = 0 := by
  simpa using
    (two_pow_zmod_two_pow_eq_zero_of_le
      (n := 4) (e := e) h)

/-- 任意の自然数は mod 2 で `0` または `1`。 -/
private theorem mod_two_eq_zero_or_one (e : ℕ) :
    e % 2 = 0 ∨ e % 2 = 1 := by
  have hLt : e % 2 < 2 := Nat.mod_lt _ (by omega)
  omega

/-- `ZMod 8` では偶数乗の `3` は `1`。 -/
private theorem three_pow_zmod8_eq_one_of_even
    {e : ℕ} (hEven : e % 2 = 0) :
    (3 : ZMod 8) ^ e = 1 := by
  have hPeriod : (3 : ZMod 8) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 8) (e := e) hPeriod]
  simp [hEven]

/-- `ZMod 8` では奇数乗の `3` は `3`。 -/
private theorem three_pow_zmod8_eq_three_of_odd
    {e : ℕ} (hOdd : e % 2 = 1) :
    (3 : ZMod 8) ^ e = 3 := by
  have hPeriod : (3 : ZMod 8) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 8) (e := e) hPeriod]
  simp [hOdd]

/-- 整数上で `2^a = 2^b` なら exponent も等しい。 -/
private theorem two_pow_int_injective
    {a b : ℕ}
    (h : (2 : ℤ) ^ a = (2 : ℤ) ^ b) :
    a = b := by
  have hNat : (2 : ℕ) ^ a = (2 : ℕ) ^ b := by
    exact_mod_cast h
  exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hNat

/-- 整数上で `3^a = 3^b` なら exponent も等しい。 -/
private theorem three_pow_int_injective
    {a b : ℕ}
    (h : (3 : ℤ) ^ a = (3 : ℤ) ^ b) :
    a = b := by
  have hNat : (3 : ℕ) ^ a = (3 : ℕ) ^ b := by
    exact_mod_cast h
  exact Nat.pow_right_injective (by norm_num : 2 ≤ (3 : ℕ)) hNat

/-! ## Layer 1: local consequences of `NoHoleEquation` -/

/--
no-hole equation の mod 3 条件。

`k>0` なら左辺は 0 mod 3。
`2` の mod 3 周期は 2 なので、右辺が 0 になるためには
`r,L` がともに奇数でなければならない。
-/
theorem NoHoleEquation.mod_two_residues
    {k n r L : ℕ}
    (hk : 0 < k)
    (hEq : NoHoleEquation k n r L) :
    r % 2 = 1 ∧ L % 2 = 1 := by
  have hMod := hEq.to_mod 3
  unfold NoHoleModEquation at hMod
  have hTwoPeriod : (2 : ZMod 3) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := r) hTwoPeriod,
      pow_eq_pow_mod_of_pow_eq_one (2 : ZMod 3) (e := L) hTwoPeriod] at hMod
  have hThree : (3 : ZMod 3) ^ k = 0 := by
    obtain ⟨t, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    simp [pow_succ]
    rfl
  rw [hThree] at hMod
  rcases mod_two_eq_zero_or_one r with hr0 | hr1
  · rcases mod_two_eq_zero_or_one L with hL0 | hL1
    · norm_num [hr0, hL0] at hMod
    · norm_num [hr0, hL1] at hMod
      exact False.elim ((by decide : (0 : ZMod 3) ≠ 2) hMod)
  · rcases mod_two_eq_zero_or_one L with hL0 | hL1
    · norm_num [hr1, hL0] at hMod
    · exact ⟨hr1, hL1⟩

/-- `n≥3` なら mod 8 と parity から `r=1`。 -/
private theorem noHole_large_source_r_eq_one
    {k n r L : ℕ}
    (hk : 0 < k)
    (hn : 3 ≤ n)
    (hr : 0 < r)
    (hEq : NoHoleEquation k n r L) :
    r = 1 := by
  have hrMod := (hEq.mod_two_residues hk).1
  by_contra hNe
  have hrThree : 3 ≤ r := by omega
  have hMod := hEq.to_mod 8
  unfold NoHoleModEquation at hMod
  have h2n := two_pow_zmod8_eq_zero_of_three_le hn
  have h2r := two_pow_zmod8_eq_zero_of_three_le hrThree
  rw [h2n, h2r] at hMod
  rcases mod_two_eq_zero_or_one k with hk0 | hk1
  · rw [three_pow_zmod8_eq_one_of_even hk0] at hMod
    norm_num at hMod
    exact (by decide : (-1 : ZMod 8) ≠ 1) hMod
  · rw [three_pow_zmod8_eq_three_of_odd hk1] at hMod
    norm_num at hMod
    exact (by decide : (-3 : ZMod 8) ≠ 1) hMod

/-- `n≥3` かつ `r=1` なら parity と mod 8 から `L≥3`。 -/
private theorem noHole_large_source_L_ge_three
    {k n r L : ℕ}
    (hk : 0 < k)
    (hn : 3 ≤ n)
    (hL : 0 < L)
    (hrOne : r = 1)
    (hEq : NoHoleEquation k n r L) :
    3 ≤ L := by
  have hLMod := (hEq.mod_two_residues hk).2
  by_contra hNot
  have hLEq : L = 1 := by omega
  subst L
  subst r
  have hMod := hEq.to_mod 8
  unfold NoHoleModEquation at hMod
  have h2n := two_pow_zmod8_eq_zero_of_three_le hn
  rw [h2n] at hMod
  rcases mod_two_eq_zero_or_one k with hk0 | hk1
  · rw [three_pow_zmod8_eq_one_of_even hk0] at hMod
    norm_num at hMod
    exact (by decide : (-1 : ZMod 8) ≠ 3) hMod
  · rw [three_pow_zmod8_eq_three_of_odd hk1] at hMod
    norm_num at hMod
    exact (by decide : (-3 : ZMod 8) ≠ 3) hMod

/-- `n≥3`, `r=1`, `L≥3` なら mod 8 から `k` は偶数。 -/
private theorem noHole_large_source_k_even
    {k n r L : ℕ}
    (hn : 3 ≤ n)
    (hrOne : r = 1)
    (hLThree : 3 ≤ L)
    (hEq : NoHoleEquation k n r L) :
    k % 2 = 0 := by
  subst r
  have hMod := hEq.to_mod 8
  unfold NoHoleModEquation at hMod
  have h2n := two_pow_zmod8_eq_zero_of_three_le hn
  have h2L := two_pow_zmod8_eq_zero_of_three_le hLThree
  rw [h2n, h2L] at hMod
  rcases mod_two_eq_zero_or_one k with hk0 | hk1
  · exact hk0
  · rw [three_pow_zmod8_eq_three_of_odd hk1] at hMod
    norm_num at hMod
    exact False.elim ((by decide : (3 : ZMod 8) ≠ 1) hMod)

/--
source length `n≥3` の no-hole equation は非常に rigid。

mod 3 と mod 8 だけで

`r = 1`, `L ≥ 3`, `k` even

まで強制される。
-/
theorem NoHoleEquation.large_source_shape
    {k n r L : ℕ}
    (hk : 0 < k)
    (hn : 3 ≤ n)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : NoHoleEquation k n r L) :
    r = 1 ∧ 3 ≤ L ∧ k % 2 = 0 := by
  have hrOne := noHole_large_source_r_eq_one hk hn hr hEq
  have hLThree := noHole_large_source_L_ge_three hk hn hL hrOne hEq
  have hkEven := noHole_large_source_k_even hn hrOne hLThree hEq
  exact ⟨hrOne, hLThree, hkEven⟩

/-- `n=1`, odd depth なら mod 8 から `r=1`。 -/
private theorem noHole_source_one_odd_r_eq_one
    {k r L : ℕ}
    (hk : 0 < k)
    (hr : 0 < r)
    (hOdd : k % 2 = 1)
    (hEq : NoHoleEquation k 1 r L) :
    r = 1 := by
  have hrMod := (hEq.mod_two_residues hk).1
  by_contra hNe
  have hrThree : 3 ≤ r := by omega
  have hMod := hEq.to_mod 8
  unfold NoHoleModEquation at hMod
  have h2r := two_pow_zmod8_eq_zero_of_three_le hrThree
  rw [h2r, three_pow_zmod8_eq_three_of_odd hOdd] at hMod
  norm_num at hMod
  exact (by decide : (3 : ZMod 8) ≠ 1) hMod

/-- `n=1`, odd depth, `r=1` なら mod 8 から `L=1`。 -/
private theorem noHole_source_one_odd_L_eq_one
    {k r L : ℕ}
    (hk : 0 < k)
    (hL : 0 < L)
    (hOdd : k % 2 = 1)
    (hrOne : r = 1)
    (hEq : NoHoleEquation k 1 r L) :
    L = 1 := by
  have hLMod := (hEq.mod_two_residues hk).2
  by_contra hNe
  have hLThree : 3 ≤ L := by omega
  subst r
  have hMod := hEq.to_mod 8
  unfold NoHoleModEquation at hMod
  have h2L := two_pow_zmod8_eq_zero_of_three_le hLThree
  rw [h2L, three_pow_zmod8_eq_three_of_odd hOdd] at hMod
  norm_num at hMod
  exact (by decide : (3 : ZMod 8) ≠ (-1 : ZMod 8)) hMod

/--
`n=1` かつ odd depth の no-hole equation は最小解しか持たない。

これは large-depth residual を even exponent 側だけに絞るための elementary lemma。
-/
theorem NoHoleEquation.source_one_odd_depth
    {k r L : ℕ}
    (hk : 0 < k)
    (hr : 0 < r)
    (hL : 0 < L)
    (hOdd : k % 2 = 1)
    (hEq : NoHoleEquation k 1 r L) :
    k = 1 ∧ r = 1 ∧ L = 1 := by
  have hrOne := noHole_source_one_odd_r_eq_one hk hr hOdd hEq
  have hLOne := noHole_source_one_odd_L_eq_one hk hL hOdd hrOne hEq
  subst r
  subst L
  have hPowInt : (3 : ℤ) ^ k = (3 : ℤ) ^ 1 := by
    unfold NoHoleEquation at hEq
    norm_num at hEq ⊢
    exact hEq
  have hkOne : k = 1 := three_pow_int_injective hPowInt
  exact ⟨hkOne, rfl, rfl⟩

/--
`n=1`, `k≥3` の解では depth は偶数。

odd depth case は `source_one_odd_depth` により `k=1` へ落ちるため排除される。
-/
theorem NoHoleEquation.source_one_depth_even
    {k r L : ℕ}
    (hk : 3 ≤ k)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : NoHoleEquation k 1 r L) :
    k % 2 = 0 := by
  rcases mod_two_eq_zero_or_one k with hEven | hOdd
  · exact hEven
  · have hSmall := hEq.source_one_odd_depth (by omega) hr hL hOdd
    omega

/-- `n=2` の no-hole equation は `n=1`, depth `k+1` へ exact に移る。 -/
theorem NoHoleEquation.source_two_to_source_one
    {k r L : ℕ}
    (hEq : NoHoleEquation k 2 r L) :
    NoHoleEquation (k + 1) 1 r L := by
  unfold NoHoleEquation at hEq ⊢
  norm_num at hEq ⊢
  rw [pow_succ]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hEq

/-! ## Layer 2: small-depth derived classification -/

/-- `k=1,n=1` は最小解だけ。 -/
private theorem noHole_depth_one_source_one
    {r L : ℕ}
    (hr : 0 < r) (hL : 0 < L)
    (hEq : NoHoleEquation 1 1 r L) :
    r = 1 ∧ L = 1 := by
  rcases hEq.source_one_odd_depth
      (by omega) hr hL (by decide) with
    ⟨_, hrOne, hLOne⟩
  exact ⟨hrOne, hLOne⟩

/-- `k=2,n=1` の唯一の解は `(r,L)=(3,1)`。 -/
private theorem noHole_depth_two_source_one
    {r L : ℕ}
    (hr : 0 < r) (hL : 0 < L)
    (hEq : NoHoleEquation 2 1 r L) :
    r = 3 ∧ L = 1 := by
  have hrOdd := (hEq.mod_two_residues (by omega)).1
  have hNine :
      (9 : ℤ) = (2 : ℤ) ^ r * ((2 : ℤ) ^ L - 1) + 1 := by
    unfold NoHoleEquation at hEq
    norm_num at hEq
    exact hEq
  have hrCases : r = 1 ∨ r = 3 ∨ 5 ≤ r := by omega
  rcases hrCases with hR1 | hR3 | hR5
  · subst r
    have hMod := congrArg (fun z : ℤ => (z : ZMod 4)) hNine
    push_cast at hMod
    by_cases hL1 : L = 1
    · subst L
      norm_num at hMod
      exact False.elim ((by decide : (9 : ZMod 4) ≠ 3) hMod)
    · have hL2 : 2 ≤ L := by omega
      have h2L := two_pow_zmod4_eq_zero_of_two_le hL2
      rw [h2L] at hMod
      norm_num at hMod
      exact False.elim ((by decide : (9 : ZMod 4) ≠ (-1 : ZMod 4)) hMod)
  · subst r
    have hPowInt : (2 : ℤ) ^ L = (2 : ℤ) ^ 1 := by
      norm_num at hNine ⊢
      linarith [hNine]
    exact ⟨rfl, two_pow_int_injective hPowInt⟩
  · have hMod := congrArg (fun z : ℤ => (z : ZMod 16)) hNine
    push_cast at hMod
    have h2r := two_pow_zmod16_eq_zero_of_four_le (by omega : 4 ≤ r)
    rw [h2r] at hMod
    norm_num at hMod
    exact False.elim ((by decide : (9 : ZMod 16) ≠ 1) hMod)

/-- `k=2,n=2` は `k=3,n=1` に移り、odd-depth lemma と矛盾する。 -/
private theorem noHole_depth_two_source_two_impossible
    {r L : ℕ}
    (hr : 0 < r) (hL : 0 < L)
    (hEq : NoHoleEquation 2 2 r L) : False := by
  have hAux : NoHoleEquation 3 1 r L := by
    simpa using hEq.source_two_to_source_one
  have hSmall :=
    hAux.source_one_odd_depth (by omega) hr hL (by decide)
  omega

private theorem noHole_depth_two_large_source
    {n r L : ℕ}
    (hn : 3 ≤ n) (hr : 0 < r) (hL : 0 < L)
    (hEq : NoHoleEquation 2 n r L) :
    n = 3 ∧ r = 1 ∧ L = 5 := by
  rcases hEq.large_source_shape (hk := by omega) hn hr hL with
    ⟨hR, hLThree, _⟩
  subst r
  have hnThree : n = 3 := by
    by_contra hNe
    have hnFour : 4 ≤ n := by omega
    have hNPred : 3 ≤ n - 1 := by omega
    have hPowInt :
        (2 : ℤ) ^ L = 9 * (2 : ℤ) ^ (n - 1) - 4 := by
      unfold NoHoleEquation at hEq
      have hnEq : n = (n - 1) + 1 := by omega
      rw [hnEq] at hEq
      rw [show (2 : ℤ) ^ ((n - 1) + 1) = (2 : ℤ) ^ (n - 1) * 2 by
        rw [pow_succ]] at hEq
      norm_num at hEq
      linarith [hEq]
    have hMod := congrArg (fun z : ℤ => (z : ZMod 8)) hPowInt
    push_cast at hMod
    have h2L := two_pow_zmod8_eq_zero_of_three_le hLThree
    have h2n := two_pow_zmod8_eq_zero_of_three_le hNPred
    rw [h2L, h2n] at hMod
    norm_num at hMod
    exact (by decide : (4 : ZMod 8) ≠ 0) hMod
  subst n
  have hPowInt : (2 : ℤ) ^ L = (2 : ℤ) ^ 5 := by
    unfold NoHoleEquation at hEq
    norm_num at hEq ⊢
    linarith [hEq]
  exact ⟨rfl, rfl, two_pow_int_injective hPowInt⟩

/-- depth `k=1` の no-hole equation を完全分類する。 -/
theorem noHole_depth_one_classification
    {n r L : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hL : 0 < L)
    (hEq : NoHoleEquation 1 n r L) :
    (n = 1 ∧ r = 1 ∧ L = 1) ∨
    (n = 2 ∧ r = 3 ∧ L = 1) := by
  by_cases hnLarge : 3 ≤ n
  · have hShape :=
      hEq.large_source_shape (hk := by omega) hnLarge hr hL
    norm_num at hShape
  · have hnCases : n = 1 ∨ n = 2 := by omega
    rcases hnCases with rfl | rfl
    · rcases noHole_depth_one_source_one hr hL hEq with ⟨rfl, rfl⟩
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · have hAux : NoHoleEquation 2 1 r L := by
        simpa using hEq.source_two_to_source_one
      rcases noHole_depth_two_source_one hr hL hAux with ⟨rfl, rfl⟩
      exact Or.inr ⟨rfl, rfl, rfl⟩

/-- depth `k=2` の no-hole equation を完全分類する。 -/
theorem noHole_depth_two_classification
    {n r L : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hL : 0 < L)
    (hEq : NoHoleEquation 2 n r L) :
    (n = 1 ∧ r = 3 ∧ L = 1) ∨
    (n = 3 ∧ r = 1 ∧ L = 5) := by
  by_cases hnLarge : 3 ≤ n
  · rcases noHole_depth_two_large_source hnLarge hr hL hEq with
      ⟨rfl, rfl, rfl⟩
    exact Or.inr ⟨rfl, rfl, rfl⟩
  · have hnCases : n = 1 ∨ n = 2 := by omega
    rcases hnCases with rfl | rfl
    · rcases noHole_depth_two_source_one hr hL hEq with ⟨rfl, rfl⟩
      exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact False.elim (noHole_depth_two_source_two_impossible hr hL hEq)

/-! ## Layer 3: residual reduction -/

/--
large-depth no-hole の `n=1,2` 側に残る唯一の型。

偶数 exponent `m≥4` の
`3^m = 2^r(2^L-1)+1`
を排除できれば source length 1,2 の large-depth case は閉じる。
-/
def NoHoleEvenSourceOneResidual : Prop :=
  ∀ m r L : ℕ,
    4 ≤ m →
    m % 2 = 0 →
    0 < r →
    0 < L →
    NoHoleEquation m 1 r L →
    False

/--
large-depth no-hole の `n≥3` 側に残る型。

mod 8 までで `r=1`, `k` even が強制されるので、残りは

`3^k(2^n-1)=2^(L+1)-1`

型だけである。
-/
def NoHoleEvenMersenneQuotientResidual : Prop :=
  ∀ k n L : ℕ,
    4 ≤ k →
    k % 2 = 0 →
    3 ≤ n →
    3 ≤ L →
    NoHoleEquation k n 1 L →
    False

/--
二つの residual arithmetic problem が閉じれば、no-hole 完全分類が得られる。

したがって既存 `NoHoleCompleteClassification` の未解決部分は、この二命題だけに局所化される。
-/
theorem noHoleCompleteClassification_of_residuals
    (hSourceOne : NoHoleEvenSourceOneResidual)
    (hQuotient : NoHoleEvenMersenneQuotientResidual) :
    NoHoleCompleteClassification := by
  intro k n r L hk hn hr hL hEq
  by_cases hkLe : k ≤ 2
  · have hkCases : k = 1 ∨ k = 2 := by omega
    rcases hkCases with rfl | rfl
    · rcases noHole_depth_one_classification hn hr hL hEq with h | h
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
    · rcases noHole_depth_two_classification hn hr hL hEq with h | h
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
  · have hkThree : 3 ≤ k := by omega
    by_cases hn1 : n = 1
    · subst n
      have hkEven := hEq.source_one_depth_even hkThree hr hL
      have hkFour : 4 ≤ k := by omega
      exact False.elim (hSourceOne k r L hkFour hkEven hr hL hEq)
    · by_cases hn2 : n = 2
      · subst n
        have hAux : NoHoleEquation (k + 1) 1 r L :=
          hEq.source_two_to_source_one
        have hSuccEven :=
          hAux.source_one_depth_even (by omega) hr hL
        have hSuccFour : 4 ≤ k + 1 := by omega
        exact False.elim
          (hSourceOne (k + 1) r L hSuccFour hSuccEven hr hL hAux)
      · have hnThree : 3 ≤ n := by omega
        rcases hEq.large_source_shape hk hnThree hr hL with
          ⟨hR, hLThree, hkEven⟩
        subst r
        have hkFour : 4 ≤ k := by omega
        exact False.elim
          (hQuotient k n L hkFour hkEven hnThree hLThree hEq)

end Mersenne
end Collatz3
