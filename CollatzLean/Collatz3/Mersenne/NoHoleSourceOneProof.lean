import CollatzLean.Collatz3.Mersenne.NoHoleProof
import CollatzLean.Collatz3.Arithmetic.ThreeOrderModTwoPow
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: source-one no-hole residual の排除

`NoHoleProof` で残った二つの residual のうち、まず

`NoHoleEvenSourceOneResidual`

を完全に閉じる。

対象は

`3^m = 2^r (2^L - 1) + 1`

で、`m ≥ 4` は偶数、`r,L > 0`。

証明の核は次の四段階。

1. mod 3 から既に分かっている `r,L` odd を使い、mod 8 で `r ≥ 3`。
2. `3^m = 1 (mod 2^r)` と
   `ord_(2^r)(3)=2^(r-2)` から `2^(r-2) ∣ m`。
3. `m` と `r+L` がともに偶数なので差の平方へ因数分解し、
   `3^(m/2) < 2^r` を得る。
4. 位数から得る `m/2 ≥ 2^(r-3)` と
   `2^r < 3^(2^(r-3))` (`r≥5`) が矛盾する。
   残る `r=3` も `m≥4` から直ちに矛盾する。

LTE の一般定理を仮定せず、必要な位数だけを
`Arithmetic.ThreeOrderModTwoPow` で elementary に証明している。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

/-- source-one equation を差の形へ移す。 -/
private theorem NoHoleEquation.source_one_difference
    {m r L : ℕ}
    (hEq : NoHoleEquation m 1 r L) :
    (2 : ℤ) ^ (r + L) - (3 : ℤ) ^ m = (2 : ℤ) ^ r - 1 := by
  unfold NoHoleEquation at hEq
  norm_num at hEq
  rw [pow_add]
  linear_combination -hEq

/--
`r ≥ 5` なら `2^r` より `3^(2^(r-3))` の方が大きい。

後段では位数から `m/2 ≥ 2^(r-3)` を得るため、この粗い成長比較で十分。
-/
private theorem twoPow_lt_threePow_twoPow
    (r : ℕ)
    (hr : 5 ≤ r) :
    2 ^ r < 3 ^ (2 ^ (r - 3)) := by
  induction r, hr using Nat.le_induction with
  | base =>
      norm_num
  | succ r hr ih =>
      let X : ℕ := 3 ^ (2 ^ (r - 3))
      have hTwoLtX : 2 < X := by
        have hFourLe : 4 ≤ 2 ^ r := by
          have hPowLe :=
            Nat.pow_le_pow_right
              (by norm_num : 0 < (2 : ℕ))
              (by omega : 2 ≤ r)
          norm_num at hPowLe ⊢
          exact hPowLe
        have hTwoLtPow : 2 < 2 ^ r := by omega
        exact lt_trans hTwoLtPow ih
      have hStep1 : 2 ^ r * 2 < X * 2 := by
        omega
      have hStep2 : X * 2 ≤ X * X :=
        Nat.mul_le_mul_left X (by omega)
      have hExp :
          2 ^ ((r + 1) - 3) = 2 ^ (r - 3) * 2 := by
        rw [show (r + 1) - 3 = (r - 3) + 1 by omega, pow_succ]
      calc
        2 ^ (r + 1) = 2 ^ r * 2 := by rw [pow_succ]
        _ < X * 2 := hStep1
        _ ≤ X * X := hStep2
        _ = 3 ^ (2 ^ ((r + 1) - 3)) := by
          dsimp [X]
          rw [hExp, pow_mul]
          norm_num [pow_two]

/--
source-one equation で even `m` なら `r=1` は不可能。
したがって mod 3 で得る oddness と合わせて `r≥3`。
-/
private theorem noHole_source_one_even_r_ge_three
    {m r L : ℕ}
    (hmPos : 0 < m)
    (hmEven : m % 2 = 0)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : NoHoleEquation m 1 r L) :
    3 ≤ r := by
  have hResidues := hEq.mod_two_residues hmPos
  have hrOdd := hResidues.1
  have hLOdd := hResidues.2
  by_contra hNot
  have hrOne : r = 1 := by omega
  subst r
  have hMod := hEq.to_mod 8
  unfold NoHoleModEquation at hMod
  have hThreePeriod : (3 : ZMod 8) ^ 2 = 1 := by decide
  have hThree : (3 : ZMod 8) ^ m = 1 := by
    rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 8) (e := m) hThreePeriod]
    simp [hmEven]
  rw [hThree] at hMod
  have hLCases : L = 1 ∨ 3 ≤ L := by omega
  rcases hLCases with rfl | hLThree
  · norm_num at hMod
    exact (by decide : (1 : ZMod 8) ≠ 3) hMod
  · have hTwoL : (2 : ZMod 8) ^ L = 0 := by
      simpa using ZMod.natCast_pow_eq_zero_of_le 2 hLThree
    rw [hTwoL] at hMod
    norm_num at hMod
    exact (by decide : (1 : ZMod 8) ≠ -1) hMod

/--
source-one equation から `3^m = 1 (mod 2^r)` を読む。
-/
private theorem noHole_source_one_threePow_eq_one_zmod
    {m r L : ℕ}
    (hEq : NoHoleEquation m 1 r L) :
    (3 : ZMod (2 ^ r)) ^ m = 1 := by
  have hMod := hEq.to_mod (2 ^ r)
  unfold NoHoleModEquation at hMod
  have hTwoR : (2 : ZMod (2 ^ r)) ^ r = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 (le_refl r)
  rw [hTwoR] at hMod
  norm_num at hMod ⊢
  exact hMod

/--
source-one equation と `r≥3` から `2^(r-2) ∣ m`。
-/
private theorem noHole_source_one_order_dvd
    {m r L : ℕ}
    (hrThree : 3 ≤ r)
    (hEq : NoHoleEquation m 1 r L) :
    2 ^ (r - 2) ∣ m := by
  have hPow := noHole_source_one_threePow_eq_one_zmod hEq
  have hOrd : orderOf (3 : ZMod (2 ^ r)) ∣ m :=
    orderOf_dvd_iff_pow_eq_one.mpr hPow
  rwa [Arithmetic.orderOf_three_zmod_twoPow r hrThree] at hOrd

/--
偶数 `m` と odd `r,L` の source-one equation では

`3^(m/2) < 2^r`。

これは

`2^(r+L) - 3^m = 2^r - 1`

を差の平方に分解しただけである。
-/
private theorem noHole_source_one_halfPow_lt_twoPow
    {m r L : ℕ}
    (hmEven : m % 2 = 0)
    (hrOdd : r % 2 = 1)
    (hLOdd : L % 2 = 1)
    (hr : 0 < r)
    (hEq : NoHoleEquation m 1 r L) :
    3 ^ (m / 2) < 2 ^ r := by
  let s : ℕ := m / 2
  let q : ℕ := (r + L) / 2
  have hmDecomp : s * 2 = m := by
    dsimp [s]
    have h := Nat.mod_add_div m 2
    omega
  have hSumMod : (r + L) % 2 = 0 := by
    rw [Nat.add_mod, hrOdd, hLOdd]
  have hSumDecomp : q * 2 = r + L := by
    dsimp [q]
    have h := Nat.mod_add_div (r + L) 2
    omega
  have hDiff := hEq.source_one_difference
  rw [← hSumDecomp, ← hmDecomp, pow_mul, pow_mul] at hDiff
  let A : ℤ := (2 : ℤ) ^ q
  let B : ℤ := (3 : ℤ) ^ s
  have hSquares : A ^ 2 - B ^ 2 = (2 : ℤ) ^ r - 1 := by
    simpa [A, B] using hDiff
  have hProd :
      (A - B) * (A + B) = (2 : ℤ) ^ r - 1 := by
    calc
      (A - B) * (A + B) = A ^ 2 - B ^ 2 := by ring
      _ = (2 : ℤ) ^ r - 1 := hSquares
  have hRhsPos : 0 < (2 : ℤ) ^ r - 1 := by
    have hPow : (1 : ℤ) < (2 : ℤ) ^ r :=
      one_lt_pow₀ (by norm_num : (1 : ℤ) < 2) (Nat.ne_of_gt hr)
    linarith
  have hSumPos : 0 < A + B := by
    dsimp [A, B]
    positivity
  have hProdPos : 0 < (A - B) * (A + B) := by
    rw [hProd]
    exact hRhsPos
  have hDiffPos : 0 < A - B := by
    rcases mul_pos_iff.mp hProdPos with h | h
    · exact h.1
    · linarith [h.2, hSumPos]
  have hDiffOne : (1 : ℤ) ≤ A - B := by omega
  have hSumNonneg : 0 ≤ A + B := le_of_lt hSumPos
  have hSumLeProd : A + B ≤ (A - B) * (A + B) := by
    have hMul := mul_le_mul_of_nonneg_right hDiffOne hSumNonneg
    simpa using hMul
  rw [hProd] at hSumLeProd
  have hBltInt : B < (2 : ℤ) ^ r := by
    linarith
  have hBltInt' : (3 : ℤ) ^ s < (2 : ℤ) ^ r := by
    simpa [B] using hBltInt
  have hBltNat : 3 ^ s < 2 ^ r := by
    exact_mod_cast hBltInt'
  simpa [s] using hBltNat

/--
`NoHoleEvenSourceOneResidual` は無条件に排除できる。
-/
theorem noHoleEvenSourceOneResidual :
    NoHoleEvenSourceOneResidual := by
  intro m r L hmFour hmEven hr hL hEq
  have hmPos : 0 < m := by omega
  have hResidues := hEq.mod_two_residues hmPos
  have hrOdd := hResidues.1
  have hLOdd := hResidues.2
  have hrThree :=
    noHole_source_one_even_r_ge_three hmPos hmEven hr hL hEq
  have hOrderDvd := noHole_source_one_order_dvd hrThree hEq
  have hUpper :=
    noHole_source_one_halfPow_lt_twoPow hmEven hrOdd hLOdd hr hEq
  let s : ℕ := m / 2
  have hmDecomp : s * 2 = m := by
    dsimp [s]
    have h := Nat.mod_add_div m 2
    omega
  rcases hOrderDvd with ⟨c, hc⟩
  have hcPos : 0 < c := by
    by_contra hNot
    have hcZero : c = 0 := by omega
    rw [hcZero] at hc
    simp at hc
    omega
  have hPowSplit :
      2 ^ (r - 2) = 2 ^ (r - 3) * 2 := by
    rw [show r - 2 = (r - 3) + 1 by omega, pow_succ]
  have hsEq : s = 2 ^ (r - 3) * c := by
    have hMul : s * 2 = (2 ^ (r - 3) * c) * 2 := by
      calc
        s * 2 = m := hmDecomp
        _ = 2 ^ (r - 2) * c := hc
        _ = (2 ^ (r - 3) * c) * 2 := by
          rw [hPowSplit]
          ring
    omega
  have hsLower : 2 ^ (r - 3) ≤ s := by
    rw [hsEq]
    calc
      2 ^ (r - 3) = 2 ^ (r - 3) * 1 := by simp
      _ ≤ 2 ^ (r - 3) * c := Nat.mul_le_mul_left _ (by omega)
  have hPowLower : 3 ^ (2 ^ (r - 3)) ≤ 3 ^ s :=
    Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hsLower
  have hrCases : r = 3 ∨ 5 ≤ r := by omega
  rcases hrCases with rfl | hrFive
  · have hsTwo : 2 ≤ s := by omega
    have hNine : 9 ≤ 3 ^ s := by
      have h := Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hsTwo
      norm_num at h ⊢
      exact h
    have hUpperS : 3 ^ s < 8 := by
      simpa [s] using hUpper
    omega
  · have hGrowth := twoPow_lt_threePow_twoPow r hrFive
    have hLowerS : 2 ^ r < 3 ^ s := lt_of_lt_of_le hGrowth hPowLower
    have hUpperS : 3 ^ s < 2 ^ r := by
      simpa [s] using hUpper
    omega

/--
source-one residual が閉じたので、no-hole 完全分類の残りは
`NoHoleEvenMersenneQuotientResidual` 一つだけ。
-/
theorem noHoleCompleteClassification_of_mersenneQuotientResidual
    (hQuotient : NoHoleEvenMersenneQuotientResidual) :
    NoHoleCompleteClassification := by
  exact noHoleCompleteClassification_of_residuals
    noHoleEvenSourceOneResidual hQuotient

end Mersenne
end Collatz3
