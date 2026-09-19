import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity


/-!
# Collatz3 Mersenne: 共通 2-adic arithmetic

one-hole / two-hole の cut proof で重複していた小補題を公開 API にする。
ここでは Mersenne 固有の equation は導入しない。
-/

namespace Collatz3
namespace Mersenne

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- 正の 2 冪は even。 -/
theorem twoPow_even_of_pos
    {n : ℕ}
    (hn : 0 < n) :
    Even (2 ^ n) := by
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  refine ⟨2 ^ m, ?_⟩
  rw [pow_succ]
  ring

/-- `2^n * odd` の 2-adic valuation は exact に `n`。 -/
theorem padicValNat_twoPow_mul_odd
    (n m : ℕ)
    (hm : Odd m) :
    padicValNat 2 (2 ^ n * m) = n := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm
  have hNot : ¬ 2 ∣ m := by
    rintro ⟨c, hc⟩
    rcases hm with ⟨a, ha⟩
    omega
  rw [padicValNat.mul (by positivity) hm0]
  rw [padicValNat.prime_pow]
  rw [padicValNat.eq_zero_of_not_dvd hNot]
  omega

/-- even exponent に対する `v₂(3^m-1)=2+v₂(m)`。 -/
theorem padicValNat_threePow_sub_one
    {m : ℕ}
    (hm : 0 < m)
    (hmEven : Even m) :
    padicValNat 2 (3 ^ m - 1) = 2 + padicValNat 2 m := by
  have hLTE :=
    padicValNat.pow_two_sub_one
      (x := 3) (n := m)
      (by norm_num) (by norm_num)
      (Nat.ne_of_gt hm) hmEven
  have hFour : padicValNat 2 4 = 2 := by
    change padicValNat 2 (2 ^ 2) = 2
    rw [padicValNat.prime_pow]
  have hTwo : padicValNat 2 2 = 1 := by
    simp only [Order.lt_two_iff, Std.le_refl, padicValNat_base]
  rw [hFour, hTwo] at hLTE
  omega

/-- 正の 2 冪倍から 1 を引くと odd。 -/
theorem odd_twoPow_mul_sub_one
    {e m : ℕ}
    (he : 0 < e)
    (hm : 0 < m) :
    Odd (2 ^ e * m - 1) := by
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  let C : ℕ := 2 ^ d * m
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  have hEvenForm : 2 ^ (d + 1) * m = 2 * C := by
    dsimp [C]
    rw [pow_succ]
    ring
  rw [hEvenForm]
  refine ⟨C - 1, ?_⟩
  omega

/-- `C+1=2^e*m`, `e>0`, `m>0` なら `C` は odd。 -/
theorem odd_of_succ_eq_twoPow_mul
    {C e m : ℕ}
    (he : 0 < e)
    (hm : 0 < m)
    (h : C + 1 = 2 ^ e * m) :
    Odd C := by
  have hOdd := odd_twoPow_mul_sub_one he hm
  have hLe : 1 ≤ 2 ^ e * m := by
    have hProdPos : 0 < 2 ^ e * m := by
      exact Nat.mul_pos (Nat.pow_pos (by norm_num)) hm
    omega
  have hC : C = 2 ^ e * m - 1 := by omega
  simpa [hC] using hOdd

end Mersenne
end Collatz3
