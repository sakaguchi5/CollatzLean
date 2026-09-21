import CollatzLean.Collatz3.Mersenne.SmallHoleModular
import CollatzLean.Collatz3.Arithmetic.TwoThreeUnit
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: two-hole six-unit 共通算術

source-two / target-two の minimal certificate 排除で共通に使う小さな指数算術だけを集める。
ここでは Collatz 固有の pattern は定義せず、`3^k+1=2^e` と
`2^n 3^k + 2^s = 2^(s+T)` のような局所等式だけを扱う。
-/

namespace Collatz3
namespace Mersenne
namespace TwoHoleUnitArithmetic

open Arithmetic

/-- 正の `3^k` は `ZMod 3` で 0。 -/
theorem threePow_zmod3_eq_zero_of_pos
    {k : ℕ}
    (hk : 0 < k) :
    (3 : ZMod 3) ^ k = 0 := by
  simpa using ZMod.natCast_pow_eq_zero_of_le 3 hk

/-- `2` は `ZMod 3` の unit なので、その冪は 0 にならない。 -/
theorem twoPow_ne_zero_zmod3
    (e : ℕ) :
    (2 : ZMod 3) ^ e ≠ 0 := by
  have hUnit : IsUnit (2 : ZMod 3) := by
    exact (ZMod.isUnit_iff_coprime 2 3).2 (by decide)
  exact (hUnit.pow e).ne_zero

/-- `3^k+1` が 2 冪なら、正の `k` では `k=1`。 -/
theorem threePow_add_one_eq_twoPow_depth_one
    {k e : ℕ}
    (hk : 0 < k)
    (hEq : 3 ^ k + 1 = 2 ^ e) :
    k = 1 := by
  by_contra hkOne
  have hkTwo : 2 ≤ k := by omega
  have hNine : 9 ≤ 3 ^ k := by
    calc
      9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hkTwo
  have heThree : 3 ≤ e := by
    by_contra hNot
    have heLe : e ≤ 2 := by omega
    have hPowLe : 2 ^ e ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) heLe
    norm_num at hPowLe
    omega
  have hCast := congrArg (fun z : ℕ => (z : ZMod 8)) hEq
  push_cast at hCast
  have hTwo : (2 : ZMod 8) ^ e = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 heThree
  have hPeriod : (3 : ZMod 8) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 8) (e := k) hPeriod] at hCast
  rw [hTwo] at hCast
  rcases Nat.mod_two_eq_zero_or_one k with hkEven | hkOdd
  · norm_num [hkEven] at hCast
    exact (by decide : (2 : ZMod 8) ≠ 0) hCast
  · norm_num [hkOdd] at hCast
    exact (by decide : (4 : ZMod 8) ≠ 0) hCast

/--
`2^n*3^k + 2^s = 2^(s+T)` かつ `T>0` なら、二つの左項の 2-adic 位相は一致する。
-/
theorem sourceTop_plus_twoPow_forces_same_twoExp
    {k n s T : ℕ}
    (hT : 0 < T)
    (hEq : 2 ^ n * 3 ^ k + 2 ^ s = 2 ^ (s + T)) :
    n = s := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hns | hsn
  · let d : ℕ := s - n
    have hd : 0 < d := by dsimp [d]; omega
    have hsEq : s = n + d := by dsimp [d]; omega
    have hExp : s + T = n + (d + T) := by omega
    have hFactor :
        2 ^ n * (3 ^ k + 2 ^ d) = 2 ^ n * 2 ^ (d + T) := by
      calc
        2 ^ n * (3 ^ k + 2 ^ d)
            = 2 ^ n * 3 ^ k + 2 ^ (n + d) := by
                rw [pow_add]
                ring
        _ = 2 ^ n * 3 ^ k + 2 ^ s := by rw [← hsEq]
        _ = 2 ^ (s + T) := hEq
        _ = 2 ^ (n + (d + T)) := by rw [hExp]
        _ = 2 ^ n * 2 ^ (d + T) := by rw [pow_add]
    have hCancel : 3 ^ k + 2 ^ d = 2 ^ (d + T) :=
      Nat.mul_left_cancel (by positivity) hFactor
    rcases SignedTwoThreeUnit.threePow_eq_two_mul_add_one k with ⟨q, hq⟩
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    have hEvenD : ∃ x : ℕ, 2 ^ d = 2 * x := by
      refine ⟨2 ^ j, ?_⟩
      rw [hj, pow_succ]
      ring
    have hdT : 0 < d + T := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdT)
    have hEvenDT : ∃ y : ℕ, 2 ^ (d + T) = 2 * y := by
      refine ⟨2 ^ m, ?_⟩
      rw [hm, pow_succ]
      ring
    rcases hEvenD with ⟨x, hx⟩
    rcases hEvenDT with ⟨y, hy⟩
    rw [hq, hx, hy] at hCancel
    omega
  · let d : ℕ := n - s
    have hd : 0 < d := by dsimp [d]; omega
    have hnEq : n = s + d := by dsimp [d]; omega
    have hFactor :
        2 ^ s * (2 ^ d * 3 ^ k + 1) = 2 ^ s * 2 ^ T := by
      calc
        2 ^ s * (2 ^ d * 3 ^ k + 1)
            = 2 ^ (s + d) * 3 ^ k + 2 ^ s := by
                rw [pow_add]
                ring
        _ = 2 ^ n * 3 ^ k + 2 ^ s := by rw [← hnEq]
        _ = 2 ^ (s + T) := hEq
        _ = 2 ^ s * 2 ^ T := by rw [pow_add]
    have hCancel : 2 ^ d * 3 ^ k + 1 = 2 ^ T :=
      Nat.mul_left_cancel (by positivity) hFactor
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    have hEvenLeft : ∃ x : ℕ, 2 ^ d * 3 ^ k = 2 * x := by
      refine ⟨2 ^ j * 3 ^ k, ?_⟩
      rw [hj, pow_succ]
      ring
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
    have hEvenRight : ∃ y : ℕ, 2 ^ T = 2 * y := by
      refine ⟨2 ^ m, ?_⟩
      rw [hm, pow_succ]
      ring
    rcases hEvenLeft with ⟨x, hx⟩
    rcases hEvenRight with ⟨y, hy⟩
    rw [hx, hy] at hCancel
    omega

/-- 上の 2-adic 一致により、同型方程式は `3^k+1=2^T` へ落ちる。 -/
theorem sourceTop_plus_twoPow_depth_one
    {k n s T : ℕ}
    (hk : 0 < k)
    (hT : 0 < T)
    (hEq : 2 ^ n * 3 ^ k + 2 ^ s = 2 ^ (s + T)) :
    k = 1 := by
  have hns := sourceTop_plus_twoPow_forces_same_twoExp hT hEq
  subst n
  have hFactor :
      2 ^ s * (3 ^ k + 1) = 2 ^ s * 2 ^ T := by
    rw [pow_add] at hEq
    simpa [mul_add, mul_assoc] using hEq
  have hCore : 3 ^ k + 1 = 2 ^ T :=
    Nat.mul_left_cancel (by positivity) hFactor
  exact threePow_add_one_eq_twoPow_depth_one hk hCore

end TwoHoleUnitArithmetic
end Mersenne
end Collatz3
