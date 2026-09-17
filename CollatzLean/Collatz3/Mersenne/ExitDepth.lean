import CollatzLean.Collatz3.Mersenne.OneZero
import Mathlib.Tactic.Ring

import Mathlib.Tactic.NormNum

/-!
# Collatz3 Mersenne: one-zero exit depth

`n ≥ 3` の one-zero family では、macro endpoint の追加 2-depth `r` は
zero position `k` の偶奇だけで決まる。

* `k` 偶数なら `r = 1`
* `k` 奇数なら `r = 2`

証明は valuation function を primitive にせず、`3^k (2^n-1)` の
mod `4` / mod `8` に相当する exact decomposition だけで行う。
-/

namespace Collatz3
namespace Mersenne

private theorem exists_threePow_even_eq_eight_mul_add_one
    (j : ℕ) :
    ∃ q : ℕ, 3 ^ (2 * j) = 8 * q + 1 := by
  induction j with
  | zero =>
      exact ⟨0, by norm_num⟩
  | succ j ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨9 * q + 1, ?_⟩
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, hq]
      norm_num
      ring

private theorem exists_threePow_odd_eq_eight_mul_add_three
    (j : ℕ) :
    ∃ q : ℕ, 3 ^ (2 * j + 1) = 8 * q + 3 := by
  rcases exists_threePow_even_eq_eight_mul_add_one j with ⟨q, hq⟩
  refine ⟨3 * q, ?_⟩
  rw [pow_succ, hq]
  ring

private theorem exists_twoPow_sub_one_eq_eight_mul_add_seven
    {n : ℕ}
    (hn : 3 ≤ n) :
    ∃ q : ℕ, 2 ^ n - 1 = 8 * q + 7 := by
  have hThree : 3 ≤ n := by
    omega
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hThree
  have ht : 0 < 2 ^ t := Arithmetic.twoPow_pos t
  refine ⟨2 ^ t - 1, ?_⟩
  rw [pow_add]
  norm_num
  omega

private theorem exists_even_oneZeroProduct_eq_four_mul_add_three
    (j : ℕ)
    {n : ℕ}
    (hn : 3 ≤ n) :
    ∃ q : ℕ,
      3 ^ (2 * j) * (2 ^ n - 1) = 4 * q + 3 := by
  rcases exists_threePow_even_eq_eight_mul_add_one j with ⟨a, ha⟩
  rcases exists_twoPow_sub_one_eq_eight_mul_add_seven hn with ⟨b, hb⟩
  refine ⟨16 * a * b + 14 * a + 2 * b + 1, ?_⟩
  rw [ha, hb]
  ring

private theorem exists_odd_oneZeroProduct_eq_eight_mul_add_five
    (j : ℕ)
    {n : ℕ}
    (hn : 3 ≤ n) :
    ∃ q : ℕ,
      3 ^ (2 * j + 1) * (2 ^ n - 1) = 8 * q + 5 := by
  rcases exists_threePow_odd_eq_eight_mul_add_three j with ⟨a, ha⟩
  rcases exists_twoPow_sub_one_eq_eight_mul_add_seven hn with ⟨b, hb⟩
  refine ⟨8 * a * b + 7 * a + 3 * b + 2, ?_⟩
  rw [ha, hb]
  ring

/--
zero position が偶数 `2j` なら、`n≥3` の one-zero macro exit depth は exactly `1`。
-/
theorem exitDepth_eq_one_of_evenPosition
    {j n r x y : ℕ}
    (hn : 3 ≤ n)
    (h : BlockData (2 * j) r (2 ^ n - 1) x y) :
    r = 1 := by
  rcases exists_even_oneZeroProduct_eq_four_mul_add_three j hn with ⟨q, hProd⟩
  by_contra hne
  have hrTwo : 2 ≤ r := by
    have hr := h.exitDepth_pos
    omega
  obtain ⟨t, rfl⟩ :=
    Nat.exists_eq_add_of_le hrTwo
  have hOther :
      3 ^ (2 * j) * (2 ^ n - 1) =
        4 * (2 ^ t * y) + 1 := by
    calc
      3 ^ (2 * j) * (2 ^ n - 1)
          = 2 ^ (2 + t) * y + 1 := h.endEquation.symm
      _ = 4 * (2 ^ t * y) + 1 := by
        rw [pow_add]
        norm_num
        ring
  omega

/--
zero position が奇数 `2j+1` なら、`n≥3` の one-zero macro exit depth は exactly `2`。
-/
theorem exitDepth_eq_two_of_oddPosition
    {j n r x y : ℕ}
    (hn : 3 ≤ n)
    (h : BlockData (2 * j + 1) r (2 ^ n - 1) x y) :
    r = 2 := by
  rcases exists_odd_oneZeroProduct_eq_eight_mul_add_five j hn with ⟨q, hProd⟩
  by_cases hrOne : r = 1
  · subst r
    rcases h.end_odd with ⟨s, hs⟩
    have hOther :
        3 ^ (2 * j + 1) * (2 ^ n - 1) = 4 * s + 3 := by
      calc
        3 ^ (2 * j + 1) * (2 ^ n - 1)
            = 2 ^ 1 * y + 1 := h.endEquation.symm
        _ = 4 * s + 3 := by
          rw [hs]
          norm_num
          ring
    omega
  · by_cases hrTwo : r = 2
    · exact hrTwo
    · have hrThree : 3 ≤ r := by
        have hr := h.exitDepth_pos
        omega
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hrThree
      have hOther :
          3 ^ (2 * j + 1) * (2 ^ n - 1) =
            8 * (2 ^ t * y) + 1 := by
        calc
          3 ^ (2 * j + 1) * (2 ^ n - 1)
              = 2 ^ (3 + t) * y + 1 := h.endEquation.symm
          _ = 8 * (2 ^ t * y) + 1 := by
            rw [pow_add]
            norm_num
            ring
      omega

end Mersenne
end Collatz3
