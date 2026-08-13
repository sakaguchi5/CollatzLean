import CollatzLean.Collatz2.Orbit.FutureMinimum
import Mathlib.Tactic.Linarith

/-!
# Collatz2: elementary arithmetic at future minima

future minimum の直後の normalized step だけから得られる算術を分離する。
Matrix / center / replay には依存しない。

future minimum value `x > 1` では first exponent は必ず `1`。
さらに normalized successor が odd なので `x = 4k+3`。
従って十分後ろの adjacent future-minimum value gap は正の4倍数になる。
-/

namespace Collatz2
namespace OddOrbit

/--
`x > 1` の future minimum の直後では normalized exponent は `1`。
`e ≥ 2` なら successor が start より小さくなり future-minimum 性に反する。
-/
theorem FutureMinimumAt.exponent_eq_one_of_one_lt_value
    {O : OddOrbit} {n : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hx : 1 < O.value n) :
    O.exponent n = 1 := by
  have hepos : 0 < O.exponent n := O.exponent_pos n
  by_contra hne
  have he2 : 2 ≤ O.exponent n := by omega
  obtain ⟨k, hk⟩ : ∃ k : ℕ, O.exponent n = k + 2 := by
    exact ⟨O.exponent n - 2, by omega⟩
  have hstep := O.step n
  have hpow : 4 ≤ 2 ^ O.exponent n := by
    rw [hk, pow_add]
    simp only [pow_two]
    have hkpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
    nlinarith
  have hfour :
      4 * O.value (n + 1) ≤ 3 * O.value n + 1 := by
    calc
      4 * O.value (n + 1)
          ≤ 2 ^ O.exponent n * O.value (n + 1) :=
            Nat.mul_le_mul_right _ hpow
      _ = 3 * O.value n + 1 := hstep
  have hminNext : O.value n ≤ O.value (n + 1) :=
    hmin (n + 1) (by omega)
  omega

/--
`x > 1` の future minimum は `3 mod 4`。
除算 exponent `1` と start/end の oddness だけで出る。
-/
theorem FutureMinimumAt.value_eq_four_mul_add_three
    {O : OddOrbit} {n : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hx : 1 < O.value n) :
    ∃ k : ℕ, O.value n = 4 * k + 3 := by
  have he : O.exponent n = 1 :=
    hmin.exponent_eq_one_of_one_lt_value hx
  obtain ⟨a, ha⟩ := O.value_odd (n + 1)
  obtain ⟨b, hb⟩ := O.value_odd n
  have hstep := O.step n
  rw [he, ha, hb] at hstep
  obtain ⟨k, hEven | hOdd⟩ := b.even_or_odd'
  · rw [hEven] at hstep
    omega
  · refine ⟨k, ?_⟩
    rw [hb, hOdd]
    omega

namespace FutureMinima

/-- selected adjacent future-minimum values の差。 -/
def valueGap
    {O : OddOrbit}
    (S : O.FutureMinima)
    (n : ℕ) : ℕ :=
  O.value (S.index (n + 1)) - O.value (S.index n)

/-- adjacent future-minimum gap は常に正。 -/
theorem valueGap_pos
    {O : OddOrbit}
    (S : O.FutureMinima)
    (n : ℕ) :
    0 < S.valueGap n := by
  unfold valueGap
  exact Nat.sub_pos_of_lt (S.value_strict (Nat.lt_succ_self n))

/--
start future minimum が `> 1` なら、adjacent gap は正の4倍数。
両 endpoint が `3 mod 4` であることの差にすぎない。
-/
theorem valueGap_eq_four_mul
    {O : OddOrbit}
    (S : O.FutureMinima)
    {n : ℕ}
    (hstart : 1 < O.value (S.index n)) :
    ∃ q : ℕ, 0 < q ∧ S.valueGap n = 4 * q := by
  have hend :
      1 < O.value (S.index (n + 1)) :=
    lt_trans hstart (S.value_strict (Nat.lt_succ_self n))
  obtain ⟨a, ha⟩ :=
    (S.minimum n).value_eq_four_mul_add_three hstart
  obtain ⟨b, hb⟩ :=
    (S.minimum (n + 1)).value_eq_four_mul_add_three hend
  have hab : a < b := by
    have hval :
        O.value (S.index n) <
          O.value (S.index (n + 1)) := by
      simpa [Nat.succ_eq_add_one] using
        S.value_strict (Nat.lt_succ_self n)
    rw [ha, hb] at hval
    omega
  refine ⟨b - a, Nat.sub_pos_of_lt hab, ?_⟩
  unfold valueGap
  rw [ha, hb]
  omega

/--
selected future minima は最終的に `> 1` なので、
adjacent gap は tail 全体で正の4倍数になる。
-/
theorem eventually_valueGap_eq_four_mul
    {O : OddOrbit}
    (S : O.FutureMinima) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ q : ℕ, 0 < q ∧ S.valueGap n = 4 * q := by
  obtain ⟨N, hN⟩ := S.values_eventually_large 1
  refine ⟨N, ?_⟩
  intro n hn
  exact S.valueGap_eq_four_mul (hN n hn)

end FutureMinima
end OddOrbit
end Collatz2
