import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Ring

/-!
# 2進完全分解

Collatz固有の語や軌道に依存しない、正自然数の2進完全分解を集約する。
この層では代表の選択関数を作らず、存在と一意性だけを与える。
-/

namespace Collatz
namespace TwoAdic

/-- `n = 2^d * u` かつ `u` が奇数であるという完全2進分解。 -/
def ExactFactor (n d u : ℕ) : Prop :=
  n = 2 ^ d * u ∧ Odd u

/-- 自然数が同時に奇数かつ偶数になることはない。 -/
lemma odd_even_false {n : ℕ} (ho : Odd n) (he : Even n) : False := by
  rcases ho with ⟨a, ha⟩
  rcases he with ⟨b, hb⟩
  omega

/-- 正の2冪を含む積は偶数である。 -/
lemma even_two_pow_succ_mul (r v : ℕ) : Even (2 ^ (r + 1) * v) := by
  refine ⟨2 ^ r * v, ?_⟩
  rw [pow_succ]
  ring

/-- 左の2進指数が真に小さいなら、そのodd partは偶数になる。 -/
lemma oddPart_eq_twoPow_mul_of_lt
    {a b u v : ℕ}
    (hpow : 2 ^ a * u = 2 ^ b * v)
    (hab : a < b) :
    ∃ r : ℕ, u = 2 ^ (r + 1) * v := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, b = a + (r + 1) := by
    exact ⟨b - a - 1, by omega⟩
  refine ⟨r, ?_⟩
  have hc : 2 ^ a * u = 2 ^ a * (2 ^ (r + 1) * v) := by
    calc
      2 ^ a * u = 2 ^ b * v := hpow
      _ = 2 ^ a * (2 ^ (r + 1) * v) := by
        rw [hr, pow_add]
        ring
  exact Nat.mul_left_cancel (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hc

/-- 完全2進分解の指数は一意。 -/
theorem exponent_unique
    {n a b u v : ℕ}
    (ha : ExactFactor n a u)
    (hb : ExactFactor n b v) :
    a = b := by
  have hnotAB : ¬ a < b := by
    intro hab
    obtain ⟨r, hur⟩ := oddPart_eq_twoPow_mul_of_lt
      (ha.1.symm.trans hb.1) hab
    exact odd_even_false ha.2 (by rw [hur]; exact even_two_pow_succ_mul r v)
  have hnotBA : ¬ b < a := by
    intro hba
    obtain ⟨r, hvr⟩ := oddPart_eq_twoPow_mul_of_lt
      (hb.1.symm.trans ha.1) hba
    exact odd_even_false hb.2 (by rw [hvr]; exact even_two_pow_succ_mul r u)
  omega

/-- 指数が一致する完全2進分解ではodd partも一致。 -/
theorem oddPart_unique_of_exponent_eq
    {n a b u v : ℕ}
    (ha : ExactFactor n a u)
    (hb : ExactFactor n b v)
    (hab : a = b) :
    u = v := by
  subst b
  exact Nat.mul_left_cancel
    (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
    (ha.1.symm.trans hb.1)

/-- 完全2進分解は一意。 -/
theorem unique
    {n a b u v : ℕ}
    (ha : ExactFactor n a u)
    (hb : ExactFactor n b v) :
    a = b ∧ u = v := by
  have h := exponent_unique ha hb
  exact ⟨h, oddPart_unique_of_exponent_eq ha hb h⟩

/-- 任意の正自然数は完全2進分解を持つ。 -/
theorem exists_of_pos :
    ∀ n : ℕ, 0 < n → ∃ d u : ℕ, ExactFactor n d u := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn
      obtain ⟨m, heven | hodd⟩ := n.even_or_odd'
      · have hmpos : 0 < m := by omega
        have hmlt : m < n := by omega
        obtain ⟨d, u, hfac⟩ := ih m hmlt hmpos
        refine ⟨d + 1, u, ?_, hfac.2⟩
        rw [heven, hfac.1, pow_succ]
        ring
      · exact ⟨0, n, by simp, ⟨m, hodd⟩⟩

end TwoAdic
end Collatz
