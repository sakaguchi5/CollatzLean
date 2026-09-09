import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith


/-!
# Collatz3 Experimental2: slope window の純粋実数算術

このファイルでは unit-carry を仮定しない。

整数値関数 `β` と実数 `σ` が

`β(n) ≤ nσ ≤ β(n)+1`

という幅一の window を全正整数で満たすときに従う純粋算術を扱う。
-/

namespace Collatz3
namespace Experimental2

def IsRoofSlope
    (β : ℕ → ℕ)
    (σ : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    (β n : ℝ) ≤ (n : ℝ) * σ ∧
      (n : ℝ) * σ ≤ (β n : ℝ) + 1

def HasNoIntegralMultiple (σ : ℝ) : Prop :=
  ∀ n k : ℕ, 0 < n →
    (n : ℝ) * σ ≠ (k : ℝ)

def IsNatFloor
    (k : ℕ)
    (x : ℝ) : Prop :=
  (k : ℝ) ≤ x ∧ x < (k : ℝ) + 1

def IsNatUpperCell
    (k : ℕ)
    (x : ℝ) : Prop :=
  (k : ℝ) < x ∧ x ≤ (k : ℝ) + 1

/-- 二つの slope は各正幅 `n` で互いに `1/n` 以内。 -/
theorem roofSlope_distance_le_inv
    {β : ℕ → ℕ}
    {σ τ : ℝ}
    (Sσ : IsRoofSlope β σ)
    (Sτ : IsRoofSlope β τ)
    {n : ℕ}
    (hn : 0 < n) :
    σ ≤ τ + 1 / (n : ℝ) ∧
      τ ≤ σ + 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hσ := Sσ n hn
  have hτ := Sτ n hn
  have hST : σ - τ ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hnR).2
    nlinarith [hσ.2, hτ.1]
  have hTS : τ - σ ≤ 1 / (n : ℝ) := by
    apply (le_div_iff₀ hnR).2
    nlinarith [hτ.2, hσ.1]
  constructor <;> linarith

/-- 全 `n` で相互距離が `1/n` 以下なら二実数は一致する。 -/
theorem eq_of_mutual_le_add_inv_nat
    {σ τ : ℝ}
    (H : ∀ n : ℕ, 0 < n →
      σ ≤ τ + 1 / (n : ℝ) ∧
        τ ≤ σ + 1 / (n : ℝ)) :
    σ = τ := by
  apply le_antisymm
  · by_contra hNot
    have hgap : 0 < σ - τ := sub_pos.mpr (lt_of_not_ge hNot)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hgap
    let n := k + 1
    have hn : 0 < n := by dsimp [n]; omega
    have hClose := (H n hn).1
    have hk' : 1 / (n : ℝ) < σ - τ := by simpa [n] using hk
    linarith
  · by_contra hNot
    have hgap : 0 < τ - σ := sub_pos.mpr (lt_of_not_ge hNot)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hgap
    let n := k + 1
    have hn : 0 < n := by dsimp [n]; omega
    have hClose := (H n hn).2
    have hk' : 1 / (n : ℝ) < τ - σ := by simpa [n] using hk
    linarith

/-- slope window を満たす slope は一意。 -/
theorem roofSlope_unique
    {β : ℕ → ℕ}
    {σ τ : ℝ}
    (Sσ : IsRoofSlope β σ)
    (Sτ : IsRoofSlope β τ) :
    σ = τ := by
  apply eq_of_mutual_le_add_inv_nat
  intro n hn
  exact roofSlope_distance_le_inv Sσ Sτ hn

/-- integer boundary が無いなら lower floor cell に入る。 -/
theorem isNatFloor_of_roofSlope_noIntegralMultiple
    {β : ℕ → ℕ}
    {σ : ℝ}
    (S : IsRoofSlope β σ)
    (H : HasNoIntegralMultiple σ)
    {n : ℕ}
    (hn : 0 < n) :
    IsNatFloor (β n) ((n : ℝ) * σ) := by
  have h := S n hn
  refine ⟨h.1, ?_⟩
  rcases lt_or_eq_of_le h.2 with hLt | hEq
  · exact hLt
  · exfalso
    apply H n (β n + 1) hn
    norm_num at hEq ⊢
    exact hEq

/-- irrational slope なら正整数倍は自然数境界に乗らない。 -/
theorem irrational_hasNoIntegralMultiple
    {σ : ℝ}
    (hIrr : Irrational σ) :
    HasNoIntegralMultiple σ := by
  intro n k hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hMul : Irrational ((n : ℝ) * σ) := by
    simpa [mul_comm] using hIrr.mul_natCast hn0
  exact hMul.ne_nat k

end Experimental2
end Collatz3
