import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Ring

/-!
# 指数優越の初等・漸近算術
-/

namespace Collatz
namespace Arithmetic

open Filter Asymptotics

/-- 固定多項式は最終的に`2^(p+1)`より小さい。 -/
def PolynomialBelowTwoPower : Prop :=
  ∀ K A : ℕ, ∃ N : ℕ, ∀ p : ℕ, N ≤ p →
    K * (p + 1) ^ A < 2 ^ (p + 1)

/-- 固定多項式は`2^(p+1)`より遅く成長する。 -/
theorem polynomialBelowTwoPower : PolynomialBelowTwoPower := by
  intro K A
  have hLittle :
      (fun n : ℕ => (n : ℝ) ^ A) =o[atTop]
        (fun n : ℕ => (2 : ℝ) ^ n) :=
    isLittleO_pow_const_const_pow_of_one_lt A (by norm_num)
  have hCoefficient : 0 < ((((K + 1 : ℕ) : ℝ))⁻¹) := by positivity
  have hEventually :
      ∀ᶠ n : ℕ in atTop,
        ‖(n : ℝ) ^ A‖ ≤ ((((K + 1 : ℕ) : ℝ))⁻¹) * ‖(2 : ℝ) ^ n‖ :=
    hLittle.def hCoefficient
  obtain ⟨N, hN⟩ := eventually_atTop.1 hEventually
  refine ⟨N, ?_⟩
  intro p hp
  have hnorm := hN (p + 1) (by omega)
  have hpNonneg : 0 ≤ ((p + 1 : ℕ) : ℝ) := by positivity
  have htwoNonneg : 0 ≤ (2 : ℝ) := by norm_num
  simp only [Real.norm_eq_abs, abs_pow, abs_of_nonneg hpNonneg,
    abs_of_nonneg htwoNonneg] at hnorm
  have hscale :
      (((K + 1 : ℕ) : ℝ) * (((p + 1 : ℕ) : ℝ) ^ A)) ≤
        (2 : ℝ) ^ (p + 1) := by
    calc
      (((K + 1 : ℕ) : ℝ) * (((p + 1 : ℕ) : ℝ) ^ A))
          ≤ ((K + 1 : ℕ) : ℝ) *
            (((((K + 1 : ℕ) : ℝ))⁻¹) * (2 : ℝ) ^ (p + 1)) := by
              exact mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = (2 : ℝ) ^ (p + 1) := by
            have hne : ((K + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  have hfactorPos : 0 < (((p + 1 : ℕ) : ℝ) ^ A) := by positivity
  have hKlt : (K : ℝ) < ((K + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_succ_self K
  have hstrict :
      (K : ℝ) * (((p + 1 : ℕ) : ℝ) ^ A) <
        ((K + 1 : ℕ) : ℝ) * (((p + 1 : ℕ) : ℝ) ^ A) := by
    exact _root_.mul_lt_mul_of_pos_right hKlt hfactorPos
  have hreal :
      (K : ℝ) * (((p + 1 : ℕ) : ℝ) ^ A) < (2 : ℝ) ^ (p + 1) :=
    lt_of_lt_of_le hstrict hscale
  exact_mod_cast hreal

/-- `2^q ≤ 3^q`。 -/
theorem twoPow_le_threePow (q : ℕ) : 2 ^ q ≤ 3 ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul ih (by omega)

/-- `2^(q+1) ≤ 2*3^q`。 -/
theorem twoPow_succ_le_two_mul_threePow (q : ℕ) :
    2 ^ (q + 1) ≤ 2 * 3 ^ q := by
  rw [pow_succ]
  have h := Nat.mul_le_mul_left 2 (twoPow_le_threePow q)
  simpa [Nat.mul_comm] using h

/-- 固定多項式は最終的に`2*3^q`より小さい。 -/
theorem polynomialBelowTwoMulThreePower
    (K A : ℕ) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q → K * (q + 1) ^ A < 2 * 3 ^ q := by
  obtain ⟨N, hN⟩ := polynomialBelowTwoPower K A
  refine ⟨N, ?_⟩
  intro q hq
  exact lt_of_lt_of_le (hN q hq) (twoPow_succ_le_two_mul_threePow q)

end Arithmetic
end Collatz
