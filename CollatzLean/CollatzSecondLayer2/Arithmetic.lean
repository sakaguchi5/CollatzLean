import Mathlib.Data.Nat.Factorization.Defs

/-!
# 第二層で使う初等的指数優越入力

固定多項式が最終的に2冪より小さくなることを、API依存から分離した命題として置く。
旧SecondLayerはimportしない。
-/

namespace CollatzSecondLayer2

/-- 固定多項式は最終的に`2^(p+1)`より小さい。 -/
def PolynomialBelowTwoPower : Prop :=
  ∀ K A : ℕ,
    ∃ N : ℕ,
      ∀ p : ℕ, N ≤ p →
        K * (p + 1) ^ A < 2 ^ (p + 1)

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
    (hPow : PolynomialBelowTwoPower)
    (K A : ℕ) :
    ∃ N : ℕ, ∀ q : ℕ, N ≤ q →
      K * (q + 1) ^ A < 2 * 3 ^ q := by
  obtain ⟨N, hN⟩ := hPow K A
  refine ⟨N, ?_⟩
  intro q hq
  exact lt_of_lt_of_le (hN q hq) (twoPow_succ_le_two_mul_threePow q)

end CollatzSecondLayer2
