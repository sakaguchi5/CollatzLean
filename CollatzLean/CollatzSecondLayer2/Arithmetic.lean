import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Tactic.Ring

/-!
# 第二層で使う初等的指数優越入力

固定多項式の指数優越と、2と3の相対gapに対するBaker型入力を
旧`CollatzSecondLayer`から独立に定義する。
-/

namespace CollatzSecondLayer2

/-- 固定多項式は最終的に`2^(p+1)`より小さい。 -/
def PolynomialBelowTwoPower : Prop :=
  ∀ K A : ℕ,
    ∃ N : ℕ,
      ∀ p : ℕ, N ≤ p →
        K * (p + 1) ^ A < 2 ^ (p + 1)

/--
`2^H-3^p`が`3^p`に対して逆多項式以上であるという、
2と3専用のBaker型入力。
-/
def TwoThreeGapPolynomialBound : Prop :=
  ∃ K A : ℕ,
    0 < K ∧
    ∀ p H : ℕ,
      0 < p →
      3 ^ p < 2 ^ H →
      3 ^ p ≤ K * (p + 1) ^ A * (2 ^ H - 3 ^ p)

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

/-- `p`を一次数へ吸収する初等評価。 -/
theorem length_mul_gap_polynomial_le
    (p K A g : ℕ) :
    p * (K * (p + 1) ^ A * g) ≤
      g * (K * (p + 1) ^ (A + 1)) := by
  have hp : p ≤ p + 1 := by omega
  calc
    p * (K * (p + 1) ^ A * g)
        = g * (p * (K * (p + 1) ^ A)) := by ring
    _ ≤ g * ((p + 1) * (K * (p + 1) ^ A)) := by
      exact Nat.mul_le_mul_left g
        (Nat.mul_le_mul_right (K * (p + 1) ^ A) hp)
    _ = g * (K * (p + 1) ^ (A + 1)) := by
      rw [pow_succ]
      ring

/-- gap付き開始値評価から多項式開始値評価を得る。 -/
theorem start_le_polynomial_of_gap_bound
    {p g X K A : ℕ}
    (hg : 0 < g)
    (hGX : g * X ≤ p * 3 ^ p)
    (hthree : 3 ^ p ≤ K * (p + 1) ^ A * g) :
    X ≤ K * (p + 1) ^ (A + 1) := by
  have hchain :
      g * X ≤ g * (K * (p + 1) ^ (A + 1)) := by
    calc
      g * X ≤ p * 3 ^ p := hGX
      _ ≤ p * (K * (p + 1) ^ A * g) :=
        Nat.mul_le_mul_left p hthree
      _ ≤ g * (K * (p + 1) ^ (A + 1)) :=
        length_mul_gap_polynomial_le p K A g
  exact Nat.le_of_mul_le_mul_left hchain hg

end CollatzSecondLayer2
