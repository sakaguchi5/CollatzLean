import CollatzLean.Collatz.Arithmetic.Growth

/-!
# 2と3のgapに対する外部算術入力
-/

namespace Collatz
namespace External

/-- `2^H-3^p`に対する2と3専用のBaker型入力。 -/
def TwoThreeGapPolynomialBound : Prop :=
  ∃ K A : ℕ,
    0 < K ∧
    ∀ p H : ℕ,
      0 < p →
      3 ^ p < 2 ^ H →
      3 ^ p ≤ K * (p + 1) ^ A * (2 ^ H - 3 ^ p)

end External
end Collatz
