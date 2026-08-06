import CollatzLean.CollatzSupport.Arithmetic

/-!
# 2と3のgapに対する外部算術入力

Lean内で証明済みの指数優越とは分離し、Baker型入力だけを公開する。
-/

namespace CollatzExternal

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

end CollatzExternal
