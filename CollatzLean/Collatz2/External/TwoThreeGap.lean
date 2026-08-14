import CollatzLean.Collatz2.Arithmetic.TwoThreeSmallGap

/-!
# Collatz2 External: 2-3 polynomial gap interface

旧系で使っていた Baker / Matveev 型の相対 gap 入力を
Collatz2 側へ薄い純整数論 interface として再導入する。

Collatz word や orbit には依存しない。

  3^p < 2^H

なら

  3^p <= K * (p+1)^A * (2^H - 3^p)

という polynomial-relative lower bound を仮定する。

このファイルは Prop interface のみで、外部仮定定数は置かない。
-/

namespace Collatz2
namespace External

/--
2 と 3 の冪差に対する Baker / Matveev 型 polynomial-relative gap。
-/
def TwoThreeGapPolynomialBound : Prop :=
  ∃ K A : ℕ,
    0 < K ∧
    ∀ p H : ℕ,
      0 < p →
      3 ^ p < 2 ^ H →
      3 ^ p ≤
        K * (p + 1) ^ A * (2 ^ H - 3 ^ p)

end External
end Collatz2
