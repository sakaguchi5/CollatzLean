import Mathlib.Data.Nat.Factorization.Defs

/-!
# Collatz2 Arithmetic: 2^H と 3^p の small-gap exclusion interface

Collatz 側が必要とする外部整数論入力を、軌道・word・replay から完全に分離する。

必要なのは一般の Matveev 定理そのものではなく、その後で導く次の exact obstruction だけである。

  G > 0
  2^H = 3^p + G
  6*G + 6 < p

を同時に満たす自然数 H,p,G は存在しない。

このファイルでは命題の interface だけを定義し、外部入力は置かない。
-/

namespace Collatz2

/--
2 と 3 の冪の正の差は、odd-step exponent `p` に対して
`6*G+6 < p` となるほど小さくはならない、という純粋整数論 interface。

将来は Matveev の linear forms in logarithms と有限 remainder の certified check から
この命題を Lean 内で証明する。
-/
def TwoThreeSmallGapExclusion : Prop :=
  ∀ H p G : ℕ,
    0 < G →
    2 ^ H = 3 ^ p + G →
    6 * G + 6 < p →
    False

end Collatz2
