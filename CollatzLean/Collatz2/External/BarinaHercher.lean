import CollatzLean.Collatz2.Orbit.OddOrbit
import CollatzLean.Collatz2.Arithmetic.HercherContinuedFractionCertificate

/-!
# Collatz2 External: Barina 2^71 + Hercher denominator certificate

このファイルは計算機検証 / continued fraction を Collatz 本体から隔離する。

1. Barina (Journal of Supercomputing 81, 810, 2025) は Collatz convergence を
   `2^71` まで検証した。
   unbounded normalized odd-only orbit に対する corollary として

     2^71 < O.value i

   を external interface にする。

2. Hercher Lemma 22 型の continued-fraction denominator certificate。
   finite Hercher narrow inequality

     3*(2^H-3^K)*2^71 < K*3^K

   は

     log(3)/log(2) < H/K

   の幅を `1/(3*2^71*log 2)` 未満にする。
   この open interval で最小分母を持つ fraction は

     114208327604 / 72057431991

   なので `K >= 72057431991`。

continued fraction / transcendental real-number verification はこの外部 certificate にのみ隔離する。
-/

namespace Collatz2
namespace External

/-- Barina `2^71` verification の unbounded odd-orbit corollary。 -/
structure BarinaTwoPow71Input : Prop where
  unbounded_odd_orbit_above :
    ∀ (O : OddOrbit),
      O.Unbounded →
      ∀ i : ℕ,
        2 ^ 71 < O.value i

/--
Hercher Lemma 22 の `2^71` interval 用 denominator certificate。
純整数の division-free premise で downstream へ渡す。
-/
structure HercherTwoPow71DenominatorInput : Prop where
  denominator_bound :
    ∀ K H : ℕ,
      0 < K →
      3 ^ K < 2 ^ H →
      3 * (2 ^ H - 3 ^ K) * 2 ^ 71 <
        K * 3 ^ K →
      Arithmetic.cfDenominator
          Arithmetic.hercherTwoPow71BoundaryCF ≤ K

/-- 2025 Barina computation を外部入力として使用する。 -/
axiom barinaTwoPow71 : BarinaTwoPow71Input

/--
continued fraction certificate。
境界 fraction は `114208327604 / 72057431991`。
-/
axiom hercherTwoPow71Denominator :
  HercherTwoPow71DenominatorInput

end External
end Collatz2
