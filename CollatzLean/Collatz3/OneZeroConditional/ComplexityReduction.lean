import CollatzLean.Collatz3.OneZeroConditional.Basic
import CollatzLean.Collatz3.Binary.Complexity

/-!
# Collatz3 OneZeroConditional: bounded defect から power-of-three complexity への reduction interface

Collatz / Mersenne 側の組合せ還元と、外部の powers-of-three growth theorem を分離する。

ここでは reduction 自体を axiom にせず、後から theorem で埋めるための `Prop` interface に名前を与える。
-/

namespace Collatz3
namespace OneZeroConditional

/--
overlap region で target defect が `B` 以下なら、`3^k` の binary run 数が
`B` のみに依存する上限へ押し込まれる、という reduction interface。
-/
def OverlapRunComplexityReduction : Prop :=
  ∀ B : ℕ,
    ∃ C : ℕ,
      ∀ k n y : ℕ,
        Mersenne.InOverlapRegion k n →
        Mersenne.OneZeroExit k n y →
        Binary.HasZeroDefectAtMost y B →
        Binary.HasRunComplexityAtMost (3 ^ k) C

/--
periodic region で target defect が `B` 以下なら、period `n` に対する `3^k` の
binary period-break 数が `B` のみに依存する上限へ押し込まれる reduction interface。
-/
def PeriodicBreakComplexityReduction : Prop :=
  ∀ B : ℕ,
    ∃ C : ℕ,
      ∀ k n y : ℕ,
        Mersenne.InPeriodicRegion k n →
        Mersenne.OneZeroExit k n y →
        Binary.HasZeroDefectAtMost y B →
        Binary.HasPeriodBreakAtMost (3 ^ k) n C

end OneZeroConditional
end Collatz3
