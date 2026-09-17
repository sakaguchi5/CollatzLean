import CollatzLean.Collatz3.OneZeroConditional.Basic
import CollatzLean.Collatz3.Binary.Complexity

/-!
# Collatz3 OneZeroConditional: powers of three の complexity growth interface

Stephan / Baker 型の外部入力を、Collatz の語彙から切り離した最小 `Prop` として保存する。

これらは axiom ではない。後で対応する数論定理を Lean で証明したとき、
この `Prop` の theorem を与えればよい。
-/

namespace Collatz3
namespace OneZeroConditional

/-- `3^k` の canonical binary run complexity は任意固定上限を最終的に越える。 -/
def Pow3RunComplexityUnbounded : Prop :=
  ∀ C : ℕ,
    ∃ K : ℕ,
      ∀ k : ℕ,
        K ≤ k →
        ¬ Binary.HasRunComplexityAtMost (3 ^ k) C

/--
periodic region で許される period `n` に対し、`3^k` の period-break complexity は
任意固定上限を最終的に越える。
-/
def Pow3PeriodBreakComplexityUnbounded : Prop :=
  ∀ C : ℕ,
    ∃ K : ℕ,
      ∀ k n : ℕ,
        K ≤ k →
        Mersenne.InPeriodicRegion k n →
        ¬ Binary.HasPeriodBreakAtMost (3 ^ k) n C

end OneZeroConditional
end Collatz3
