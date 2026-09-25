import CollatzLean.Collatz3.External.BakerWustholzFourRat
import CollatzLean.Collatz3.Binary.Complexity
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Stephan variable-period aperiodicity の純粋算術 interface

A2 target-large では内部算術だけで

* period `p=n`,
* break 数 `≤5`,
* `p ≤ 3 + v₂(k)` または `p ≤ 3 + v₂(k-1)`

まで落ちる。

従来、この先の analytic escape を `Mersenne.BlockComplexity` 内の
`StephanValuationWidthPeriodBreakEscape` という project-local interface に置いていた。

ここでは同じ内容を `3^k` の二進展開だけについて述べる純粋数論 theorem として
External 層へ移す。Stephan の fixed/variable window proof の核は四対数 gap principle で、
その trusted input は `BakerWustholzFourRat` に分離した。

この axiom は Collatz equation や target-two branch を一切仮定しない。
将来 Stephan の `gap_principle → window_break → pigeonhole` を直接移植した時点で
derived theorem に置き換える。
-/

namespace Collatz3
namespace External
namespace StephanVariablePeriod

/--
period が `v₂(k)` / `v₂(k-1)` の logarithmic width 以下で、
period-break 数が固定値 `B` 以下なら exponent `k` は一様有界。
-/
def ValuationWidthPeriodBreakEscape : Prop :=
  ∀ B : ℕ,
    ∃ K : ℕ,
      ∀ {k p : ℕ},
        2 ≤ k →
        (p ≤ 3 + padicValNat 2 k ∨
          p ≤ 3 + padicValNat 2 (k - 1)) →
        Binary.HasPeriodBreakAtMost (3 ^ k) p B →
        k < K

/--
Stephan/Baker--Wüstholz 側の純粋数論 corollary。

A2 固有の branch assumption ではなく、`3^k` の二進展開だけの statement。
-/
axiom valuationWidthPeriodBreakEscape :
    ValuationWidthPeriodBreakEscape

end StephanVariablePeriod
end External
end Collatz3
