import CollatzLean.Collatz3.Binary.Complexity

/-!
# Collatz3 External: powers of three の period-1 break escape

Ralf Stephan, *Aperiodicity and subword complexity in the binary expansion of powers of three*
(arXiv:2607.14774, 2026) の period `p=1` 部分から、この repository が実際に使う
最小の帰結だけを cited input として切り出す。

ここで仮定するのは Collatz equation ではなく、純粋に `3^k` の canonical binary word の
period-1 break 数が固定値以下なら指数 `k` が一様有界、という事実だけである。

Stephan の公開 Lean 形式化では、この結論は Baker--Wüstholz [BW93] の三対数評価から
導かれている。今の repository では、その大きな digit-block development 全体を import
しないため、この一様有界性だけを trusted theorem として隔離する。

将来 `External/BakerWustholz.lean` から Stephan の p=1 proof engine を直接再構成した時点で、
この axiom は derived theorem に置き換えられる。
-/

namespace Collatz3
namespace External
namespace StephanTransitions

/--
`3^k` の period-1 break 数が固定値 `B` 以下なら、`k` は `B` のみに依存して一様有界。

`Binary.HasPeriodBreakAtMost` は canonical bit length を同時に要求するため、leading zero を
追加して break 数を人工的に小さくすることはできない。

この theorem は Collatz 固有の branch、hole、Mersenne equation を一切仮定しない。
-/
axiom threePow_periodOne_bounded :
    ∀ B : ℕ,
      ∃ K : ℕ,
        ∀ {k : ℕ},
          2 ≤ k →
          Binary.HasPeriodBreakAtMost (3 ^ k) 1 B →
          k < K

/-- `B` に対する cited theorem の bound witness を固定する。 -/
noncomputable def periodOneDepthBound (B : ℕ) : ℕ :=
  Classical.choose (threePow_periodOne_bounded B)

/-- 固定した witness が実際に period-1 bounded-depth theorem を満たす。 -/
theorem periodOneDepthBound_spec
    (B : ℕ)
    {k : ℕ}
    (hk2 : 2 ≤ k)
    (hBreak : Binary.HasPeriodBreakAtMost (3 ^ k) 1 B) :
    k < periodOneDepthBound B := by
  exact (Classical.choose_spec (threePow_periodOne_bounded B)) hk2 hBreak

end StephanTransitions
end External
end Collatz3
