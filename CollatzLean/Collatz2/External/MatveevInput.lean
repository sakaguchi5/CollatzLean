import CollatzLean.Collatz2.Arithmetic.TwoThreeSmallGap

/-!
# Collatz2 External: temporary Matveev input

Collatz 本体から transcendence theory を隔離するための唯一の外部入力。

この axiom は Matveev の一般定理そのものではなく、Collatz 側が実際に必要とする
`TwoThreeSmallGapExclusion` という純粋整数論 corollary を表す。

将来 Matveev を Lean 化した後は、この axiom を theorem に置き換える。
Collatz 側の証明は変更しない。
-/

namespace Collatz2
namespace External

/--
一時的な外部整数論入力。
将来は Matveev の linear forms in logarithms と有限 remainder の検証から証明する。
-/
axiom matveev_twoThreeSmallGap : TwoThreeSmallGapExclusion

end External
end Collatz2
