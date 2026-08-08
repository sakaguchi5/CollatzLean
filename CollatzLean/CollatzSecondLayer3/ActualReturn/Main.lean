import CollatzLean.CollatzSecondLayer3.ActualReturn.Dichotomy

/-!
# 発散側 actual-return 正本入口

最終的な数学目標は二つだけ。

1. Adjacent Expanding Return tower の排除
2. Adjacent Contracting Return tower の排除

first crossing・meander・Special C3・terminal normalization は最終 reduction の
公開分岐には現れない。標準 future-minimum の隣接区間の determinant 符号だけで
無条件に二分岐する。
-/

namespace CollatzSecondLayer3

open CollatzCore

/-- リファクタ後の発散側最終目標。 -/
def ActualReturnMainTarget : Prop :=
  AdjacentExpandingReturnExclusionPrinciple ∧
    AdjacentContractingReturnExclusionPrinciple

/--
二つの隣接-return局所整数枝を排除すれば、非有界 odd-only 軌道は存在しない。
reduction theorem は Lean 内で無条件に証明済みなので追加仮定を取らない。
-/
theorem no_unbounded_odd_orbit_of_actualReturnMain
    (hMain : ActualReturnMainTarget) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_odd_orbit_adjacentReturn_dichotomy hU with hExp | hCon
  · exact hMain.1 hExp
  · exact hMain.2 hCon

end CollatzSecondLayer3
