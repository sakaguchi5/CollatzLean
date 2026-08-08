import CollatzLean.CollatzSecondLayer3.ActualReturn.Dichotomy

/-!
# 発散側 actual-return 正本入口

最終的な数学目標は二つだけ。

1. ExactAdjacency tower の排除
2. LateNextMinimum tower の排除

`ActualReturnDichotomyPrinciple` が閉じれば、この二局所整数枝の排除だけで
非有界 odd-only 軌道を完全排除できる。
-/

namespace CollatzSecondLayer3

open CollatzCore

/-- リファクタ後の発散側最終目標。 -/
def ActualReturnMainTarget : Prop :=
  ExactAdjacencyExclusionPrinciple ∧
    LateNextMinimumExclusionPrinciple

/--
actual-return 二分岐 reduction と二局所枝排除から、非有界 odd-only 軌道を排除する。
-/
theorem no_unbounded_odd_orbit_of_actualReturnMain
    (hReduce : ActualReturnDichotomyPrinciple)
    (hMain : ActualReturnMainTarget) :
    ¬ HasUnboundedOddOrbit := by
  rintro ⟨O, hU⟩
  rcases hReduce O hU with hExact | hLate
  · exact hMain.1 ⟨O, hExact⟩
  · exact hMain.2 ⟨O, hLate⟩

end CollatzSecondLayer3
