import CollatzLean.CollatzSecondLayer3.ActualReturn.Valuation
import CollatzLean.CollatzSecondLayer3.ActualReturn.LateNextMinimum

/-!
# late-next-minimum の return-depth 1 refinement

`D = 1` では first high offset が0になり、crossing endpoint 自身が first high event になる。
この枝の線形 smallness と high exponent 制約を今後ここへ集約する。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer

/-- late tower の全項で actual return gap の exact 2進 depth が1。 -/
structure LateNextMinimumD1TowerData (O : OddOrbit) where
  source : LateNextMinimumTowerData O
  depthOne : ∀ j : ℕ,
    ∃ u : ℕ,
      ExactTwoFactor
        (firstCrossingReturnGap
          (O := O)
          (O.futureMinIndex (source.select j))
          (source.length j))
        1 u

/-- D=1 late branch の排除目標。 -/
def LateNextMinimumD1ExclusionPrinciple : Prop :=
  ¬ ∃ O : OddOrbit, Nonempty (LateNextMinimumD1TowerData O)

end CollatzSecondLayer3
