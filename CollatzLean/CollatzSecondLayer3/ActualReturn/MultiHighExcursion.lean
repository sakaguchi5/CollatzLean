import CollatzLean.CollatzSecondLayer3.ActualReturn.LateNextMinimumHighBlock

/-!
# multi-high expanding excursion

late-next-minimum のうち、first-high block でも crossing endpoint 以下へ戻らない最終難所。
今後は「最初に crossing endpoint 以下へ戻す critical high block」を正規化して解析する。
-/

namespace CollatzSecondLayer3

open CollatzCore

/-- first-high block が expanding のまま残る late tower。 -/
structure MultiHighExcursionTowerData (O : OddOrbit) where
  source : LateNextMinimumTowerData O
  firstHighExpanding : ∀ j : ℕ,
    source.FirstHighBlockExpandingAt j

/-- multi-high excursion obstruction の存在。 -/
def HasMultiHighExcursionTower : Prop :=
  ∃ O : OddOrbit, Nonempty (MultiHighExcursionTowerData O)

/-- multi-high excursion 最終枝の排除目標。 -/
def MultiHighExcursionExclusionPrinciple : Prop :=
  ¬ HasMultiHighExcursionTower

end CollatzSecondLayer3
