import CollatzLean.CollatzSecondLayer3.ActualReturn.State

/-!
# exact-adjacency obstruction

`r = p`、すなわち current first-crossing endpoint が次の標準 future-minimum そのものになる枝。
connector が消えるため、最終的には最も純粋な局所整数論枝になる。
-/

namespace CollatzSecondLayer3

open CollatzCore

/-- `r = p` が無限に続く actual-return tower。 -/
structure ExactAdjacencyTowerData (O : OddOrbit) where
  unbounded : O.Unbounded
  select : ℕ → ℕ
  select_strict : StrictMono select
  length : ℕ → ℕ
  crossing : ∀ j : ℕ,
    FirstCrossingAt O (O.futureMinIndex (select j)) (length j)
  exact : ∀ j : ℕ,
    length j = consecutiveFutureMinimumIndexGap O (select j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < length j

namespace ExactAdjacencyTowerData

/-- exact-adjacency tower の局所 state。 -/
def state
    {O : OddOrbit}
    (T : ExactAdjacencyTowerData O)
    (j : ℕ) : StandardFutureMinimumReturnData O :=
  { unbounded := T.unbounded
    index := T.select j
    length := T.length j
    crossing := T.crossing j }

end ExactAdjacencyTowerData

/-- 非有界軌道上の exact-adjacency obstruction。 -/
def HasExactAdjacencyTower : Prop :=
  ∃ O : OddOrbit, Nonempty (ExactAdjacencyTowerData O)

/-- 最終局所整数枝1の排除原理。 -/
def ExactAdjacencyExclusionPrinciple : Prop :=
  ¬ HasExactAdjacencyTower

end CollatzSecondLayer3
