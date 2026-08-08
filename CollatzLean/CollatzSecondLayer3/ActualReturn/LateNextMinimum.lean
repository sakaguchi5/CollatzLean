import CollatzLean.CollatzSecondLayer3.ActualReturn.State

/-!
# late-next-minimum obstruction

`p < r`、すなわち current first-crossing endpoint の後に次 future-minimum が来る枝。
first high event と下降 connector の整数論解析をこの枝の内部へ閉じ込める。
-/

namespace CollatzSecondLayer3

open CollatzCore

/-- `p < r` が無限に続く actual-return tower。 -/
structure LateNextMinimumTowerData (O : OddOrbit) where
  unbounded : O.Unbounded
  select : ℕ → ℕ
  select_strict : StrictMono select
  length : ℕ → ℕ
  crossing : ∀ j : ℕ,
    FirstCrossingAt O (O.futureMinIndex (select j)) (length j)
  late : ∀ j : ℕ,
    length j < consecutiveFutureMinimumIndexGap O (select j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < length j

namespace LateNextMinimumTowerData

/-- late tower の局所 state。 -/
def state
    {O : OddOrbit}
    (T : LateNextMinimumTowerData O)
    (j : ℕ) : StandardFutureMinimumReturnData O :=
  { unbounded := T.unbounded
    index := T.select j
    length := T.length j
    crossing := T.crossing j }

end LateNextMinimumTowerData

/-- 非有界軌道上の late-next-minimum obstruction。 -/
def HasLateNextMinimumTower : Prop :=
  ∃ O : OddOrbit, Nonempty (LateNextMinimumTowerData O)

/-- 最終局所整数枝2の排除原理。 -/
def LateNextMinimumExclusionPrinciple : Prop :=
  ¬ HasLateNextMinimumTower

end CollatzSecondLayer3
