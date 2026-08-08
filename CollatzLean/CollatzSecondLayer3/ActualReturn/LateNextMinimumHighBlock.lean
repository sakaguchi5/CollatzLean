import CollatzLean.CollatzSecondLayer3.ActualReturn.FirstHigh
import CollatzLean.CollatzSecondLayer3.ActualReturn.LateNextMinimum

/-!
# late-next-minimum の first-high block

D≥2 側では crossing endpoint から最初の high event まで all-one run が存在する。
その first-high block が multiplicatively contracting か expanding かを、
late branch 内部の次の二分岐として定義する。
-/

namespace CollatzSecondLayer3

open CollatzCore

namespace LateNextMinimumTowerData

/-- late tower 各項の crossing 後最初の high-event data。 -/
noncomputable def firstHigh
    {O : OddOrbit}
    (T : LateNextMinimumTowerData O)
    (j : ℕ) : FutureMinimumFirstCrossingHighEventData O :=
  firstCrossingFirstHighEventData
    O T.unbounded
    (O.futureMinimumAt_futureMinIndex (T.select j))
    (T.crossing j)

/-- all-one run と最初の high step を合わせた block が contracting。 -/
def FirstHighBlockContractingAt
    {O : OddOrbit}
    (T : LateNextMinimumTowerData O)
    (j : ℕ) : Prop :=
  let D := T.firstHigh j
  3 ^ (D.highOffset + 1) <
    2 ^ (D.highOffset + O.exponent D.highPosition)

/-- all-one run と最初の high step を合わせた block が expanding。 -/
def FirstHighBlockExpandingAt
    {O : OddOrbit}
    (T : LateNextMinimumTowerData O)
    (j : ℕ) : Prop :=
  let D := T.firstHigh j
  2 ^ (D.highOffset + O.exponent D.highPosition) <
    3 ^ (D.highOffset + 1)

end LateNextMinimumTowerData

end CollatzSecondLayer3
