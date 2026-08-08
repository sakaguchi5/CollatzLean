import CollatzLean.CollatzSecondLayer3.ActualReturn.State

/-!
# next future-minimum が first crossing より早い枝

`r < p` は最終 obstruction として保存しない。
この場合、次 future-minimum から current crossing endpoint までに contracting prefix が生じ、
次 first-crossing 長を真に短くできる、という well-founded descent に吸収する。
-/

namespace CollatzSecondLayer3

open CollatzCore

namespace StandardFutureMinimumReturnData

/-- 次 future-minimum が current first-crossing endpoint より前に来る。 -/
def EarlyNextMinimumAt
    {O : OddOrbit} (R : StandardFutureMinimumReturnData O) : Prop :=
  R.indexGap < R.length

/-- current first crossing が次 future-minimum 以前に完了する。 -/
def NonEarlyNextMinimumAt
    {O : OddOrbit} (R : StandardFutureMinimumReturnData O) : Prop :=
  R.length ≤ R.indexGap

end StandardFutureMinimumReturnData

/--
`r < p` なら次 future-minimum からより短い first crossing を得る、という
無限降下排除の局所核心。
-/
def EarlyNextMinimumDescentPrinciple : Prop :=
  ∀ O : OddOrbit,
    ∀ R : StandardFutureMinimumReturnData O,
      R.EarlyNextMinimumAt →
        ∃ pNext : ℕ,
          FirstCrossingAt O (O.futureMinIndex (R.index + 1)) pNext ∧
            pNext < R.length

end CollatzSecondLayer3
