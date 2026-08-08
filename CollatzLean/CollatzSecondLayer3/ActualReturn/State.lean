import CollatzLean.CollatzSecondLayer3.ActualReturn.Arithmetic
import CollatzLean.CollatzSecondLayer3.ActualReturn.FutureMinimumGeometry
import CollatzLean.CollatzSecondLayer3.ActualReturn.FirstHigh

/-!
# 標準 future-minimum actual-return state

発散側の正本局所状態を、標準 future-minimum とその first crossing だけで表す。
Special C3、negative shadow、terminal normalization はこの層の公開状態には含めない。
-/

namespace CollatzSecondLayer3

open CollatzCore

/-- 標準 future-minimum の一項と、その actual first crossing。 -/
structure StandardFutureMinimumReturnData (O : OddOrbit) where
  unbounded : O.Unbounded
  index : ℕ
  length : ℕ
  crossing : FirstCrossingAt O (O.futureMinIndex index) length

namespace StandardFutureMinimumReturnData

/-- current 標準 future-minimum の位置。 -/
noncomputable def startIndex {O : OddOrbit} (R : StandardFutureMinimumReturnData O) : ℕ :=
  O.futureMinIndex R.index

/-- 次の標準 future-minimum の位置。 -/
noncomputable def nextIndex {O : OddOrbit} (R : StandardFutureMinimumReturnData O) : ℕ :=
  O.futureMinIndex (R.index + 1)

/-- current から次 future-minimum までの位置差。 -/
noncomputable def indexGap {O : OddOrbit} (R : StandardFutureMinimumReturnData O) : ℕ :=
  consecutiveFutureMinimumIndexGap O R.index

/-- current future-minimum 値。 -/
noncomputable def startValue {O : OddOrbit} (R : StandardFutureMinimumReturnData O) : ℕ :=
  O.value R.startIndex

/-- current first-crossing endpoint 値。 -/
noncomputable def endpointValue {O : OddOrbit} (R : StandardFutureMinimumReturnData O) : ℕ :=
  O.value (R.startIndex + R.length)

/-- 次の標準 future-minimum 値。 -/
noncomputable def nextValue {O : OddOrbit} (R : StandardFutureMinimumReturnData O) : ℕ :=
  O.value R.nextIndex

/-- actual first-crossing return gap。 -/
noncomputable def returnGap {O : OddOrbit} (R : StandardFutureMinimumReturnData O) : ℕ :=
  firstCrossingReturnGap (O := O) R.startIndex R.length

/-- 隣接 future-minimum の値差。 -/
noncomputable def nextValueGap {O : OddOrbit} (R : StandardFutureMinimumReturnData O) : ℕ :=
  consecutiveFutureMinimumValueGap O R.index

/-- first-crossing 長は正。 -/
theorem length_pos
    {O : OddOrbit} (R : StandardFutureMinimumReturnData O) :
    0 < R.length :=
  R.crossing.length_pos

/-- 標準 future-minimum first crossing の return gap は少なくとも4。 -/
theorem four_le_returnGap
    {O : OddOrbit} (R : StandardFutureMinimumReturnData O) :
    4 ≤ R.returnGap := by
  simpa [returnGap, startIndex] using
    four_le_firstCrossingReturnGap_at_futureMinIndex
      O R.unbounded R.index R.length R.crossing

/-- 次 future-minimum 値差は actual return gap 以下。 -/
theorem nextValueGap_le_returnGap
    {O : OddOrbit} (R : StandardFutureMinimumReturnData O) :
    R.nextValueGap ≤ R.returnGap := by
  simpa [nextValueGap, returnGap, startIndex] using
    consecutiveFutureMinimumValueGap_le_firstCrossingReturnGap
      O R.unbounded R.index R.length R.crossing

/-- 標準 future-minimum first crossing は長さ13以上。 -/
theorem thirteen_le_length
    {O : OddOrbit} (R : StandardFutureMinimumReturnData O) :
    13 ≤ R.length := by
  simpa using
    thirteen_le_firstCrossingLength_at_futureMinIndex
      O R.unbounded R.index R.length R.crossing

end StandardFutureMinimumReturnData

/--
標準 future-minimum 上で arbitrarily long な actual first crossing を保持する tower。
`Extraction` が最終的に構成すべき正本対象。
-/
structure StandardFutureMinimumReturnTowerData (O : OddOrbit) where
  unbounded : O.Unbounded
  select : ℕ → ℕ
  select_strict : StrictMono select
  length : ℕ → ℕ
  crossing : ∀ j : ℕ,
    FirstCrossingAt O (O.futureMinIndex (select j)) (length j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < length j

namespace StandardFutureMinimumReturnTowerData

/-- tower の各項を局所 actual-return state として読む。 -/
def state
    {O : OddOrbit}
    (T : StandardFutureMinimumReturnTowerData O)
    (j : ℕ) : StandardFutureMinimumReturnData O :=
  { unbounded := T.unbounded
    index := T.select j
    length := T.length j
    crossing := T.crossing j }

end StandardFutureMinimumReturnTowerData

end CollatzSecondLayer3
