import CollatzLean.Collatz3.OneZeroConditional.ComplexityReduction
import CollatzLean.Collatz3.OneZeroConditional.ComplexityGrowth
import CollatzLean.Collatz3.OneZeroConditional.StableDefectGrowth
import CollatzLean.Collatz3.OneZeroConditional.Pow3RunGrowth
import CollatzLean.Collatz3.OneZeroConditional.SparseWindowGrowth
import CollatzLean.Collatz3.OneZeroConditional.BoundedDefectEscape

/-!
# Collatz3 OneZeroConditional: reduction + growth から region escape へ

従来の大きな interface

* `Pow3RunGrowth`
* `SparseWindowGrowth`

を、Collatz 側 reduction と powers-of-three 側 growth に分解して再構成する。
-/

namespace Collatz3
namespace OneZeroConditional

/-- overlap reduction と run-complexity growth から既存 `Pow3RunGrowth` が従う。 -/
theorem pow3RunGrowth_of_complexity
    (hReduction : OverlapRunComplexityReduction)
    (hGrowth : Pow3RunComplexityUnbounded) :
    Pow3RunGrowth := by
  unfold Pow3RunGrowth EventualRegionEscape
  intro B
  rcases hReduction B with ⟨C, hReduce⟩
  rcases hGrowth C with ⟨K, hGrow⟩
  refine ⟨K, ?_⟩
  intro k n y hk hRegion hExit hDefect
  exact hGrow k hk (hReduce k n y hRegion hExit hDefect)

/-- periodic reduction と period-break growth から既存 `SparseWindowGrowth` が従う。 -/
theorem sparseWindowGrowth_of_periodBreak
    (hReduction : PeriodicBreakComplexityReduction)
    (hGrowth : Pow3PeriodBreakComplexityUnbounded) :
    SparseWindowGrowth := by
  unfold SparseWindowGrowth EventualRegionEscape
  intro B
  rcases hReduction B with ⟨C, hReduce⟩
  rcases hGrowth C with ⟨K, hGrow⟩
  refine ⟨K, ?_⟩
  intro k n y hk hRegion hExit hDefect
  exact hGrow k n hk hRegion (hReduce k n y hRegion hExit hDefect)

/--
Stable 側 escape と、overlap / periodic の分解済み二経路から global bounded-defect escape を得る。
-/
theorem boundedDefectEscape_of_complexity
    (hStable : StableDefectGrowth)
    (hOverlapReduction : OverlapRunComplexityReduction)
    (hRunGrowth : Pow3RunComplexityUnbounded)
    (hPeriodicReduction : PeriodicBreakComplexityReduction)
    (hBreakGrowth : Pow3PeriodBreakComplexityUnbounded) :
    BoundedDefectEscape := by
  exact boundedDefectEscape_of_regions
    hStable
    (pow3RunGrowth_of_complexity hOverlapReduction hRunGrowth)
    (sparseWindowGrowth_of_periodBreak hPeriodicReduction hBreakGrowth)

end OneZeroConditional
end Collatz3
