import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ColumnLayerFareyBridge

/-!
# Critical-boundary chain -> column/layer Farey data

`ColumnLayerFareyBridge` は一つの Ferrers step に対して、lower の current extra depth `j`
から actual cell data を復元する。

ここでは critical Sturmian boundary 起点の chain に適用する。
`FerrersColumnOccupancy` により lower の extra depth はその column の current occupancy
そのものなので、chain prefix と次の selected rank cut だけから

  j = rankColumnOccupancy(prefix, k)

が決まり、その step の

  D,
  cost quotient,
  residual cost,
  residual lambda

は endpoint `(H,m)` と `(k,j)` だけで canonical に決まる。
-/

namespace Collatz2
namespace CSTMicro

namespace FerrersChain

/--
critical boundary 起点の chain prefix に続く一 step では、selected lower depth は
その rank column の current occupancy に一致する。
-/
theorem criticalBoundary_selected_lower_extraDepth_eq_occupancy
    {v lower upper : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) lower)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    (S : FerrersStep lower upper)
    (hkLt :
      S.edge.rankCut <
        Collatz2.Word.oddSteps
          (exponentWordOfParity (criticalBoundaryWord v.length))) :
    parityExtraDepth lower S.edge.rankCut =
      C.rankColumnOccupancy S.edge.rankCut := by
  exact
    criticalBoundary_to_finish_extraDepth_eq_columnOccupancy
      hFP hLen C hkLt

/--
critical boundary 起点の次セル Farey residue は、現在の column occupancy を layer として
canonical cell weight に一致する。
-/
theorem criticalBoundary_next_fareyResidue_eq_columnLayer
    {v lower upper : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) lower)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    (S : FerrersStep lower upper)
    (hkLt :
      S.edge.rankCut <
        Collatz2.Word.oddSteps
          (exponentWordOfParity (criticalBoundaryWord v.length))) :
    S.edge.toFareyCellPacket.residue =
      columnLayerFareyResidue
        S.edge.length
        S.edge.oddTotal
        S.edge.rankCut
        (C.rankColumnOccupancy S.edge.rankCut) := by
  have hBoundaryFP :
      IsFirstPassageWord (criticalBoundaryWord v.length) :=
    criticalBoundaryWord_isFirstPassage hFP
  have hLowerFP : IsFirstPassageWord lower :=
    C.preserves_firstPassage hBoundaryFP
  have hDepth :=
    C.criticalBoundary_selected_lower_extraDepth_eq_occupancy
      hFP hLen S hkLt
  exact S.fareyResidue_eq_columnLayerFareyResidue hLowerFP hDepth

/-- critical boundary 起点の次セル full-gap quotient も column/layer だけで決まる。 -/
theorem criticalBoundary_next_costQuotient_eq_columnLayer
    {v lower upper : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) lower)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    (S : FerrersStep lower upper)
    (hkLt :
      S.edge.rankCut <
        Collatz2.Word.oddSteps
          (exponentWordOfParity (criticalBoundaryWord v.length))) :
    S.actualRankTopCostQuotient =
      columnLayerCostQuotient
        S.edge.length
        S.edge.oddTotal
        S.edge.rankCut
        (C.rankColumnOccupancy S.edge.rankCut) := by
  have hBoundaryFP :
      IsFirstPassageWord (criticalBoundaryWord v.length) :=
    criticalBoundaryWord_isFirstPassage hFP
  have hLowerFP : IsFirstPassageWord lower :=
    C.preserves_firstPassage hBoundaryFP
  have hDepth :=
    C.criticalBoundary_selected_lower_extraDepth_eq_occupancy
      hFP hLen S hkLt
  exact
    S.actualRankTopCostQuotient_eq_columnLayerCostQuotient
      hLowerFP hDepth

/-- critical boundary 起点の次セル residual cost も column/layer だけで決まる。 -/
theorem criticalBoundary_next_residualCost_eq_columnLayer
    {v lower upper : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) lower)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    (S : FerrersStep lower upper)
    (hkLt :
      S.edge.rankCut <
        Collatz2.Word.oddSteps
          (exponentWordOfParity (criticalBoundaryWord v.length))) :
    S.actualRankTopResidualCost =
      columnLayerResidualCost
        S.edge.length
        S.edge.oddTotal
        S.edge.rankCut
        (C.rankColumnOccupancy S.edge.rankCut) := by
  have hBoundaryFP :
      IsFirstPassageWord (criticalBoundaryWord v.length) :=
    criticalBoundaryWord_isFirstPassage hFP
  have hLowerFP : IsFirstPassageWord lower :=
    C.preserves_firstPassage hBoundaryFP
  have hDepth :=
    C.criticalBoundary_selected_lower_extraDepth_eq_occupancy
      hFP hLen S hkLt
  exact
    S.actualRankTopResidualCost_eq_columnLayerResidualCost
      hLowerFP hDepth

/-- critical boundary 起点の次セル residual lambda も column/layer だけで決まる。 -/
theorem criticalBoundary_next_residualLambda_eq_columnLayer
    {v lower upper : ParityWord}
    (C : FerrersChain (criticalBoundaryWord v.length) lower)
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    (S : FerrersStep lower upper)
    (hkLt :
      S.edge.rankCut <
        Collatz2.Word.oddSteps
          (exponentWordOfParity (criticalBoundaryWord v.length))) :
    S.actualResidualRankTopLambda =
      columnLayerResidualLambda
        S.edge.length
        S.edge.oddTotal
        S.edge.rankCut
        (C.rankColumnOccupancy S.edge.rankCut) := by
  have hBoundaryFP :
      IsFirstPassageWord (criticalBoundaryWord v.length) :=
    criticalBoundaryWord_isFirstPassage hFP
  have hLowerFP : IsFirstPassageWord lower :=
    C.preserves_firstPassage hBoundaryFP
  have hDepth :=
    C.criticalBoundary_selected_lower_extraDepth_eq_occupancy
      hFP hLen S hkLt
  exact
    S.actualResidualRankTopLambda_eq_columnLayerResidualLambda
      hLowerFP hDepth

/--
一つの critical-boundary chain prefix と次 step が同時に保持する column/layer packet。
-/
structure CriticalColumnLayerCellPacket
    {v lower upper : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    (C : FerrersChain (criticalBoundaryWord v.length) lower)
    (S : FerrersStep lower upper)
    (hkLt :
      S.edge.rankCut <
        Collatz2.Word.oddSteps
          (exponentWordOfParity (criticalBoundaryWord v.length))) where
  layer : ℕ
  layer_eq_occupancy : layer = C.rankColumnOccupancy S.edge.rankCut
  residue_eq :
    S.edge.toFareyCellPacket.residue =
      columnLayerFareyResidue
        S.edge.length S.edge.oddTotal S.edge.rankCut layer
  quotient_eq :
    S.actualRankTopCostQuotient =
      columnLayerCostQuotient
        S.edge.length S.edge.oddTotal S.edge.rankCut layer
  residualCost_eq :
    S.actualRankTopResidualCost =
      columnLayerResidualCost
        S.edge.length S.edge.oddTotal S.edge.rankCut layer
  residualLambda_eq :
    S.actualResidualRankTopLambda =
      columnLayerResidualLambda
        S.edge.length S.edge.oddTotal S.edge.rankCut layer

/-- canonical packet construction。 -/
def toCriticalColumnLayerCellPacket
    {v lower upper : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length)
    (C : FerrersChain (criticalBoundaryWord v.length) lower)
    (S : FerrersStep lower upper)
    (hkLt :
      S.edge.rankCut <
        Collatz2.Word.oddSteps
          (exponentWordOfParity (criticalBoundaryWord v.length))) :
    CriticalColumnLayerCellPacket hFP hLen C S hkLt := by
  let j := C.rankColumnOccupancy S.edge.rankCut
  refine {
    layer := j
    layer_eq_occupancy := rfl
    residue_eq := ?_
    quotient_eq := ?_
    residualCost_eq := ?_
    residualLambda_eq := ?_
  }
  · simpa [j] using
      C.criticalBoundary_next_fareyResidue_eq_columnLayer
        hFP hLen S hkLt
  · simpa [j] using
      C.criticalBoundary_next_costQuotient_eq_columnLayer
        hFP hLen S hkLt
  · simpa [j] using
      C.criticalBoundary_next_residualCost_eq_columnLayer
        hFP hLen S hkLt
  · simpa [j] using
      C.criticalBoundary_next_residualLambda_eq_columnLayer
        hFP hLen S hkLt

end FerrersChain

end CSTMicro
end Collatz2
