import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FerrersColumnOccupancy
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.FerrersCellResiduePotential
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.ResidualRankTopLedger

/-!
# Column/layer -> canonical Farey cell bridge

critical boundary を depth zero とし、Ferrers move `01 -> 10` が selected rank column の
`extraDepth` を exact に 1 増やすことを使う。

rank column `k` で、lower 側の current extra depth が `j` なら selected cell の
standard position は

  i = criticalHeight(k) - j - 1

であり、Farey left exponent は

  a = k + 1

である。したがって actual Farey residue は endpoint `(H,m)` と column/layer `(k,j)`
だけから `ferrersCellResidueWeight` により復元できる。

さらに `C = G-D` を natural cost に戻し、ResidualRankTopLedger の

  costQuotient,
  residualCost,
  residualLambda

も同じ `(H,m,k,j)` から canonical に復元する。
-/

namespace Collatz2
namespace CSTMicro

/-- rank column `k` の layer `j` に対応する standard Ferrers position。 -/
def columnLayerPosition (k j : ℕ) : ℕ :=
  Collatz2.Word.criticalHeight k - j - 1

/-- rank column `k` の Farey left exponent。 -/
def columnLayerLeftExponent (k : ℕ) : ℕ :=
  k + 1

/-- endpoint `(H,m)` の natural terminal gap。 -/
def columnLayerGap (H m : ℕ) : ℕ :=
  2 ^ H - 3 ^ m

/--
endpoint `(H,m)` と rank column/layer `(k,j)` だけから作る canonical Farey residue。
-/
def columnLayerFareyResidue
    (H m k j : ℕ) : ℤ :=
  ferrersCellResidueWeight
    H m
    (columnLayerPosition k j)
    (columnLayerLeftExponent k)

/-- canonical cell cost `C = G-D` の natural lift。 -/
def columnLayerCellCostNat
    (H m k j : ℕ) : ℕ :=
  Int.toNat
    ((columnLayerGap H m : ℤ) - columnLayerFareyResidue H m k j)

/-- canonical cell cost の full-gap quotient。 -/
def columnLayerCostQuotient
    (H m k j : ℕ) : ℕ :=
  rankTopCostQuotient
    (columnLayerGap H m)
    (columnLayerCellCostNat H m k j)

/-- canonical cell cost の bounded residual。 -/
def columnLayerResidualCost
    (H m k j : ℕ) : ℕ :=
  rankTopResidualCost
    (columnLayerGap H m)
    (columnLayerCellCostNat H m k j)

/-- canonical cell の residual four-letter lambda。 -/
def columnLayerResidualLambda
    (H m k j : ℕ) : ℕ :=
  residualRankTopLambda
    (columnLayerGap H m)
    (columnLayerCellCostNat H m k j)

namespace AdjacentFerrersSwap

/-- selected rank cut と Farey left exponent は `a = k+1` で一致する。 -/
theorem fareyLeftExponent_eq_rankCut_add_one
    (S : AdjacentFerrersSwap) :
    S.fareyLeftExponent = S.rankCut + 1 := by
  unfold AdjacentFerrersSwap.fareyLeftExponent
    AdjacentFerrersSwap.rankCut
  rfl

end AdjacentFerrersSwap

namespace FerrersStep

/--
selected lower cell の current extra depth が `j` なら、swap position は
critical roof から `j+1` 下の位置に exact にある。
-/
theorem position_eq_columnLayerPosition_of_lower_extraDepth
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {j : ℕ}
    (hDepth : parityExtraDepth lower S.edge.rankCut = j) :
    S.edge.position = columnLayerPosition S.edge.rankCut j := by
  have hEdgeLowerFP : IsFirstPassageWord S.edge.lowerWord :=
    S.edge_lower_firstPassage hLowerFP
  have hWord :
      exponentWordOfParity lower = S.edge.rankLowerExponentWord := by
    unfold AdjacentFerrersSwap.rankLowerExponentWord
    exact congrArg exponentWordOfParity S.lower_eq
  have hDepthEdge :
      Collatz2.Word.extraDepth
          S.edge.rankLowerExponentWord S.edge.rankCut = j := by
    unfold parityExtraDepth at hDepth
    rw [hWord] at hDepth
    exact hDepth
  have hCheckpoint :=
    S.edge.prefixTwoDepth_rankCut_eq_position_add_one hEdgeLowerFP
  have hSlack := S.rankCell_oneStepFirstPassageSlack hLowerFP
  have hRoof :
      S.edge.position + 1 ≤
        Collatz2.Word.criticalHeight S.edge.rankCut :=
    Collatz2.Word.le_criticalHeight_of_twoPow_lt_threePow hSlack
  unfold Collatz2.Word.extraDepth at hDepthEdge
  rw [hCheckpoint] at hDepthEdge
  unfold columnLayerPosition
  omega

/-- actual common endpoint gap は `(H,m)` から作った `columnLayerGap`。 -/
theorem actualRankTopGap_eq_columnLayerGap
    {lower upper : ParityWord}
    (S : FerrersStep lower upper) :
    S.actualRankTopGap =
      columnLayerGap S.edge.length S.edge.oddTotal := by
  unfold actualRankTopGap columnLayerGap wordTerminalGap
  rw [S.edge.lowerWord_length, S.edge.lowerWord_oddCount]

/--
first-passage selected cell の signed Farey gap は natural endpoint gap の cast。
-/
theorem fareyGap_eq_columnLayerGap_cast
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower) :
    S.edge.toFareyCellPacket.G =
      (columnLayerGap S.edge.length S.edge.oddTotal : ℤ) := by
  have hEdgeLowerFP := S.edge_lower_firstPassage hLowerFP
  have hContract :
      3 ^ S.edge.oddTotal < 2 ^ S.edge.length := by
    have h := hEdgeLowerFP.2.2
    unfold CoefficientContracting at h
    rw [S.edge.lowerWord_oddCount, S.edge.lowerWord_length] at h
    exact h
  change
    (2 : ℤ) ^ S.edge.length - (3 : ℤ) ^ S.edge.oddTotal =
      ((2 ^ S.edge.length - 3 ^ S.edge.oddTotal : ℕ) : ℤ)
  rw [Nat.cast_sub (Nat.le_of_lt hContract)]
  push_cast
  rfl

/--
selected actual Farey residue `D` は endpoint `(H,m)` と current column/layer `(k,j)`
だけから exact に復元できる。
-/
theorem fareyResidue_eq_columnLayerFareyResidue
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {j : ℕ}
    (hDepth : parityExtraDepth lower S.edge.rankCut = j) :
    S.edge.toFareyCellPacket.residue =
      columnLayerFareyResidue
        S.edge.length S.edge.oddTotal S.edge.rankCut j := by
  have hPosition :=
    S.position_eq_columnLayerPosition_of_lower_extraDepth hLowerFP hDepth
  have hLeft := S.edge.fareyLeftExponent_eq_rankCut_add_one
  have hResid := S.edge.fareyResidue_eq_ferrersCellResidueWeight
  unfold columnLayerFareyResidue columnLayerLeftExponent
  rw [← hPosition, ← hLeft]
  exact hResid

/--
actual positive cell cost の natural representative も column/layer data だけで復元できる。
-/
theorem fareyCellCost_toNat_eq_columnLayerCellCostNat
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {j : ℕ}
    (hDepth : parityExtraDepth lower S.edge.rankCut = j) :
    S.edge.fareyCellCost.toNat =
      columnLayerCellCostNat
        S.edge.length S.edge.oddTotal S.edge.rankCut j := by
  have hGap := S.fareyGap_eq_columnLayerGap_cast hLowerFP
  have hResid :=
    S.fareyResidue_eq_columnLayerFareyResidue hLowerFP hDepth
  unfold AdjacentFerrersSwap.fareyCellCost columnLayerCellCostNat
  rw [hGap, hResid]

/-- actual full-gap cost quotient は column/layer invariant。 -/
theorem actualRankTopCostQuotient_eq_columnLayerCostQuotient
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {j : ℕ}
    (hDepth : parityExtraDepth lower S.edge.rankCut = j) :
    S.actualRankTopCostQuotient =
      columnLayerCostQuotient
        S.edge.length S.edge.oddTotal S.edge.rankCut j := by
  have hGap := S.actualRankTopGap_eq_columnLayerGap
  have hCost :=
    S.fareyCellCost_toNat_eq_columnLayerCellCostNat hLowerFP hDepth
  unfold actualRankTopCostQuotient columnLayerCostQuotient
  rw [hGap, hCost]

/-- actual bounded residual cost は column/layer invariant。 -/
theorem actualRankTopResidualCost_eq_columnLayerResidualCost
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {j : ℕ}
    (hDepth : parityExtraDepth lower S.edge.rankCut = j) :
    S.actualRankTopResidualCost =
      columnLayerResidualCost
        S.edge.length S.edge.oddTotal S.edge.rankCut j := by
  have hGap := S.actualRankTopGap_eq_columnLayerGap
  have hCost :=
    S.fareyCellCost_toNat_eq_columnLayerCellCostNat hLowerFP hDepth
  unfold actualRankTopResidualCost columnLayerResidualCost
  rw [hGap, hCost]

/-- actual residual four-letter lambda は column/layer invariant。 -/
theorem actualResidualRankTopLambda_eq_columnLayerResidualLambda
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {j : ℕ}
    (hDepth : parityExtraDepth lower S.edge.rankCut = j) :
    S.actualResidualRankTopLambda =
      columnLayerResidualLambda
        S.edge.length S.edge.oddTotal S.edge.rankCut j := by
  have hGap := S.actualRankTopGap_eq_columnLayerGap
  have hCost :=
    S.fareyCellCost_toNat_eq_columnLayerCellCostNat hLowerFP hDepth
  unfold actualResidualRankTopLambda columnLayerResidualLambda
  rw [hGap, hCost]

/-- column/layer residual lambda は常に `{0,1,2,3}`。 -/
theorem columnLayerResidualLambda_cases
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hLowerFP : IsFirstPassageWord lower)
    {j : ℕ}
    (hDepth : parityExtraDepth lower S.edge.rankCut = j) :
    columnLayerResidualLambda
          S.edge.length S.edge.oddTotal S.edge.rankCut j = 0 ∨
      columnLayerResidualLambda
          S.edge.length S.edge.oddTotal S.edge.rankCut j = 1 ∨
      columnLayerResidualLambda
          S.edge.length S.edge.oddTotal S.edge.rankCut j = 2 ∨
      columnLayerResidualLambda
          S.edge.length S.edge.oddTotal S.edge.rankCut j = 3 := by
  rw [← S.actualResidualRankTopLambda_eq_columnLayerResidualLambda
        hLowerFP hDepth]
  exact S.actualResidualRankTopLambda_cases hLowerFP

end FerrersStep

end CSTMicro
end Collatz2
