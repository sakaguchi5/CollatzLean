/-
# 第3例 fixed-window 探索核 集約

このファイルは、第3例探索の 1〜8 をまとめて import する。

1. 左 68 block の 2 進 affine 切断
2. 左 68 block から開始値 residue の一意復元
3. 右 42 block の 3 進 affine 切断
4. Record plateau の Hensel 一括転送
5. Record jump → Hensel boundary の局所 bridge
6. terminal Hensel の 3-lift survivor 上界
7. 標準ブロック transfer の合成
8. special return による actual first drop = coefficient first crossing

巨大整数 `G` や全軌道を hot loop で生成せず、左右 collar と中央の圧縮 transfer を
分離するための最小核である。
-/
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.AffinePrefixModTwo
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.StartValuePrefix68
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.AffineSuffixModThree
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordPlateauQOneMacro
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordJumpHenselBoundary
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.TerminalHenselThreeLift
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.StandardBlockTransfer
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.FirstCrossingSpecialReturn
--
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordPlateauLocalMacro
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.PlateauPhiClosedForm
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordPlateauOneParameter
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordFerrersProvenanceAdapter
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordJumpHenselDictionary
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.TerminalBoundaryLiftSurvival
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ActualOstrowskiStandardBlockTransfer
/-
# 第3例探索 次段 1-2
1. 実 Hensel 3-lift と criticalization boundary digit の exact adapter
2. canonical Ostrowski block list 全体の StandardBlockTransfer fold
-/
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.TerminalHenselBoundaryDigitAdapter
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.CanonicalOstrowskiTransferFold

/-
# 第3例探索: 計算可能性の追加修正

1. canonical Ostrowski decomposition を最小 rank で実行する高速版
2. `Fin 3` Hensel digit label を実際の三つの integer lift 値へ接続する adapter
-/

import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.FastCanonicalOstrowskiRank
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ArithmeticHenselLiftValueAdapter
--
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.GapOneSuffixHenselBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleConvergent22Checkpoint
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ModularStandardBlockTransfer
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ModularContinuedFractionStandardBlock
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleOddScaleModularTransfers
/-
A. corrected CF packet + proof-only actual certification interface
B. certified one-block modular transfer correctness
C. canonical 42-block modular fold correctness

探索 hot path は literal P/Q と ZMod recurrence のみを使い、
巨大 `criticalPowerP/Q` / `criticalIntervalPhiZ` を評価しない。
actual power-Farey との一致証明は `ThirdExampleCFPacketCertification` に隔離される。
-/
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCFPacketCertification
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleOneBlockModularCorrectness
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCanonical42ModularFold
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCanonical42FullPrefixBridge

import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleResidueSearchState
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleHensel42ResidueCompleteness
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleResidueD2Aggregate
--
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleForcedHensel42
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleResidueD2Aggregate
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleD3ComputableHenselAggregate
--
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleComputableBackwardPredecessor
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleComputableBackwardPredecessorActualSoundness
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleBackwardHensel42
/-
# 第3例探索: last-41 / long-width pruning umbrella

次段の仕事は、この有限 `(r,d,w)` domain ごとに最後41列以下の Ferrers deficit
residue を作り、full-defect residue との affine compatibility から endpoint residue を
復元すること。
-/
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleLast41TailPruning
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleLongWidthPhaseCheckpoint
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleLongWidthBranchPruning
--
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteDeficitBranch
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleGapOneAffineCompatibility
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteDeficitEvaluator
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteDeficitSoundness
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleNativeDeficitVerifier
--
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleActualLast41Bridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFullDeficitProfileNumeratorBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleBranchLocalDeficitCandidates
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDeficitThreeAdicFilter
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDirectEndpointResidue
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleIndependentResidualFilter
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFinalNativeKernel
--
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleResidueSearchState
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCleanDirectEndpointResidue
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleCleanActualFerrersDeficitBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleD3CleanAggregate
--
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleEndpointBound42
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleGapFactors
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDeficitTwoAdicNonvanishing
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFirstDefectOneCell
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.FerrersDeficitValuationPeeling
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleVisibleDefectDecoder68
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleDecoderIndependentProfileBridge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleRightCompressedDeficitMerge
import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleValuationSearchAggregate


namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- 今回の continued-fraction target に対応する first-drop odd block 数。 -/
def targetP : ℕ := 6586818669

/-- 今回の continued-fraction target に対応する first-drop two-depth。 -/
def targetH : ℕ := 10439860590

/-- 左 collar の odd block 幅。 -/
def leftCollarWidth : ℕ := 68

/-- 右 collar の odd block 幅。 -/
def rightCollarWidth : ℕ := 42

/-- 左右 collar を除いた中央 odd block 数。 -/
def middleOddBlocks : ℕ :=
  targetP - leftCollarWidth - rightCollarWidth

/-- 中央 window は 6,586,818,559 odd blocks。 -/
theorem middleOddBlocks_eq :
    middleOddBlocks = 6586818559 := by
  decide

end ThirdExampleSearch
end CSTMicro
end Collatz2
