import CollatzLean.CollatzSecondLayer.Reduction
import CollatzLean.CollatzSecondLayer.MovingCompactnessConsequences
import CollatzLean.CollatzSecondLayer.CylinderConsequences

/-!
# 第二層・prepared carry接続の監査

* positive replayはactual `Runs`まで保存する。
* ordered terminal差分と下側軌道埋込みから最小同期境界を自動構成する。
* prepared carry深さはSpecial C3 suffix長の2倍以下である。
* 未証明の強いterminal抽出とbounded-depth rigidityは第三bridgeに残す。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

#check canonicalEnd
#check CanonicalReplayCoordinate
#check CanonicalReplayCoordinate.lowerNaturalReplay
#check ExpWord.Runs.replay_down
#check LowerNaturalRunReplayData
#check CanonicalReplayCoordinate.lowerNaturalRunReplay

#check OrderedDifferenceData
#check OrderedDifferenceData.value_lt
#check OrderedDifferenceData.twoPow_le_difference
#check TerminalLowerOrbitEmbedding
#check terminalLowerOrbitEmbeddingOfExtraction
#check SynchronizationBoundaryData
#check synchronizationBoundaryOfOrbit
#check PreparedCarryData
#check PreparedCarryData.ofOrbit
#check PreparedCarryData.remainingDepth_pos
#check PreparedCarryData.depth_balance
#check PreparedCarryData.syncLength_add_remainingDepth_le_original
#check PreparedCarryData.toCarryComparison

#check RawCarryComparison
#check CarryComparison
#check CarryOrigin
#check TerminalAnalysisPacket
#check TerminalAnalysisPacket.prepared
#check TerminalAnalysisPacket.carry
#check TerminalAnalysisPacket.carryOrigin
#check AlternativeExitAt
#check SpecialC3At
#check analysisOutcome_nonempty
#check InfiniteLowerNaturalReplay

#check SpecialC3Data.connectionEquation
#check SpecialC3Data.negativeShadowExact
#check SpecialC3Data.finish_lt_two_mul_threePow
#check SpecialC3Data.originalDepth_le_twice_suffixLength
#check SpecialC3Data.preparedDepth_le_twice_suffixLength
#check SpecialC3Data.syncLength_add_preparedDepth_le_twice_suffixLength

#check MovingLimitData.limitExponent_zero_eq_one
#check MovingLimitData.limitWord_twoSteps_le_quadratic
#check FirstCrossingCylinder.finish_le_start_add_length
#check C3CylinderSequence.finishes_polynomialSmall

#check InfiniteTerminalExtraction
#check InfiniteTerminalAnalysis
#check PersistentAlternativeExitData
#check ArbitrarilyDeepSpecialC3Data
#check HasInfiniteTerminalExtractionObstruction
#check HasPersistentAlternativeExit
#check HasArbitrarilyDeepSpecialC3
#check TerminalPacketConstructionPrinciple
#check InfiniteOutcomeExtractionPrinciple
#check infiniteTerminalAnalysisPrinciple_of_parts
#check InfiniteTerminalAnalysisPrinciple
#check ReductionBridge.ofArithmetic
#check AsymptoticSpecialC3ExclusionPrinciple
#check unbounded_orbit_reduction
#check arbitrarilyDeepSpecialC3_of_unbounded_of_no_exceptions
#check no_unbounded_orbit

example (B : ReductionBridge) :
    HasUnboundedOddOrbit →
      HasOneSidedMeander ∨
      HasInfiniteTerminalExtractionObstruction ∨
      HasPersistentAlternativeExit ∨
      HasArbitrarilyDeepSpecialC3 :=
  unbounded_orbit_reduction B

end CollatzSecondLayer
