import CollatzLean.CollatzSecondLayer.Reduction
import CollatzLean.CollatzSecondLayer.MovingCompactnessConsequences
import CollatzLean.CollatzSecondLayer.CylinderConsequences

/-!
# 第二層・canonical replay再構築の監査

* 第一bridgeは完全証明済み。
* canonical終点とpredecessor shadowは語から自動構成する。
* 現行Special C3はcanonical境界・negative predecessor shadow・deferred carryで定義する。
* determinant非零、center差、alpha深さ収支はterminal runから自動導出する。
* 未証明プレースホルダーは使用しない。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

#check canonicalEnd
#check canonicalEnd_realizes
#check canonicalEnd_pos
#check CanonicalReplayCoordinate
#check LowerNaturalReplayData
#check canonicalReplayCoordinate_of_runs
#check predecessorStart_neg
#check predecessorShadow
#check predecessorShadow_realizes
#check predecessorShadow_ne_zero
#check predecessorShadow_neg_iff
#check predecessorShadow_pos_iff
#check CanonicalReplayCoordinate.connectionEquation
#check CanonicalReplayCoordinate.quotient_eq_zero_iff_start_eq_canonical
#check CanonicalReplayCoordinate.lowerNaturalReplay

#check FirstCarryOutcome
#check RawCarryComparison
#check RawCarryComparison.outcome
#check first_carry_trichotomy_nonempty
#check ExpWord.Runs.replay_of_gap_depth_gt_twoSteps
#check ExpWord.Runs.replay_endpoint_exact_difference

#check determinant_ne_zero_of_valid_nonempty
#check alpha_gap_suffix_balance
#check terminal_suffix_exact_twoFactor

#check OddOrbit
#check MovingLimitData
#check movingCompactnessPrinciple
#check MovingLimitData.limitExponent_zero_eq_one
#check MovingLimitData.limitWord_twoSteps_le_quadratic

#check FirstCrossingSequenceData
#check C3CylinderSequence
#check TwoThreeGapPolynomialBound
#check PolynomialBelowTwoPower
#check cylinderUpgradePrinciple_of_arithmetic
#check FirstCrossingCylinder.finish_le_start_add_length
#check C3CylinderSequence.finishes_polynomialSmall

#check TerminalPairData
#check TerminalPairData.suffixDepthBalance
#check TerminalPairData.omegaExactDepth
#check TerminalPairData.center_ne
#check InfiniteTerminalExtraction
#check TerminalAnalysisPacket.replayCoordinate
#check TerminalAnalysisPacket.connectionEquation
#check AlternativeExitAt
#check SpecialC3At
#check analysisOutcome_nonempty
#check InfiniteTerminalAnalysis
#check PersistentAlternativeExitData
#check ArbitrarilyDeepSpecialC3Data
#check SpecialC3Data.connectionEquation
#check SpecialC3Data.negativeShadowExact
#check SpecialC3Data.finish_lt_two_mul_threePow
#check SpecialC3Data.suffixStart_eq_canonicalStart

#check HasInfiniteTerminalExtractionObstruction
#check HasPersistentAlternativeExit
#check HasArbitrarilyDeepSpecialC3
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
