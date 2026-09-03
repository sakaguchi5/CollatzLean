import CollatzLean.Collatz2.CSTMicro.MultiCorner.TerminalLastTwoExposedNormalForm
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CarryNormalizedCheckpoint
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RecordFerrersExposedProvenance
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedBranchDivisibility
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalComponentRigidity
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSingleCornerHenselObligation
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedBranchClosure
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTwoCornerHensel
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCarryNormalizedTail
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCanonicalHenselBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedHenselFactorRepeat
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedHenselZeroCycleBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedHenselNonzeroRepeatObligation
import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftOfCriticalizationBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselBeattyArithmetic
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselFactorRepeat
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselNonzeroRepeat
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselPrimitiveZeroClosure
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselZeroCycle
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselLargeWidthClosure
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselFinite36
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCriticalTailFusion
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedRepeatIntervalDefectBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedRightEndSmallness
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselFinite36
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedShiftedRepeatIntervalDefect
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalPredFusion
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalFareyComparison
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCriticalizationUnitBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalThreeClearance
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalTailDepthCoordinates
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedShiftedRepeatStateDifference
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedFreeBaseQOneBound
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedNonzeroRepeatDepthBudget
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedActualTerminalMountain
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedMountainParameterLeftIdentity
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedMountainParameterTerminalInverse
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedActualMountainBridge
/-
# MultiCorner attached Shared-Cost checkpoint umbrella

attached branch の数学的 Shared-Cost 方針をまとめて import する入口。

この段階では attached impossibility 自体は主張しない。
二つの predecessor が共有する `G-q` budget、straight cost transport、
entrance-depth Hensel residue を lossless に保持し、次段の純算術排除定理へ渡す。
-/
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedSharedCostArithmetic
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedSharedCostTransfer
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedEntranceDepthHensel
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedSharedCostCheckpoint
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedSharedCostRhoDepthCompatibility
import CollatzLean.Collatz2.CSTMicro.MultiCorner.ActualAttachedSharedCostPairAssembly
import CollatzLean.Collatz2.CSTMicro.MultiCorner.ActualAttachedDoublePredecessorSafety
--
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedIntervalFerrersDefectBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedIntervalFerrersHenselBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedLocalizedThreeClearance

/-
# criticalization boundary digit 集約

arithmetic criticalization の最左境界 `s = criticalizationStart` について、

1. `s-1` から critical shadow を延長する residue が成立しないこと、
2. global profile numerator の exact 3 進 quotient `criticalizationUnit` を
   開始 state `Z_s` で展開すること、
3. `criticalizationUnit` の最初の mod 3 digit が、その one-step extension failure と
   一致すること、

この層では actual exponent word が `s` から critical になるとは仮定しない。
扱うのは integral critical shadow と profile numerator の exact 3 進境界だけである。
-/
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CriticalizationPredResidue
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CriticalizationUnitStartState
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CriticalizationUnitModThree
/-
# Criticalization boundary digit bridge

criticalization boundary の arithmetic を次の順で集約する。

1. actual minimal-B packet から boundary arithmetic を取得する;
2. canonical unit の最初の 3 進 digit を `ZMod 3` の `1 / 2` に有限化する;
3. criticalization より左の任意 cut の residual へ exact に transport する;
4. Left Case II の exposed provenance と同じ packet に束ねる。

-/
import CollatzLean.Collatz2.CSTMicro.MultiCorner.ActualCriticalizationBoundaryDigit
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CriticalizationBoundaryDigitZMod3
import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftExposedCriticalizationDigitBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftRecordFerrersResidualIncompatibility
--
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RecordFerrersExposedProvenanceNumericalization
import CollatzLean.Collatz2.CSTMicro.MultiCorner.PreviousExposedRecordEmbedding
import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftExposedCriticalizationNormalizedTail
/-
# MultiCorner: hard Case II shifted-criticalization

 hard Case II

  previous < b ≤ criticalizationStart < terminalCriticalStart

で使う新しい bridge

`RestartedTerminalGeometryPacket`
: Case I 固有条件 `criticalizationStart ≤ previous` を geometry から除去する。
  restarted support の positivity、`h(b)=1`、interior run-gap `=1`、
  checkpoint の slope-one line を Case II でも利用可能にする。

`ShiftedCriticalizationHenselPacket`
: arithmetic criticalization start `s` から terminal start `c` まで Hensel chain を shift し、
  次の exact bridge を与える。

  * `(2)` `U = N_s + 2^p_s qH_s`
  * `(3)` criticalization unit の start-state 展開
  * `(4)` `2^p_s qH_s` の affine/shadow 差表示
  * `(5)` `qH_s = X_s - 2^h(s) Z_s`
  * `(6)` `X_s > 2^h(s) Z_s`
  * `(8)` critical shadow の `s-1` への integral extension failure

`ActualShiftedCriticalizationHenselPacket`
: pure witness `y-q` を actual minimal-B の upper representative に戻し、
  shifted affine state の actual endpoint coordinate を露出する。

## 残る数学

前段で式 `(7)` と呼んだ actual difference recurrence を完全に閉じるには、
`affineStateAtCriticalization` と actual step-by-step prefix trace state の同定が必要である。
その未証明 bridge を仮定せず、`ShiftedActualLeftStepObligation` として明示する。
-/
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalGeometryPacket
import CollatzLean.Collatz2.CSTMicro.MultiCorner.ShiftedCriticalizationHenselPacket
import CollatzLean.Collatz2.CSTMicro.MultiCorner.ActualShiftedCriticalizationHenselPacket

--
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalAffineNumerator
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedCaseIIEndpointBalance
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSharedCostTwoBand
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedActualSharedCostPairAssembly
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedActualProfileWeightBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedActualDoublePredecessorSafety
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedCaseIIEndpointReduction
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedCaseIIActualEndpointReduction
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedCaseIIEndpointClosureReduction

/-!
# CSTMicro MultiCorner

`card E ≥ 2` branch の共通入口。


-/
