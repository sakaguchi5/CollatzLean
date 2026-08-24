import CollatzLean.Collatz2.CSTMicro.MultiCorner.TerminalLastTwoExposedNormalForm
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CarryNormalizedCheckpoint
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RecordFerrersExposedProvenance
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedBranchDivisibility
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalComponentRigidity
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSingleCornerHenselObligation
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedBranchClosure
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTwoCornerHensel
import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftOfCriticalizationBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselBeattyArithmetic
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselFactorRepeat
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselNonzeroRepeat
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselPrimitiveZeroClosure
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselZeroCycle
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselLargeWidthClosure
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselFinite36

/-!
# CSTMicro MultiCorner

`card E ≥ 2` branch の共通入口。

restarted Case I は corrected terminal component から suffix-Hensel chain へ移し、

* finite range `width ≤ 36` は deterministic backward certificate,
* large range `37 ≤ width` は Beatty factor repeat + zero-cycle closure

で全幅を axiom なしに排除する。

`RestartedSingleCornerHenselObligation.lean` は旧 API 名を theorem として残す
compatibility wrapper であり、未証明 obligation は持たない。
最終 theorem-only closure は `RestartedBranchClosure.lean`。
-/
