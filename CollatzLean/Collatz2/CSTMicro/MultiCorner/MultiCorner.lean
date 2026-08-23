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



/-!
# CSTMicro MultiCorner

`card E ≥ 2` branch の共通入口。

restarted Case I は区間を corrected し、
唯一の open arithmetic obligation を
`RestartedSingleCornerHenselObligation.lean` に隔離した。
それ以外の restarted flow は `RestartedBranchClosure.lean` で `False` まで接続済み。
-/
