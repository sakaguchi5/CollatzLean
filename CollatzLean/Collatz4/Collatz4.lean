import CollatzLean.Collatz4.Core.Forward
import CollatzLean.Collatz4.Core.Normalization

import CollatzLean.Collatz4.General.Envelope
import CollatzLean.Collatz4.General.QCutoff
import CollatzLean.Collatz4.General.CandidateInterval
import CollatzLean.Collatz4.General.ResidualBounds
import CollatzLean.Collatz4.General.ResidualEnvelope
import CollatzLean.Collatz4.General.ForwardSemantics
import CollatzLean.Collatz4.General.ForwardProblem
import CollatzLean.Collatz4.General.Witness
import CollatzLean.Collatz4.General.FiniteReduction
import CollatzLean.Collatz4.General.Pruning
import CollatzLean.Collatz4.General.Exclusion

import CollatzLean.Collatz4.M7.Constants
import CollatzLean.Collatz4.M7.QBound
import CollatzLean.Collatz4.M7.LengthBound
import CollatzLean.Collatz4.M7.ResidualBounds
import CollatzLean.Collatz4.M7.ResidualBridge
import CollatzLean.Collatz4.M7.ForwardReduction
import CollatzLean.Collatz4.M7.Witness
import CollatzLean.Collatz4.M7.LivePruning
import CollatzLean.Collatz4.M7.FiniteCertificate
import CollatzLean.Collatz4.Specialization.M7
import CollatzLean.Collatz4.M7.Exclusion

set_option linter.style.header false

/-!
# Collatz4

Collatz3 から独立した前向き有限状態アプローチ。

設計方針は

1. `General` に m 非依存の理論を置く。
2. 各 m は残余データと `ForwardProblem`、有限 certificate を与える。
3. 数論的 witness は1段ごとの `ResidualRecurrence` を通して `run` へ接続する。
4. 最終排除の論理は `General.Exclusion` を再利用する。

m=7 では

* 正確な `G_min/G_max` と `r≤E` から q-envelope admissibility
* 境界二点から `4088 ≤ r ≤ 8444`
* 偶数性から有限候補添字
* 意味論的 forward recurrence から `finalState = targetState`
* finite certificate による矛盾

までが接続されている。

意味論的 m=7 witness の非存在は

`Collatz4.Specialization.M7.no_m7_witness`

として公開される。

さらに原始的な指数語・Mersenne block の witness を使う場合は、それを
`Collatz4.M7.HasM7Witness` へ落とす最上流 bridge だけを追加すればよい。
-/
