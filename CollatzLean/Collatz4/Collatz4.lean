import CollatzLean.Collatz4.Core.Forward
import CollatzLean.Collatz4.Core.Normalization

import CollatzLean.Collatz4.General.Envelope
import CollatzLean.Collatz4.General.QCutoff
import CollatzLean.Collatz4.General.CandidateInterval
import CollatzLean.Collatz4.General.ForwardProblem
import CollatzLean.Collatz4.General.Witness
import CollatzLean.Collatz4.General.FiniteReduction
import CollatzLean.Collatz4.General.Pruning
import CollatzLean.Collatz4.General.Exclusion

import CollatzLean.Collatz4.M7.Constants
import CollatzLean.Collatz4.M7.QBound
import CollatzLean.Collatz4.M7.LengthBound
import CollatzLean.Collatz4.M7.ForwardReduction
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
2. 各 m は `ForwardProblem` と有限 certificate だけを与える。
3. 元の数論的 witness から finite problem への bridge を積み上げる。
4. 最終排除の論理は `General.Exclusion` を再利用する。

現在の m=7 reduced 主結果:

`Collatz4.Specialization.M7.no_m7_forward_candidate`

将来、元の m=7 witness から reduction が完成した後は

`Collatz4.Specialization.M7.no_witness_of_reduction`

へ bridge を渡すだけで最終非存在が得られる。
-/
