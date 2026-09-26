import CollatzLean.Collatz4.Dynamics.Odd
import CollatzLean.Collatz4.Dynamics.Reachability

import CollatzLean.Collatz4.Family.Basic
import CollatzLean.Collatz4.Family.Branch
import CollatzLean.Collatz4.Family.QStart
import CollatzLean.Collatz4.Family.Research

import CollatzLean.Collatz4.Parametric.Reachability
import CollatzLean.Collatz4.Parametric.Reverse

import CollatzLean.Collatz4.Finite.Forward
import CollatzLean.Collatz4.Finite.Normalization
import CollatzLean.Collatz4.Finite.Envelope
import CollatzLean.Collatz4.Finite.QCutoff
import CollatzLean.Collatz4.Finite.CandidateInterval
import CollatzLean.Collatz4.Finite.ResidualBounds
import CollatzLean.Collatz4.Finite.ResidualEnvelope
import CollatzLean.Collatz4.Finite.ForwardSemantics
import CollatzLean.Collatz4.Finite.ForwardProblem
import CollatzLean.Collatz4.Finite.Witness
import CollatzLean.Collatz4.Finite.FiniteReduction
import CollatzLean.Collatz4.Finite.Pruning
import CollatzLean.Collatz4.Finite.Exclusion

import CollatzLean.Collatz4.Targets.M7

set_option linter.style.header false

/-!
# Collatz4

Collatz4 の研究対象は、二進数表記で

`101, 1011, 10111, 101111, ...`

となる数列

`A_n = 3 * 2^n - 1` (`n >= 1`)

から始まる Collatz 軌道である。

## 層構造

1. `Dynamics`
   任意の奇数 Collatz 軌道にも適用できる一般定理だけを置く道具層。
   Collatz4 が一般の Collatz 予想を研究対象にする、という意味ではない。

2. `Family`
   `A_n = 3*2^n-1`、すなわち `101...` 族そのものを定義する研究対象層。

3. `Parametric`
   族の内部で target branch `M` を変数にする一般化。
   `M=3,5,7,9,...` を同じ語彙で比較する。

4. `Finite`
   M に依存しない有限状態・包絡線・候補区間・certificate の証明機械。

5. `Targets/M*`
   各 M の個別研究。現在は `Targets/M7` を収録する。
   今後 `Targets/M5`, `Targets/M9`, `Targets/M11`, ... を横並びで追加する。

`Targets/M7` の finite exclusion は既存 ZIP の証明を保持して再配置している。
`Parametric` の reachability から M7 witness への最上流 bridge は、研究対象の定義を
固定した後に別途接続する。
-/
