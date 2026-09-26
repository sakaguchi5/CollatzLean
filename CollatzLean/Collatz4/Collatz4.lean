import CollatzLean.Collatz4.Dynamics.Odd
import CollatzLean.Collatz4.Dynamics.Reachability
import CollatzLean.Collatz4.Dynamics.Accumulated
import CollatzLean.Collatz4.Dynamics.Merge
import CollatzLean.Collatz4.Dynamics.ThreePowerFamily
import CollatzLean.Collatz4.Dynamics.SynchronizedMerge
import CollatzLean.Collatz4.Dynamics.MergeCompression
import CollatzLean.Collatz4.Dynamics.ThreePowerCompression

import CollatzLean.Collatz4.Family.Basic
import CollatzLean.Collatz4.Family.Branch
import CollatzLean.Collatz4.Family.QStart
import CollatzLean.Collatz4.Family.Research

import CollatzLean.Collatz4.Parametric.Reachability
import CollatzLean.Collatz4.Parametric.Reverse
import CollatzLean.Collatz4.Parametric.ReachabilityWord
import CollatzLean.Collatz4.Parametric.BranchTerminalMacro

import CollatzLean.Collatz4.Finite.Forward
import CollatzLean.Collatz4.Finite.AccumulatedForwardBridge
import CollatzLean.Collatz4.Finite.ThreePowerForwardCompression
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
import CollatzLean.Collatz4.Finite.ValuationGap
import CollatzLean.Collatz4.Finite.RepresentativeCompression

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
   `Accumulated` / `Merge` / `SynchronizedMerge` で累積2指数写像と合流を扱い、
   `MergeCompression` で多数候補を代表軌道へ圧縮する。
   `ThreePowerFamily` / `ThreePowerCompression` は `3^n-1` 族への特殊化。

2. `Family`
   `A_n = 3*2^n-1`、すなわち `101...` 族そのものを定義する研究対象層。

3. `Parametric`
   族の内部で target branch `M` を変数にする一般化。
   actual reachability から exponent word / branch terminal macro を復元する。

4. `Finite`
   M に依存しない有限状態・包絡線・候補区間・certificate の証明機械。
   `AccumulatedForwardBridge` / `ThreePowerForwardCompression` により
   一般累積写像・合流圧縮を既存 `ForwardProblem` へ exact に接続する。
   `ValuationGap` / `RepresentativeCompression` は代表だけの certificate から
   全候補を排除する論理を担当する。

5. `Targets/M*`
   各 M の個別研究。
   M=7 では従来の直接 finite certificate に加え、
   `2179 -> 97 -> (58 + 39)` の構造圧縮証明を保持する。

`OddQBranchReachable 7 -> HasM7MasterWitness` は exact に接続済み。
固定 finite problem への record extraction は `MasterToWitness` で未証明義務として
明示されている。
-/
