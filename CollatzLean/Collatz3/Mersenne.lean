import CollatzLean.Collatz3.Mersenne.Basic
import CollatzLean.Collatz3.Mersenne.OneZero
import CollatzLean.Collatz3.Mersenne.ExitDepth
import CollatzLean.Collatz3.Mersenne.Word
import CollatzLean.Collatz3.Mersenne.MacroLine
import CollatzLean.Collatz3.Mersenne.Derived
import CollatzLean.Collatz3.Mersenne.OneZeroRegions
import CollatzLean.Collatz3.Mersenne.OneZeroSparseComplement
import CollatzLean.Collatz3.Mersenne.BoundedBlockSUnitReduction
import CollatzLean.Collatz3.Mersenne.BoundedBlockDefectEscape
import CollatzLean.Collatz3.Mersenne.SourceDefectBridge
import CollatzLean.Collatz3.Mersenne.FixedDefectEscape
import CollatzLean.Collatz3.Mersenne.QuantitativeDefectEscape
import CollatzLean.Collatz3.Mersenne.TwoSidedSparseDefectEscape
import CollatzLean.Collatz3.Mersenne.SmallHoleExact
import CollatzLean.Collatz3.Mersenne.SmallHoleModular
import CollatzLean.Collatz3.Mersenne.SmallHolePeel
import CollatzLean.Collatz3.Mersenne.SmallHoleParity
import CollatzLean.Collatz3.Mersenne.NoHoleProof
import CollatzLean.Collatz3.Mersenne.NoHoleSourceOneProof
import CollatzLean.Collatz3.Mersenne.NoHoleMersenneQuotientProof
import CollatzLean.Collatz3.Mersenne.NoHoleMersenneQuotientDerived
import CollatzLean.Collatz3.Mersenne.SmallHoleExitDepth
import CollatzLean.Collatz3.Mersenne.TailLoopModular
import CollatzLean.Collatz3.Mersenne.OneHoleFiniteTailLoopSieve
import CollatzLean.Collatz3.Mersenne.OneHoleFiniteLift65536
import CollatzLean.Collatz3.Mersenne.OneHoleThreeTailLargeDepth
import CollatzLean.Collatz3.Mersenne.OneHoleSourceResidualProof
import CollatzLean.Collatz3.Mersenne.TargetOneHoleGeometric
import CollatzLean.Collatz3.Mersenne.GeometricSum
import CollatzLean.Collatz3.Mersenne.TwoAdicArithmetic
import CollatzLean.Collatz3.Mersenne.TargetOneHoleValuation
import CollatzLean.Collatz3.Mersenne.TargetOneHoleGcd
import CollatzLean.Collatz3.Mersenne.TargetOneHoleLocks
import CollatzLean.Collatz3.Mersenne.TargetOneHolePrimitive
import CollatzLean.Collatz3.Mersenne.TargetOneHoleBase64Descent
import CollatzLean.Collatz3.Mersenne.TargetOneHoleExternalArithmetic
import CollatzLean.Collatz3.Mersenne.TargetOneHoleFourBranchClosure
import CollatzLean.Collatz3.Mersenne.AtMostOneHoleExternalClosure
import CollatzLean.Collatz3.Mersenne.SourceTwoHoleRegularProof
import CollatzLean.Collatz3.Mersenne.TargetTwoHolePhase
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleGeometric
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleTwoAdicCuts
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleGcd
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleValuation

/-!
# Collatz3 Mersenne

Mersenne block の純粋整数算術、small-hole normal form、one-hole closure、
two-hole internal reduction をまとめる aggregate import。

今回の refactor では次の薄い共通層を追加した。

* `GeometricSum`: geometric sum の単調性・奇偶・上界・tail 分解。
* `TwoAdicArithmetic`: cut proof で共通する 2-adic helper。
* `SmallHolePeel`: top hole を一つ短い既知 small-hole equation へ落とす。
* `SmallHoleParity`: source endpoint / split target の mod 3 parity rigidity。
* `TargetTwoHoleGcd`: `n≥4` で triple gcd `gcd(q,u,t)=1`。
* `TargetTwoHoleValuation`: 三 phase 共通で width を `v₂(k)` / `v₂(k-1)` から抑える。

既存 public theorem 名は維持し、既存ファイル内の private helper はこの段階では削除しない。
この ZIP が通過した後、それら private 重複を共通層への一行 corollary に置換できる。
-/
