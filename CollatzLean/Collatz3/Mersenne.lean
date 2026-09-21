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
import CollatzLean.Collatz3.Mersenne.ThreeTailModular
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
import CollatzLean.Collatz3.Mersenne.SplitTwoHoleMinimalPatterns
import CollatzLean.Collatz3.Mersenne.SplitTwoHoleMinimalCertificate
import CollatzLean.Collatz3.Mersenne.TargetTwoHolePhase
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleGeometric
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleTwoAdicCuts
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleGcd
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleValuation
import CollatzLean.Collatz3.Mersenne.BlockComplexity
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleBlockComplexityProof
import CollatzLean.Collatz3.Mersenne.SplitTwoHoleProperResidualProof
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleSmallSource
import CollatzLean.Collatz3.Mersenne.SourceTwoHoleResonanceThreeTail
import CollatzLean.Collatz3.Mersenne.TwoHoleUnitArithmetic
import CollatzLean.Collatz3.Mersenne.SourceTargetTwoHoleMinimalPatterns
import CollatzLean.Collatz3.Mersenne.SourceTargetTwoHoleMinimalCertificate
import CollatzLean.Collatz3.Mersenne.SourceTargetTwoHoleProperResidualProof
import CollatzLean.Collatz3.Mersenne.TwoHoleFullPattern
import CollatzLean.Collatz3.Mersenne.TwoHoleFullExternalArithmetic
import CollatzLean.Collatz3.Mersenne.AtMostTwoHoleExternalClosure

/-!
# Collatz3 Mersenne

Mersenne block の純粋整数算術、small-hole normal form、one-hole closure、
two-hole internal reduction をまとめる aggregate import。

共通 refactor 層:

* `GeometricSum`: geometric sum の単調性・奇偶・上界・tail 分解。
* `TwoAdicArithmetic`: cut proof で共通する 2-adic helper。
* `SmallHolePeel`: top hole を一つ短い既知 small-hole equation へ落とす。
* `SmallHoleParity`: source endpoint / split target の mod 3 parity rigidity。
* `TargetTwoHoleGcd`: `n≥4` で triple gcd `gcd(q,u,t)=1`。
* `TargetTwoHoleValuation`: 三 phase 共通で width を `v₂(k)` / `v₂(k-1)` から抑える。

7--9 層:

* `BlockComplexity`: `Binary.HasPeriodBreakAtMost` を target-two の内部 target として固定し、
  Stephan の variable-period corollary を明示的 external interface として接続する。
* `ThreeTailModular`: M₄ の 2/3 tail-loop certificate を one-hole finite sieve から独立させる。
* `SplitTwoHoleMinimalPatterns`: split-two の六項 `{2,3}`-unit 語彙を固定する。

追加 closure 層:

* `Binary.BlockPeriod`: 固定幅 block 列の period-break を隣接 block mismatch へ還元する。
* `TargetTwoHoleBlockComplexityProof`: `n≥4` の三 geometric phase から
  `TargetTwoHolePeriodBreakAtMostFive` を内部 theorem として閉じる。
* `SplitTwoHoleMinimalCertificate`: split-two equation から anchor-minimal certificate の存在を回収する。
* `SplitTwoHoleProperResidualProof`: non-full minimal certificate を `k≤2` へ落とし、
  `k≥3` では full six-term だけにする。
* `TargetTwoHoleSmallSource`: `n=2→n=1` bridge と `n=3` の mod 7 residue phase を固定する。
* `SourceTwoHoleResonanceThreeTail`: source-two low resonance を M₄ residual state へ縮約する。

full six-term 統合層:

* `TwoHoleUnitArithmetic`: source/target non-full 排除で共有する局所指数算術。
* `SourceTargetTwoHoleMinimalPatterns`: source/target の six-unit index と certificate 語彙。
* `SourceTargetTwoHoleMinimalCertificate`: exact equation から minimal certificate を構成する。
* `SourceTargetTwoHoleProperResidualProof`: source/target の non-full をともに `k=1` へ落とす。
* `TwoHoleFullPattern`: three placements を `TwoHoleWellFormedEquation` / `TwoHoleFullCase` にまとめる。
* `TwoHoleFullExternalArithmetic`: genuinely full six-term case だけの外部算術 interface。
* `AtMostTwoHoleExternalClosure`: one-hole external package と full-six-term package から
  `AtMostTwoHoleDepthBound` と `smallHoleLowerBound` を閉じる。

既存 public theorem 名は維持する。
-/
