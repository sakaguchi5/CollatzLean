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
import CollatzLean.Collatz3.Mersenne.NoHoleProof
import CollatzLean.Collatz3.Mersenne.NoHoleSourceOneProof
import CollatzLean.Collatz3.Mersenne.NoHoleMersenneQuotientProof
import CollatzLean.Collatz3.Mersenne.NoHoleMersenneQuotientDerived
import CollatzLean.Collatz3.Mersenne.SmallHoleExitDepth
import CollatzLean.Collatz3.Mersenne.TailLoopModular

/-!
# Collatz3 Mersenne

Mersenne block の純粋整数算術、one-zero family、fixed `(d,r)` affine lift、
one-zero obstruction の三領域 reduction、および bounded defect からの sparse equation をまとめる。
さらに、一般 `BlockData` について source coefficient / target の bounded defect を
固定項数 `{2,3}`-unit obstruction へ送る qualitative route と、source 本体の defect を
coefficient へ移す bridge も含む。

定量層では exponent 上界関数 `F(N)` を主役にせず、BlockData から得られる exact equation

`-1 - 3^k + 2^n 3^k - 3^k S + 2^r T + 2^r - 2^(L+r) = 0`

を保持し、source/target の hole 数を depth `k` の関数として直接下から抑える。
将来 `G(k) ≍ log k / log log k` のような lower bound が得られれば、
そのまま binary defect 下界へ戻せる設計になっている。

small-hole 層では exact equation の well-formedness を保持し、hole 0/1/2 を
0,1,2 個の dyadic correction を持つ正規形へ exact に分解する。
さらに `ZMod` 上の period certificate に加えて tail/loop certificate を導入し、
低い exponent を exact に保持した finite modular lifting を可能にする。

no-hole 層では mod 3 / mod 8 の elementary constraints、`ord_(2^r)(3)`、
Mersenne modulus 上の `2` の exact order、geometric-sum 分解、mod 9 を組み合わせ、
二つの residual をともに排除する。
したがって `NoHoleCompleteClassification` は無条件に閉じ、hole 0 の解は
既知の四つだけとなる。

small-hole exit-depth 層では mod 4 / mod 8 だけで決まる non-resonant branch の `r` を
exact に固定し、odd `k` の source hole `a=2` や even `k` の source-two holes `(1,2)`
といった低位 resonance を後段の tail/loop sieve へ明示的に残す。

actual `Runs` への接続は Bridge 層へ分離したままにする。
-/
