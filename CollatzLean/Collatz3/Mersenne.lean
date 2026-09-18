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

actual `Runs` への接続は Bridge 層へ分離したままにする。
-/
