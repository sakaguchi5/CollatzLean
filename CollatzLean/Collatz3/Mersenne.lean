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
import CollatzLean.Collatz3.Mersenne.OneHoleFiniteTailLoopSieve
import CollatzLean.Collatz3.Mersenne.OneHoleFiniteLift65536
import CollatzLean.Collatz3.Mersenne.OneHoleThreeTailLargeDepth
import CollatzLean.Collatz3.Mersenne.OneHoleSourceResidualProof
import CollatzLean.Collatz3.Mersenne.TargetOneHoleGeometric
import CollatzLean.Collatz3.Mersenne.TargetOneHoleValuation
import CollatzLean.Collatz3.Mersenne.TargetOneHoleGcd
import CollatzLean.Collatz3.Mersenne.TargetOneHoleLocks
import CollatzLean.Collatz3.Mersenne.TargetOneHolePrimitive
import CollatzLean.Collatz3.Mersenne.TargetOneHoleBase64Descent

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

one-hole finite sieve の第1段では `M₂=2^7*5*17*257` で `k mod 256` を絞る。
第2段では `M₃=2^8*5*17*257*65537` へ survivor class だけを lift し、
source resonance `a=2` を14個、target low-source `n=1,2` を10個の
`mod 65536` class に絞る。

第3段では `3^6` を含む `M₄=3^6*7*19*73*163*487` を使い、`k≥6` を
3-adic tail state として扱う。これにより source `a=2` と target `n=1,2` の
large-depth branch を完全排除し、source-one の残りを even `k`, `a≥3`, `r=1`、
target-one の残りを `n≥3` の parity-controlled exit-depth branch へ局所化する。

source-one の最後の residual S では、low-bit congruence から `2^(a-2) ∣ k`、
`3^k ∣ 2^(L+1)-1` から `2*3^(k-1) ∣ L+1` を導く。
前者と元の等式から得る線形上界 `L+1 < 5k+3` と、後者の指数的下界を衝突させ、
well-formed source-one について無条件に `k≤5` を得る。

target-one の残りでは `mod (2^n-1)` の residue rigidity から
`n ∣ b+r`, `n ∣ L` を導き、`b+r=nq`, `L=nt` として

`3^k + G_q(2^n) = 2^r G_t(2^n)`

へ exact に落とす。`q=t` は既存 no-hole 完全分類へ戻るため large-depth では消える。
`q<t` では 2-adic valuation により `n` が `v₂(k)` または `v₂(k-1)` から exact に決まり、
さらに `gcd(q,t)>1` は no-hole 分類から例外形 `n=3, gcd(q,t)=2` に局所化される。

新しい lock 層では同じ `q<t` geometric equation を base `2^n` の二 block normal form として
読み直す。最上位位置は `Critical.beattyIndex k = r+n(t-1)` に exact に固定され、
切替位置は

`v₂((2^n-1)3^k + (2^r-1)) = nq`

として exact に復元される。primitive `gcd(q,t)=1` branch ではさらに even 側の `n` は even、
odd 側では `n ≡ 3 (mod 6)` が排除される。唯一の non-primitive branch
`n=3, gcd(q,t)=2` は `G_(2m)(8)=9G_m(64)` により base 64 の primitive equation へ descent する。

actual `Runs` への接続は Bridge 層へ分離したままにする。
-/
