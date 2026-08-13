import CollatzLean.Collatz2.Core.Word
import CollatzLean.Collatz2.Core.AffineTransfer
import CollatzLean.Collatz2.Core.Realization
import CollatzLean.Collatz2.Core.Interval

import CollatzLean.Collatz2.Local.DeterminantSign
import CollatzLean.Collatz2.Local.Defect
import CollatzLean.Collatz2.Local.FirstCrossing
import CollatzLean.Collatz2.Local.SuffixDeterminantProfile

import CollatzLean.Collatz2.Orbit.Runs
import CollatzLean.Collatz2.Orbit.OddOrbit
import CollatzLean.Collatz2.Orbit.FutureMinimum
import CollatzLean.Collatz2.Orbit.FutureMinimumArithmetic
import CollatzLean.Collatz2.Orbit.FutureMinimumSelection

import CollatzLean.Collatz2.Canonical.ResidueClass
import CollatzLean.Collatz2.Canonical.Representative
import CollatzLean.Collatz2.Canonical.Replay
import CollatzLean.Collatz2.Canonical.ReplayExtremality

import CollatzLean.Collatz2.Global.AdjacentTransferChain
import CollatzLean.Collatz2.Global.SignDichotomy
import CollatzLean.Collatz2.Global.UnboundedReduction

-- Native axis
import CollatzLean.Collatz2.Native.IntervalReplay
import CollatzLean.Collatz2.Native.BiCanonical
import CollatzLean.Collatz2.Native.PrependOneDefect
import CollatzLean.Collatz2.Native.ReplayDynamics
import CollatzLean.Collatz2.Native.AdjacentPrependOne

-- Matrix axis
import CollatzLean.Collatz2.Matrix.Representation
import CollatzLean.Collatz2.Matrix.DefectGeometry
import CollatzLean.Collatz2.Matrix.Commutator
import CollatzLean.Collatz2.Matrix.FixedPoint
import CollatzLean.Collatz2.Matrix.CenterTransport
import CollatzLean.Collatz2.Matrix.ProjectiveDynamics

-- Native / Matrix synthesis
import CollatzLean.Collatz2.Synthesis.CenterComparison
import CollatzLean.Collatz2.Synthesis.GlobalCenterEscape
import CollatzLean.Collatz2.Synthesis.MovingCenter
import CollatzLean.Collatz2.Synthesis.PrimitiveCenter
import CollatzLean.Collatz2.Synthesis.GlobalPrimitiveCenter
import CollatzLean.Collatz2.Synthesis.SwapResidue
import CollatzLean.Collatz2.Synthesis.SwapCarry
import CollatzLean.Collatz2.Synthesis.PrimitiveReturnGap
import CollatzLean.Collatz2.Synthesis.KappaSwapValuation

-- Audit
import CollatzLean.Collatz2.ObstructionAudit.ObstructionAudit

set_option linter.style.header false

/-!
# Collatz2

旧 `CollatzLean.Collatz.*` を import しない独立再構築の入口。

Collatz2 では、有限語・actual run・無限軌道に含まれる情報をできるだけ
lossless な少数の正本 object に保持し、従来の特殊 branch や座標は
Prop / projection / characterization theorem として下流で導く。

## Shared foundation

有限側の正本は `Word`、`AffineTransfer`、`Realizes`、`Runs`、`Interval` である。

`AffineTransfer` は

  `A * y = C * x + B`

という exact affine relation を保持し、word append は transfer composition と一致する。

Expanding / Contracting は primitive branch とせず、
transfer の signed determinant `C - A` の正負として導く。

signed defect により actual displacement を

  `startDefect = A * (y - x)`

として測り、PositiveReturn は positive defect のコロラリーとして扱う。

FirstCrossing は prefix determinant sign profile、
AllSuffixesContracting は suffix determinant sign profile として再構成する。

## Canonical / Replay geometry

odd endpoint を持つ realization の start が属する合同類を先に構成し、
その最小非負代表として `canonicalStart` を定義する。

normalized `Runs` の endpoint odd から `ReplayCoordinate` を追加仮定なしで構成する。

contracting transfer では replay displacement が

  canonical displacement
    + 2 * determinant * quotient

と exact に変化するため、`q = 0` は replay family の最大 displacement layer となる。

従って旧 `j = 0` 型の canonical positive return は primitive branch ではなく、
contracting replay extremality のコロラリーとして現れる。

`ReplayDynamics` では replay quotient を canonical residue modulus に対する自然な商として読み、
word extension による binary right shift と ternary digit decomposition を導く。

## Global unbounded reduction

normalized `OddOrbit` と future minima から、
隣接 future-minimum 間の lossless `AdjacentTransferChain` を構成する。

各 adjacent block は actual `Runs` と positive return を持ち、
valid nonempty なので determinant は非零である。

sign profile の強い global dichotomy は

  positive determinant cofinal
    ∨ eventually negative determinant

である。従来の

  positive determinant cofinal
    ∨ negative determinant cofinal

はその corollary として残す。

`FutureMinimumArithmetic` では Matrix に依存せず、future minimum `x > 1` から
first exponent `1`、`x = 4k+3`、adjacent value gap の正の4倍性を導く。

## Two research axes

shared foundation の上で二つの独立した解析軸を並走させる。

### Native axis

`Native` 層では行列表現を用いず、
既存の affine coefficients・interval・replay・defect を直接解析する。

現在は `IntervalReplay`、`BiCanonical`、`PrependOneDefect`、`ReplayDynamics` を持つ。

`BiCanonical` は新しい trajectory data ではなく二つの replay quotient の zero-layer 条件、
prepend-one は `[1]` と tail の defect cocycle の特殊化として扱う。

### Matrix axis

`Matrix` 層では `AffineTransfer` を新しい正本に置き換えず、
upper-triangular `2 x 2` integer matrix representation を derived view として用いる。

matrix multiplication は `AffineTransfer.followedBy` と exact に対応する。
defect は oriented wedge、旧 center-comparison scalar `omega` は commutator の唯一の
非自明成分として現れる。

finite fixed point は homogeneous vector `(B, A-C)` として保持する。
composition では fixed-point vector は正係数線形結合で transport され、
`omega` は prefix 側で `A`、suffix 側で `C` により exact に scale する。

## Synthesis

`Synthesis` 層だけが Native / Matrix / Global の見方を合流させる。

`CenterComparison` では

  same center
    ↔ fixed-point vectors are projectively proportional
    ↔ omega = 0
    ↔ transfer matrices commute

を示す。

`GlobalCenterEscape` では negative adjacent positive return の finite center が
actual endpoint より右にあり、negative blocks の centers が cofinally infinity へ逃げることを示す。

`MovingCenter` では stronger dichotomy の eventually-negative tail を利用し、
隣接 center の strict rise と `omega > 0` を同一視する。shared future-minimum boundary を消去して

  omega_n
    = G_n * A_(n+1) * delta_(n+1)
      - G_(n+1) * C_n * delta_n

を得る。centers が infinity へ逃げるため、eventually negative branch では
`omega_n > 0` が cofinally 強制される。

`PrimitiveCenter` では fixed-point vector content を

  h = gcd(B,G) = gcd(delta,G)

として actual gap から導き、primitive center を

  b / d = 3 + 4 * alpha / d

へ正規化する。隣接 center-rise event では

  omega_n = 4 * h_n * h_(n+1) * kappa_n,
  kappa_n >= 1

となる。従って `kappa = 0` を negative divergence の top-level branch に置く必要はない。

`GlobalPrimitiveCenter` ではこれらを global に接続し、eventually-negative branch から

  Cofinal (fun n => 1 <= primitiveKappa_n)

を直接導く。従って primitive changing-center arithmetic は元の adjacent chain 上で
cofinally 強制される。

`SwapResidue` では同じ `omega` が word order swap の translation difference であり、
さらに odd-start canonical residue の exact displacement を測ることを示す。

`SwapCarry` ではその ZMod displacement の最小非負代表を取り、actual canonical starts に対して

  canonicalStart(v++u) + displacement
    = canonicalStart(u++v) + carry * residueModulus(u++v)

を exact に導く。両 representative と displacement は common modulus 未満なので
`carry` は必ず `0` または `1` である。

これにより center / commutator / primitive arithmetic と canonical / carry 側を
同じ obstruction scalar `omega` で接続する。

Matrix axis は Native axis の代替ではない。
Matrix axis で構造を発見し、その本質を affine / integer statement に翻訳して
Native axis へ戻す、という二軸の研究を続ける。
-/
