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

-- Matrix axis
import CollatzLean.Collatz2.Matrix.Representation
import CollatzLean.Collatz2.Matrix.DefectGeometry
import CollatzLean.Collatz2.Matrix.Commutator
import CollatzLean.Collatz2.Matrix.FixedPoint

-- Native / Matrix synthesis
import CollatzLean.Collatz2.Synthesis.CenterComparison




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

## Global unbounded reduction

normalized `OddOrbit` と future minima から、
隣接 future-minimum 間の lossless `AdjacentTransferChain` を構成する。

各 adjacent block は actual `Runs` と positive return を持ち、
valid nonempty なので determinant は非零である。

従って global branch は determinant sign profile の purely combinatorial な
cofinal dichotomy

  positive determinant cofinal
    ∨ negative determinant cofinal

から生じる。

Expanding cofinal / Contracting cofinal はこの sign dichotomy の別名にすぎない。

negative determinant block では actual positive return と replay extremality を合わせることで、
canonical (`q = 0`) positive return が自動的に導かれる。

## Two research axes

ここから先は shared foundation を変更せず、二つの独立した解析軸を並走させる。

### Native axis

`Native` 層では行列表現を用いず、
既存の affine coefficients・interval・replay・defect を直接解析する。

現在は、

  `IntervalReplay`
  `BiCanonical`
  `PrependOneDefect`

を導入している。

`IntervalReplay` は whole run の lossless interval decomposition から
各 subrun の replay coordinate を導く。

`BiCanonical` は新しい trajectory data ではなく、
二つの replay quotient がともに `0` であるという薄い canonicality condition として扱う。

prepend-one も専用の巨大な branch data を置かず、
`[1]` と tail の transfer composition に対する defect cocycle の特殊化として扱う。

### Matrix axis

`Matrix` 層では `AffineTransfer` を新しい正本に置き換えず、
その upper-triangular `2 x 2` matrix representation を derived view として用いる。

  `Representation`
  `DefectGeometry`
  `Commutator`
  `FixedPoint`

を導入する。

matrix multiplication は `AffineTransfer.followedBy` と exact に対応する。

defect は matrix action に対する oriented determinant / wedge として解釈される。

二 transfer の非可換性は commutator の唯一の非自明成分に集約され、
従来の center-comparison scalar に対応する量が matrix commutator として現れる。

fixed point は division を primitive にせず、
homogeneous fixed-point vector

  `(B, A - C)`

として扱う。

これにより fixed-point geometry、common center、commutation を
整数係数のまま比較できる。

## Synthesis

`Synthesis` 層だけが Native / Matrix の両方の見方を比較する。

現在の `CenterComparison` では、

  same center
    ↔ fixed-point vectors are projectively proportional
    ↔ center wedge is zero
    ↔ commutator scalar is zero
    ↔ transfer matrices commute

という対応を明示する。

したがって Matrix axis は Native axis の代替ではない。

Matrix axis で構造を発見し、
必要ならその本質を affine / integer statement に翻訳して Native axis へ戻す、
という二軸の研究を行う。
-/
