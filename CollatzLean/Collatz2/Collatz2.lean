import CollatzLean.Collatz2.Core.Word
import CollatzLean.Collatz2.Core.AffineTransfer
import CollatzLean.Collatz2.Core.Realization
import CollatzLean.Collatz2.Core.Interval

import CollatzLean.Collatz2.Local.DeterminantSign
import CollatzLean.Collatz2.Local.Defect
import CollatzLean.Collatz2.Local.FirstCrossing
import CollatzLean.Collatz2.Local.SuffixDeterminantProfile

import CollatzLean.Collatz2.Orbit.Runs
import CollatzLean.Collatz2.Orbit.RealizationRecovery
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
import CollatzLean.Collatz2.ObstructionAudit.ExactWordTranslation
import CollatzLean.Collatz2.ObstructionAudit.CanonicalResidueAudit
import CollatzLean.Collatz2.ObstructionAudit.ExactTranslationConsequences
import CollatzLean.Collatz2.ObstructionAudit.FutureMinimumPrefixFloor

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

## Exact realization recovery

`RealizationRecovery` では、valid word の genuine affine realization が odd endpoint を持てば、
whole equation から一歩ごとの normalized boundary を復元して `Runs` を構成できることを示す。

従って

  valid word
    + exact `affineConst`
    + odd endpoint realization

は stepwise normalized dynamics を失っていない。

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

`BiCanonical` は新しい trajectory data ではなく二つの replay quotient の zero-layer 条件、
prepend-one は `[1]` と tail の defect cocycle の特殊化として扱う。

### Matrix axis

`Matrix` 層では `AffineTransfer` を新しい正本に置き換えず、
upper-triangular `2 x 2` integer matrix representation を derived view として用いる。

defect は oriented wedge、旧 center-comparison scalar `omega` は commutator の唯一の
非自明成分として現れる。

finite fixed point は homogeneous vector `(B, A-C)` として保持する。
composition では fixed-point vector は正係数線形結合で transport され、
`omega` は prefix 側で `A`、suffix 側で `C` により exact に scale する。

## Synthesis

`GlobalCenterEscape` と `MovingCenter` により eventually-negative tail では
strict center rise、すなわち `omega > 0` が cofinally 強制される。

`PrimitiveCenter` / `PrimitiveReturnGap` では

  h = gcd(B,G) = gcd(returnGap,G)
  returnGap = 4*h*s
  G = h*d
  gcd(s,d) = 1

へ primitive 化し、隣接 separation を

  kappa = d*A'*s' - d'*C*s

へ exact に戻す。

`SwapResidue` / `SwapCarry` / `KappaSwapValuation` では同じ `omega` を
canonical residue displacement、0/1 carry、2-adic separation へ接続する。

## Obstruction audit: exact-word boundary

relaxed audit では primitive arithmetic、positive `kappa`、center escape、
genuine diagonal `3^p / 2^H`、begins-one profile まで明示的 infinite model が存在する。

今回さらに境界を五段階に分離する。

1. `RealizationRecovery`:
   `Valid + Realizes + Odd endpoint -> Runs` を general theorem として固定する。

2. `ExactWordTranslation`:
   audit packet に

     `translate = Word.affineConst word`

   を追加する。これにより各 packet block は genuine `Word.Realizes` / `Runs` へ戻る。

3. `CanonicalResidueAudit`:
   exact translation より弱い

     `start % residueModulus(word) = canonicalStart(word)`

   だけを追加した relaxed packet は依然 inhabitant を持つことを明示する。

4. `ExactTranslationConsequences`:
   exact packet から replay coordinate、actual prefix canonical residue、
   affineConst split recursion、adjacent swap 0/1 carry を薄い consequence として抽出する。

5. `FutureMinimumPrefixFloor`:
   exact word realizability と別に、future-minimum block 固有の

     every actual prefix boundary >= block start

   を packet として分離する。actual `AdjacentTransferChain` では
   `FutureMinimumAt` から index-level prefix floor が自動的に成立する。

従って現在の audit の狙いは、exact word translation を一気に不存在化することではなく、
その genuine-word consequences と future-minimum floor を一枚ずつ戻し、
synthetic witness が初めて消える最小境界を特定することである。
-/
