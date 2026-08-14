import CollatzLean.Collatz2.Core.Word
import CollatzLean.Collatz2.Core.AffineTransfer
import CollatzLean.Collatz2.Core.DisplacementForm
import CollatzLean.Collatz2.Core.TranslationPath
import CollatzLean.Collatz2.Core.Realization
import CollatzLean.Collatz2.Core.Interval

import CollatzLean.Collatz2.Local.DeterminantSign
import CollatzLean.Collatz2.Local.Defect
import CollatzLean.Collatz2.Local.FirstCrossing
import CollatzLean.Collatz2.Local.SuffixDeterminantProfile
import CollatzLean.Collatz2.Local.TranslationDeterminant
import CollatzLean.Collatz2.Local.ContractingClosure

import CollatzLean.Collatz2.Orbit.Runs
import CollatzLean.Collatz2.Orbit.RunDefect
import CollatzLean.Collatz2.Orbit.RealizationRecovery
import CollatzLean.Collatz2.Orbit.OddOrbit
import CollatzLean.Collatz2.Orbit.FutureMinimum
import CollatzLean.Collatz2.Orbit.FutureMinimumArithmetic
import CollatzLean.Collatz2.Orbit.FutureMinimumSelection

import CollatzLean.Collatz2.Geometry.Center
import CollatzLean.Collatz2.Geometry.PrimitiveForm

import CollatzLean.Collatz2.Canonical.ResidueClass
import CollatzLean.Collatz2.Canonical.Representative
import CollatzLean.Collatz2.Canonical.CenterResidue
import CollatzLean.Collatz2.Canonical.Replay
import CollatzLean.Collatz2.Canonical.ReplayExtremality
import CollatzLean.Collatz2.Canonical.SwapResidue
import CollatzLean.Collatz2.Canonical.SwapCarry
--一般補題
import CollatzLean.Collatz2.Canonical.EndpointFundamentalBound
import CollatzLean.Collatz2.Canonical.PositiveSuffixBudget
import CollatzLean.Collatz2.Canonical.ZeroCoreSlack
import CollatzLean.Collatz2.Canonical.Q0Deep

import CollatzLean.Collatz2.Global.AdjacentTransferChain
import CollatzLean.Collatz2.Global.AdjacentCanonical
import CollatzLean.Collatz2.Global.SignDichotomy
import CollatzLean.Collatz2.Global.UnboundedReduction
import CollatzLean.Collatz2.Global.CenterEscape
import CollatzLean.Collatz2.Global.MovingCenter
import CollatzLean.Collatz2.Global.PrimitiveCenter
import CollatzLean.Collatz2.Global.PrimitiveReturnGap
--
import CollatzLean.Collatz2.Global.InfiniteSurvival
import CollatzLean.Collatz2.Global.OddOrbitSurvivalBridge
import CollatzLean.Collatz2.Global.RightBranchFirstCrossing
import CollatzLean.Collatz2.Global.RightBranchZeroReplay
import CollatzLean.Collatz2.Global.RightBranchZeroReplayMatveev
import CollatzLean.Collatz2.Global.CanonicalAdjacentContractingReturn
import CollatzLean.Collatz2.Global.RightBranchAdjacentReduction
import CollatzLean.Collatz2.Global.CanonicalEndpointFloorContractingReturn
import CollatzLean.Collatz2.Global.RightBranchEndpointFloorClosure

-- Native: word/run 固有の特殊化
import CollatzLean.Collatz2.Native.IntervalReplay
import CollatzLean.Collatz2.Native.BiCanonical
import CollatzLean.Collatz2.Native.PrependOneDefect
import CollatzLean.Collatz2.Native.ReplayDynamics
import CollatzLean.Collatz2.Native.AdjacentPrependOne

-- Matrix: derived representation view のみ
import CollatzLean.Collatz2.Matrix.Representation
import CollatzLean.Collatz2.Matrix.DefectGeometry
import CollatzLean.Collatz2.Matrix.Commutator
import CollatzLean.Collatz2.Matrix.FixedPoint
import CollatzLean.Collatz2.Matrix.CenterTransport
import CollatzLean.Collatz2.Matrix.ProjectiveDynamics

-- primitive separation の arithmetic shadows
import CollatzLean.Collatz2.Arithmetic.KappaSwapValuation
import CollatzLean.Collatz2.Arithmetic.KappaBoundarySignature
import CollatzLean.Collatz2.Arithmetic.TwoThreeSmallGap
import CollatzLean.Collatz2.External.MatveevInput

-- Obstruction audit
import CollatzLean.Collatz2.ObstructionAudit.ObstructionAudit
import CollatzLean.Collatz2.ObstructionAudit.ExactWordTranslation
import CollatzLean.Collatz2.ObstructionAudit.CanonicalResidueAudit
import CollatzLean.Collatz2.ObstructionAudit.ExactTranslationConsequences
import CollatzLean.Collatz2.ObstructionAudit.FutureMinimumPrefixFloor
import CollatzLean.Collatz2.ObstructionAudit.TranslationShadowAudit


set_option linter.style.header false

/-!
# Collatz2

旧 `CollatzLean.Collatz.*` を import しない独立再構築の入口。

Collatz2 の設計原則は、trajectory-specific な branch data を増やさず、
lossless な少数の正本 object と、その universal projection から特殊概念を導くことである。

## 1. Lossless finite foundation

有限側の正本は

* `Word`
* `AffineTransfer`
* `Realizes`
* `Runs`
* `Interval`

である。

`AffineTransfer T = (C,A,B)` は

  `A * y = C * x + B`

を保持する。word append は transfer composition と exact に一致し、
`AffineTransfer` は最後まで lossless finite object のまま残す。

## 2. Universal B-sensitive interface: displacement form

`B` を単独の座標として解析せず、transfer から一つの整数一次式

  `Δ_T(X) = B + (C-A) X`

を導く。これが `DisplacementForm` であり、B-sensitive な解析の共通 interface である。

* constant term = `B`
* slope = `determinant = C-A`
* evaluation = defect
* projective root = finite center
* coefficient content = primitive center content
* pairwise resultant = separation

composition では

  `Δ_(T followedBy U) = C_U * Δ_T + A_T * Δ_U`

が exact に成立する。従って translation law と determinant law は、
別々の公式ではなく一つの displacement-form transport law の二成分である。

## 3. Genuine word translation path

arbitrary affine transfer では `B` は自由であるが、genuine word では

  `B = Word.affineConst w`

に固定される。

`TranslationPath` は append recursion を translation cocycle として読むだけでなく、
`B` を prefix two-depth / suffix odd-depth に沿う path terms へ展開する。

valid nonempty word では `B` は odd であり、

  `(oddSteps, twoSteps, affineConst)`

は valid word 自身を一意に復号する lossless code になる。
また二 translation の差では

* common prefix -> `2^twoSteps(prefix)` divisibility
* common suffix -> `3^oddSteps(suffix)` divisibility

が exact に現れる。これは separation / word swap の左右 boundary tomography の基礎になる。

さらに universal Archimedean shadow

  `B < A * C`

も保持する。

## 4. Local sign, displacement, and determinant integrals

`Expanding` / `Contracting` は primitive word classification ではなく
`Δ_T` の slope `C-A` の正負である。

start defect は

  `startDefect T x = Δ_T(x)`

そのもの。realization `x -> y` 上では

  `Δ_T(x) = A * (y-x)`
  `Δ_T(y) = C * (y-x)`

となるため、positive return / descent は displacement-form evaluation の符号の
corollary になる。

さらに translation path と determinant profile は exact に

  `suffixDeterminantIntegral = 3*B - p*A`
  `prefixDeterminantIntegral = p*C - 3*B`

で接続される。

従って

  `AllSuffixesContracting -> 3*B < p*A`

および proper-prefix positive profile から

  `3*B <= p*C`

が sign corollary として得られる。length `> 1` の FirstCrossing では後者は strict。

## 5. Synthesis 層を介さない center geometry

finite center は `Δ_T(X)=0` の projective root であり、最初から有理除算しない。
negative branch では `G=A-C>0` として coefficient pair `(B,G)` を使う。

二 transfer の signed root separation は

  `separation(T,U)
     = B_T * determinant(U) - B_U * determinant(T)`

である。

旧 `omega` は primitive object ではなく、この separation の Matrix compatibility alias に
降格する。

* `SameCenter <-> separation = 0`
* `CenterRises <-> separation > 0`
* Matrix commutator upper-right = separation
* fixed-point-vector wedge = `-separation`

となる。

従って旧 `Synthesis` directory は不要であり、一般幾何は `Geometry`、
actual chain の幾何は `Global`、canonical arithmetic は `Canonical`、
valuation / boundary arithmetic は `Arithmetic` に正規配置する。

## 6. Canonical representatives are local root shadows

`oddStartClass` / `canonicalStart` の total definition は従来どおり保持する。
その上で valid nonempty genuine word では、canonical start/end が同じ
`DisplacementForm` root の二つの local shadows であることを導く。

* start side: displacement evaluation is divisible by `2*A`
* endpoint side: displacement evaluation is divisible by `2*C`

`ReplayCoordinate` はこの root-shadow pair の simultaneous lift coordinate である。
高位概念名 `CenterLiftCoordinate` は semantic alias として与える。

contracting word では quotient を上げるほど displacement が slope に従って減少するため、
`q=0` は maximal positive-return layer として導かれる。旧 `j=0` は primitive branch ではない。

## 7. Matrix layer is representation only

Matrix は新しい正本ではない。

  `[[C,B],[0,A]]`

は `AffineTransfer` の homogeneous representation にすぎない。

fixed-point vector、wedge、commutator、center-vector transport はすべて
`DisplacementForm` の root / resultant / composition law の matrix shadows として置く。

## 8. Global adjacent future-minimum chain

非有界 odd orbit から `AdjacentTransferChain` を構成し、各 adjacent block に
actual `Runs`, positive return, genuine word transfer を保持する。

chain-derived API は本来の

  `Collatz2.AdjacentTransferChain`

namespace に直接置く。そのため

  `C.returnGap`
  `C.separationAdjacent`
  `C.centerContent`
  `C.primitiveKappa`

の dot notation が正規に使える。

strong global sign dichotomy は従来どおり

  positive determinant cofinal
    OR
  eventually negative determinant

である。

negative tail では center roots が cofinally infinity へ逃げることと center-order
transitivity から、positive adjacent separation が cofinally 強制される。

## 9. Primitive negative-root arithmetic

negative transfer の displacement form

  `Δ(X)=B-GX`

を `h=gcd(B,G)` で primitive 化する。
generic `PrimitiveForm` では

  `B = h*b`
  `G = h*d`

と primitive root separation を扱う。

future-minimum chain へ specialization すると

  `returnGap = 4*h*s`
  `b = 3*d + 4*alpha`

となり、adjacent separation は

  `separationAdjacent = 4*h*h'*kappa`

へ factorize する。

`PrimitiveReturnGap` はさらに

  `kappa = d*A'*s' - d'*C*s`

へ戻す。

## 10. Swap / carry / valuation are arithmetic shadows of separation

word swap `u++v` と `v++u` は diagonal coefficients を共有し、translation difference は
transfer separation そのものになる。

そこから

  separation
    -> canonical residue displacement
    -> minimal representative
    -> 0/1 carry
    -> primitive `kappa` valuation

という一本の経路を持つ。

`kappa=1` では adjacent separation の 2-adic depth が exact に `2`。
translation-difference の common-prefix divisibility と actual future-minimum head `1` を合わせると、
adjacent words は 2番目 exponent で必ず分岐し、その一方が exactly `1` になる。

また negative block の center content は `3` と互いに素なので、`kappa=1` separation は
modulo `3` で非零。translation path の terminal shadow と合わせると、adjacent words の
terminal exponents は opposite parity を持つ。

従って primitive `kappa=1` は単なる小さい整数 obstruction ではなく、
word の左右 boundary に rigid な symbolic signature を持つ。

## 11. Exact realization recovery

`RealizationRecovery` は重要な lossless boundary theorem である。

  valid word
    + genuine affine realization
    + odd endpoint
      -> normalized `Runs`

従って exact `affineConst` は単なる数値等式ではなく、stepwise normalized dynamics を
回復するだけの情報を保持する。

## 12. Obstruction audit by displacement shadows

relaxed audit では translation を free にした model を明示し、どの genuine-word shadow で
初めて synthetic witness が消えるかを監査する。

canonical start residue だけでは witness は残る。しかし exact translation の前にも

* endpoint-side translation congruence modulo `2*C`
* genuine translation path-size bound `B < A*C`

という薄い shadow があり、現在の canonical-residue witness はすでにそこで消える。

今後の audit は

  diagonal profile
    -> local root / translation shadows
    -> path-size / path-recursion shadows
    -> exact genuine `B`
    -> recovered `Runs`
    -> future-minimum prefix floor

という順に、失われた情報を一枚ずつ戻す。
-/
