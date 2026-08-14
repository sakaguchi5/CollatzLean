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

-- 一般補題
import CollatzLean.Collatz2.Canonical.EndpointFundamentalBound
import CollatzLean.Collatz2.Canonical.PositiveSuffixBudget
import CollatzLean.Collatz2.Canonical.ZeroCoreSlack
import CollatzLean.Collatz2.Canonical.Q0Deep

-- q=0 final core reduction
import CollatzLean.Collatz2.Global.EndpointFloorNaturalCoordinates
import CollatzLean.Collatz2.Canonical.PrefixBudgetExcess
import CollatzLean.Collatz2.Canonical.DualSigmaBudget
import CollatzLean.Collatz2.Canonical.BudgetGapDifference
import CollatzLean.Collatz2.Canonical.SuffixBudgetLinearLower
import CollatzLean.Collatz2.Canonical.ZeroCoreCanonicalSlacks
import CollatzLean.Collatz2.Canonical.PrependOneSwapSeparation
import CollatzLean.Collatz2.Canonical.ZeroCoreSwapDefect

-- q=0 dual-gap / nested-canonical corridor
import CollatzLean.Collatz2.Arithmetic.ExponentSlope
import CollatzLean.Collatz2.External.TwoThreeGap
import CollatzLean.Collatz2.External.TwoThreeEffectiveGap
import CollatzLean.Collatz2.Canonical.ZeroCoreDualGap
import CollatzLean.Collatz2.Canonical.ZeroCoreNestedCorridor

import CollatzLean.Collatz2.Global.AdjacentTransferChain
import CollatzLean.Collatz2.Global.AdjacentCanonical
import CollatzLean.Collatz2.Global.SignDichotomy
import CollatzLean.Collatz2.Global.UnboundedReduction
import CollatzLean.Collatz2.Global.CenterEscape
import CollatzLean.Collatz2.Global.MovingCenter
import CollatzLean.Collatz2.Global.PrimitiveCenter
import CollatzLean.Collatz2.Global.PrimitiveReturnGap

import CollatzLean.Collatz2.Global.InfiniteSurvival
import CollatzLean.Collatz2.Global.OddOrbitSurvivalBridge
import CollatzLean.Collatz2.Global.RightBranchFirstCrossing
import CollatzLean.Collatz2.Global.RightBranchZeroReplay
import CollatzLean.Collatz2.Global.RightBranchZeroReplayMatveev
import CollatzLean.Collatz2.Global.CanonicalAdjacentContractingReturn
import CollatzLean.Collatz2.Global.RightBranchAdjacentReduction
import CollatzLean.Collatz2.Global.CanonicalEndpointFloorContractingReturn
import CollatzLean.Collatz2.Global.RightBranchEndpointFloorClosure

-- Mountain / finite Hercher route (current A only; FutureMinimum endpoint 不使用)
import CollatzLean.Collatz2.Mountain.Block
import CollatzLean.Collatz2.Mountain.OneMountainExclusion
import CollatzLean.Collatz2.Mountain.FiniteHercher
import CollatzLean.Collatz2.Mountain.FiniteHercherNarrow
import CollatzLean.Collatz2.Arithmetic.HercherContinuedFractionCertificate
import CollatzLean.Collatz2.External.BarinaHercher
import CollatzLean.Collatz2.Mountain.BarinaHercherLower
import CollatzLean.Collatz2.Mountain.PolynomialStartBound
import CollatzLean.Collatz2.Mountain.PolynomialMountainLower

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

current A の正本は `CanonicalEndpointFloorContractingReturn`。
ここでは endpoint が FutureMinimum であることを仮定しない。

q=0 endpoint-floor obstruction から現在、

* natural coordinates
* prefix/suffix dual budget
* exact budget difference
* suffix budget linear lower bound
* true j=0 canonical fundamental slacks
* dual endpoint gap
* effective 2-3 linear gap
* nested canonical corridor
* mountain block / mountain decomposition
* one-mountain paradoxical return exclusion
* finite Hercher Lemma 8 / Lemma 20 integer core
* finite Hercher narrow inequality
* Barina `2^71` + Hercher continued-fraction denominator lower bound
* polynomial 2--3 gap からの stage-6 start upper bound
* mountain chain envelope と stage-7 binary mountain-count certificate

までを current A から切り出す。

特に stage 6 は `CanonicalZeroCoreData.exists_polynomialStartBoundData` により

  S+1 <= C*(p+1)^(A+1)

を得る。

stage 7 は mountain decomposition `Cmount` に対して

  p <= clog_2(C*(p+1)^(A+1)) * (2^mountainCount - 1)

という完全整数形へ圧縮する。
`mountainCount_gt_of_binaryCertificate` に有限整数 certificate を渡せば、
explicit 2--3 gap 定数から直ちに数値 mountain lower bound を得られる。

また external inputs

* `External.BarinaTwoPow71Input`
* `External.HercherTwoPow71DenominatorInput`

を入れると

`CanonicalEndpointFloorContractingReturn.oddSteps_ge_72057431991`

により cycle を仮定せず odd-step 数 `K >= 72057431991` を得る。

以前の `MinimalAdjacentCanonicalReturn` / `RotationCrossingTrap` は
endpoint FutureMinimum を追加で仮定する conditional packet であり、
current A の無条件正規ルートとしてはこの入口から外す。
-/
