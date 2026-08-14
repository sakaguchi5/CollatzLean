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
import CollatzLean.Collatz2.Global.MinimalAdjacentCanonicalReturn
import CollatzLean.Collatz2.Canonical.RotationCrossingTrap

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

q=0 endpoint-floor obstruction は現在、

* natural coordinates
* prefix/suffix dual budget
* exact budget difference
* suffix budget linear lower bound
* true j=0 canonical fundamental slacks
* prepend-one cyclic swap separation
* exact swap/core-defect identity
* dual endpoint gap
* effective 2-3 linear gap
* nested canonical corridor
* A-minimality provenance を保持する `MinimalAdjacentCanonicalReturn`
* future-minimum endpoint による actual cyclic rotation
* terminal/interior を区別した rotation crossing trap

まで lossless に整理される。

`TwoThreeEffectiveGapInput` と `TwoThreeGapPolynomialBound` は
旧系と同じ外部整数論 input を Collatz2 側へ再定義した純粋 Prop interface。

long corridor は

`CanonicalZeroCoreData.exists_longNestedCanonicalCorridor_rule`

に加え、

`CanonicalZeroCoreData.exists_logarithmicLongNestedCanonicalCorridor`

で `q = log_3(sigma*K*(p+1)^A)+1` を明示的に選び、
最後 `q` 文字を除く depth `m-q` までの全 suffix canonicality を与える。

さらに `MinimalAdjacentCanonicalReturn` は current A の最短 candidate provenance を保持し、
B1 zero-core と endpoint future-minimum を同じ packet に載せる。
そこから `RotationCrossingTrap` が必ず存在し、crossing endpoint `Y` は lossless に

  T <= Y < s

へ閉じ込められる。proper interior crossing なら strict に `T < Y < s`、
terminal crossing なら `Y = T`。

この二枝をまとめて排除する最終局所 principle が `NoRotationCrossingTrap`。
-/
