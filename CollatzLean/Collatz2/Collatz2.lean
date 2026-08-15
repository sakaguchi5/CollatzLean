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
import CollatzLean.Collatz2.Geometry.CyclicCenter
import CollatzLean.Collatz2.Geometry.RankPath
import CollatzLean.Collatz2.Geometry.RankUnit
import CollatzLean.Collatz2.Geometry.RankStrip
import CollatzLean.Collatz2.Geometry.RankQuotient
import CollatzLean.Collatz2.Geometry.ContractingPairDescent
import CollatzLean.Collatz2.Geometry.BestUpperSlope
import CollatzLean.Collatz2.Geometry.PrimitiveBestUpper
import CollatzLean.Collatz2.Geometry.WeightedRankSum
import CollatzLean.Collatz2.Geometry.WeightedRankFerrers
import CollatzLean.Collatz2.Geometry.WeightedRankBaseline
import CollatzLean.Collatz2.Geometry.ResidueIndexedFerrers

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

-- rank / cyclic geometry
import CollatzLean.Collatz2.Canonical.EndpointFloorCyclicGeometry
import CollatzLean.Collatz2.Canonical.EndpointFloorRankSeparation
import CollatzLean.Collatz2.Canonical.RotationRankTrap
import CollatzLean.Collatz2.Canonical.EndpointFloorTailRankTrap
import CollatzLean.Collatz2.Canonical.EndpointFloorBestUpperReduction
import CollatzLean.Collatz2.Canonical.EndpointFloorRecordDescent
import CollatzLean.Collatz2.Canonical.EndpointFloorRecordChain
import CollatzLean.Collatz2.Canonical.EndpointFloorWeightedRank
import CollatzLean.Collatz2.Canonical.EndpointFloorRankFerrers
import CollatzLean.Collatz2.Canonical.EndpointFloorFerrersInverse

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
endpoint FutureMinimum は仮定しない。

rank geometry では現在、従来の

* FirstCrossing rational chord rank
* `stripRank + p*extraDepth` decomposition
* unconditional tail-rank trap
* wide-strip denominator descent
* `BestUpperCertificate`

に加えて、次の三段を切り出す。

1. `StripReduced` と smaller-denominator best-upper slope の exact equivalence。
2. exponent pair の gcd primitive 化。contracting / slope / StripReduced を保存し、
   primitive+reduced では proper strip rank が `1,...,p-1` を一度ずつ取る。
3. primitive+reduced branch で current A の任意 proper cut から suffix crossing を再起動し、
   wide strip を排除して strict rank descent を得る。開始 rank が `p` 未満なら crossing block は

     twoSteps(block) = criticalHeight(length) + 1

   という minimal FirstCrossing block になり、interior endpoint は再び critical roof 上へ戻る。

Stage 3 の `NextRecordBlockData` は `EndpointFloorRecordChain` で rank strong induction により
terminal まで有限反復される。block lengths `r_i` について exact に

  1 + sum r_i = p
  1 + sum (criticalHeight(r_i)+1) = H
  d_1 = sum (p-stripRank(r_i))

まで telescope する。

また `WeightedRankSum` / `EndpointFloorWeightedRank` では primitive rank unit `u` により
translation path 全体を

  3*B = 3^p * sum u^(-d_k)     (mod G)

へまとめ、current A の small-residue equation と合わせて

  sum u^(-d_k) = 6*n           (mod G)

まで回収する。

さらに `RankQuotient` / `WeightedRankFerrers` では original word 上で

  d_k = rankResidue(k) + p*rankQuotient(k)
  rankResidue(k) = stripRank(k) % p
  rankQuotient(k) = stripRank(k)/p + extraDepth(k)

を exact に保持する。従って wide strip は descendant modulus へ移らず original word の
positive rank quotient として残る。

primitive slope では proper rank residues は `1,...,p-1` を一度ずつ取り、weighted sum は

  W = 1 + proper permutation-weighted half-depth sum

および

  W = baselineResidueSum + (halfUnitValue-1)*ferrersCellSum

へ exact に書き換えられる。`EndpointFloorRankFerrers` はこれを current A の

  W = 6*n

へ直接接続する。従って reduced / nonreduced の両方を original weighted residue 上の
一つの quotient-depth profile として扱える。

さらに `WeightedRankBaseline` / `ResidueIndexedFerrers` では primitive residue permutation を
完全に消去して

  baselineResidueSum = 1 + v + ... + v^(p-1)
  (v-1)*baselineResidueSum = halfUnitValue-1

を得る。また inverse permutation `residueCut` により

  q_r = rankQuotient(residueCut(r))

という residue-indexed quotient profile を構成し、proper cut の quotient/weight はその profile
から exact に復元される。

`EndpointFloorFerrersInverse` は `W=6*n`, baseline identity, `2*half=1` を消去し、primitive
current A に対して rank unit `R` が存在して exact に

  (1-v) * (ferrersCellSum + 12*n) = 1    (mod G)

を満たすところまで圧縮する。

初期 cut `a=1` については primitive+reduced branch で

  0 < d_1 < p
  7*p < 12*d_1

を保持する。

また external inputs

* `External.BarinaTwoPow71Input`
* `External.HercherTwoPow71DenominatorInput`

を入れると
`CanonicalEndpointFloorContractingReturn.oddSteps_ge_72057431991`
により cycle を仮定せず odd-step 数の既存下界を得る。
-/
