import CollatzLean.Collatz3.Arithmetic.Pow23
import CollatzLean.Collatz3.Arithmetic.Signed
import CollatzLean.Collatz3.Arithmetic.ModTwoPow

import CollatzLean.Collatz3.Core.Word
import CollatzLean.Collatz3.Core.PrefixDepth
import CollatzLean.Collatz3.Core.AffineTransfer
import CollatzLean.Collatz3.Core.WordTransfer
import CollatzLean.Collatz3.Core.WordScale
import CollatzLean.Collatz3.Core.PrefixAffine
import CollatzLean.Collatz3.Core.EndpointEquation

import CollatzLean.Collatz3.Canonical.AffineDataResidue
import CollatzLean.Collatz3.Canonical.AffineDataREQ
import CollatzLean.Collatz3.Canonical.OddEndpointResidue
import CollatzLean.Collatz3.Canonical.REQ
import CollatzLean.Collatz3.Canonical.LiftClassification

import CollatzLean.Collatz3.Semantics.OddStep
import CollatzLean.Collatz3.Semantics.Runs
import CollatzLean.Collatz3.Semantics.Reachability
import CollatzLean.Collatz3.Semantics.Predecessor
import CollatzLean.Collatz3.Semantics.Sufficiency
import CollatzLean.Collatz3.Semantics.ReachOne
import CollatzLean.Collatz3.Semantics.ReachOneMerge
import CollatzLean.Collatz3.Semantics.OrbitReturn
import CollatzLean.Collatz3.Semantics.PeriodicOrbit
import CollatzLean.Collatz3.Semantics.OddOrbit
import CollatzLean.Collatz3.Semantics.OrbitFate
import CollatzLean.Collatz3.Semantics.FiniteOrbitFate
import CollatzLean.Collatz3.Semantics.FutureMinimum
import CollatzLean.Collatz3.Semantics.StandardFutureMinimum
import CollatzLean.Collatz3.Semantics.OrbitFateFutureMinimum
import CollatzLean.Collatz3.Semantics.OrbitDerived

import CollatzLean.Collatz3.Combinatorics.WordRepetition
import CollatzLean.Collatz3.Combinatorics.YoungFerrers
import CollatzLean.Collatz3.Combinatorics.Record
import CollatzLean.Collatz3.Combinatorics.RecordDerived

import CollatzLean.Collatz3.FixedFiber.UniversalExcess
import CollatzLean.Collatz3.FixedFiber.PrependExcess

import CollatzLean.Collatz3.Critical.Beatty
import CollatzLean.Collatz3.Critical.BeattyCarry
import CollatzLean.Collatz3.Critical.BestUpperWidth
import CollatzLean.Collatz3.Critical.FirstPassage
import CollatzLean.Collatz3.Critical.Profile
import CollatzLean.Collatz3.Critical.ProfileAffine
import CollatzLean.Collatz3.Critical.ProfileCanonical
import CollatzLean.Collatz3.Critical.ProfileExtraction
import CollatzLean.Collatz3.Critical.Ferrers
import CollatzLean.Collatz3.Critical.WordFerrers
import CollatzLean.Collatz3.Critical.WordProfileEquiv
import CollatzLean.Collatz3.Critical.RoofAnchor
import CollatzLean.Collatz3.Critical.RecordSkeleton
import CollatzLean.Collatz3.Critical.RecordRankArithmetic
import CollatzLean.Collatz3.Critical.RecordLocalGeometry
import CollatzLean.Collatz3.Critical.RecordTerminal
import CollatzLean.Collatz3.Critical.RecordCarryExact
import CollatzLean.Collatz3.Critical.RecordCarryBlockExact

import CollatzLean.Collatz3.Ferrers.RecordView
import CollatzLean.Collatz3.Ferrers.RecordPartition
import CollatzLean.Collatz3.Ferrers.RecordPartitionInverse
import CollatzLean.Collatz3.Ferrers.RecordCanonical
import CollatzLean.Collatz3.Ferrers.RecordCarryCanonical
import CollatzLean.Collatz3.Ferrers.RecordCarryBridge
import CollatzLean.Collatz3.Ferrers.RecordExactConsequences
import CollatzLean.Collatz3.Ferrers.RecordFerrers
import CollatzLean.Collatz3.Ferrers.RecordWordFactorization
import CollatzLean.Collatz3.Ferrers.RecordArithmeticFactorization

import CollatzLean.Collatz3.Semantics.FirstPassage

import CollatzLean.Collatz3.Bridge.SufficiencyConsequences
import CollatzLean.Collatz3.Bridge.RunsToCanonical
import CollatzLean.Collatz3.Bridge.RunScaleConsequences
import CollatzLean.Collatz3.Bridge.ReachOneConsequences
import CollatzLean.Collatz3.Bridge.PeriodicOrbitConsequences
import CollatzLean.Collatz3.Bridge.OrbitFateConsequences
import CollatzLean.Collatz3.Bridge.ProfileWordCanonical
import CollatzLean.Collatz3.Bridge.FirstPassageProfile
import CollatzLean.Collatz3.Bridge.PredecessorExcess
import CollatzLean.Collatz3.Bridge.FerrersRealization
import CollatzLean.Collatz3.Bridge.CriticalRecord
import CollatzLean.Collatz3.Bridge.CriticalRecordEquiv

-- 独立実験層
import CollatzLean.Collatz3.Experimental2

-- 独立実験層との橋
import CollatzLean.Collatz3.Bridge.Experimental2Realization
import CollatzLean.Collatz3.Bridge.Experimental2BeattyInverse
import CollatzLean.Collatz3.Bridge.Experimental2SturmianBoundary
import CollatzLean.Collatz3.Bridge.Experimental2ConvergentSturmian
import CollatzLean.Collatz3.Bridge.Experimental2ConvergentSturmianCompletion
import CollatzLean.Collatz3.Bridge.Experimental2OstrowskiSturmianRecord
import CollatzLean.Collatz3.Bridge.Experimental2CanonicalOstrowski
import CollatzLean.Collatz3.Bridge.Experimental2DualOstrowskiCoordinates
import CollatzLean.Collatz3.Bridge.Experimental2HorizontalOstrowskiTwoAdic
import CollatzLean.Collatz3.Bridge.CollatzLogPhase
import CollatzLean.Collatz3.Bridge.CollatzLogPhaseBounds
import CollatzLean.Collatz3.Bridge.CollatzLogPhaseRun
import CollatzLean.Collatz3.Bridge.CollatzLogPhaseProfile
import CollatzLean.Collatz3.Bridge.CollatzLogPhaseLocalProfile
import CollatzLean.Collatz3.Bridge.CollatzLogPhaseNearReturn
import CollatzLean.Collatz3.Bridge.CollatzLogPhaseMechanical
import CollatzLean.Collatz3.Bridge.CollatzOstrowskiBlockStability
import CollatzLean.Collatz3.Bridge.CollatzOstrowskiRecordStability
import CollatzLean.Collatz3.Bridge.CollatzSturmianPathRecordStability
--
import CollatzLean.Collatz3.Bridge.RecordFerrersRealization
import CollatzLean.Collatz3.Bridge.RecordPartitionNoninjective
import CollatzLean.Collatz3.Bridge.Experimental2DualOstrowskiRealization
--
import CollatzLean.Collatz3.Bridge.GenericRecordFerrersBeatty
import CollatzLean.Collatz3.Bridge.GenericRecordFerrersCollatzOstrowski

-- F9--F13 の collision 算術を Collatz Beatty/log slope へ特殊化する橋
import CollatzLean.Collatz3.Bridge.RecordFerrersCollisionArithmetic
--
import CollatzLean.Collatz3.Bridge.FullCriticalYoung
import CollatzLean.Collatz3.Bridge.FullCriticalYoungPlateau
--
import CollatzLean.Collatz3.Bridge.FullCriticalRestrictedPartition
import CollatzLean.Collatz3.Bridge.ValidEndpointRuns
import CollatzLean.Collatz3.Bridge.CriticalActualFiber
import CollatzLean.Collatz3.Bridge.CriticalActualClassification
import CollatzLean.Collatz3.Bridge.CriticalWidthDisjoint
import CollatzLean.Collatz3.Bridge.CriticalFixedWidthCounting
import CollatzLean.Collatz3.Bridge.CriticalFixedWidthDensity
import CollatzLean.Collatz3.Bridge.CriticalFiniteWidthDensityBound
--
import CollatzLean.Collatz3.Bridge.FullFirstCrossing
import CollatzLean.Collatz3.Bridge.FullFirstCrossingPartition
import CollatzLean.Collatz3.Bridge.FullFirstCrossingActual
import CollatzLean.Collatz3.Bridge.FullFirstCrossingCoarseFiber
import CollatzLean.Collatz3.Bridge.FullFirstCrossingDensity
import CollatzLean.Collatz3.Bridge.FullFirstCrossingFiniteWidthBound
--
import CollatzLean.Collatz3.Bridge.CriticalParityCode
import CollatzLean.Collatz3.Bridge.CriticalAdmissibleParity
import CollatzLean.Collatz3.Bridge.CriticalSurvivorParity
import CollatzLean.Collatz3.Bridge.CriticalFirstCrossingKraft
import CollatzLean.Collatz3.Bridge.CriticalSurvivorDecay
import CollatzLean.Collatz3.Bridge.CriticalInfiniteDensityExact
--
import CollatzLean.Collatz3.Bridge.FiniteParityResidue
import CollatzLean.Collatz3.Bridge.SurvivorActualResidue

/-
# Collatz3: critical-margin / multi-collision package 1--6
1. critical margin と rank-drop determinant
2. coefficient first-passage -> existing CriticalFirstPassage
3. actual correction sum の necessary lower bound
4. high-orbit correction budget upper bound
5. multiple collision の additive / gcd-quadratic area penalty
6. collision-free branch の internal tight recurrence
-/
import CollatzLean.Collatz3.Bridge.CriticalMargin
import CollatzLean.Collatz3.Bridge.CoefficientFirstPassage
import CollatzLean.Collatz3.Bridge.CriticalCorrectionLowerBound
import CollatzLean.Collatz3.Bridge.CriticalCorrectionUpperBound
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.MultiCollisionPenalty
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.CollisionFreeRigidity

--Collatz3.CSTMicro
import CollatzLean.Collatz3.CSTMicro

set_option linter.style.header false

/-!
# Collatz3: thin definitions + derived theorems kernel

stable arithmetic / semantics / Ferrers と独立 `Experimental2` を、Bridge 層だけで接続する。
今回の canonical Ostrowski bridge では、regular-convergent certificate から canonical greedy digits、
sharp inverse corridor、Sturmian ceiling、admissible record cut / `initialRecordCuts` の exact 座標公式を導く。
さらに initial-value horizontal Ostrowski digits について、固定 `2^r` 法の有限状態走査から
`2^r ∣ 3x+1` を exact に判定する scan-local law を導く。
actual odd-only step については `log₂` fractional phase を導入し、一歩が
`log₂(3/2)` 回転と正の小補正 `log₂(1+1/(3x))` に exact に分解されることを導く。
finite actual run ではこの一歩則を telescope し、horizontal convergent denominator 長の区間を
`log₂` 位相の near-return block として exact に表し、高い軌道上の return shift を
`1/q_next + q/(3X ln 2)` で評価する。
さらに critical first-passage の proper prefix では、actual `log₂` growth を
`profile height + normalized Beatty phase + correction sum` に exact 分解する。
二つの proper cut の間ではその差を取り、local actual growth を
`profile difference + mechanical phase difference + local correction sum` に exact 分解する。
さらに任意 block length の horizontal canonical Ostrowski 展開から basic near-return error を合成し、
actual phase shift を `composite Ostrowski error + correction sum` として exact に記述する。
さらに normalized mechanical phase と Ostrowski block error を同定し、Beatty carry threshold、
canonical RecordFerrers carry law、actual Collatz correction-stability を四層で exact に接続する。

旧 `Experimental` は import しない。
-/
