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
--
import CollatzLean.Collatz3.Bridge.RecordFerrersRealization
import CollatzLean.Collatz3.Bridge.RecordPartitionNoninjective
import CollatzLean.Collatz3.Bridge.Experimental2DualOstrowskiRealization

set_option linter.style.header false

/-!
# Collatz3: thin definitions + derived theorems kernel

stable arithmetic / semantics / Ferrers と独立 `Experimental2` を、Bridge 層だけで接続する。
今回の canonical Ostrowski bridge では、regular-convergent certificate から canonical greedy digits、
sharp inverse corridor、Sturmian ceiling、admissible record cut / `initialRecordCuts` の exact 座標公式を導く。

旧 `Experimental` は import しない。
-/
