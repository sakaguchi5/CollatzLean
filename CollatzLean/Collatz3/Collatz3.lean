import CollatzLean.Collatz3.Arithmetic.Pow23
import CollatzLean.Collatz3.Arithmetic.Signed
import CollatzLean.Collatz3.Arithmetic.ModTwoPow

import CollatzLean.Collatz3.Core.Word
import CollatzLean.Collatz3.Core.PrefixDepth
import CollatzLean.Collatz3.Core.AffineTransfer
import CollatzLean.Collatz3.Core.WordTransfer
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
import CollatzLean.Collatz3.Semantics.OrbitReturn
import CollatzLean.Collatz3.Semantics.PeriodicOrbit

import CollatzLean.Collatz3.Combinatorics.WordRepetition
import CollatzLean.Collatz3.Combinatorics.YoungFerrers
import CollatzLean.Collatz3.Combinatorics.Record

import CollatzLean.Collatz3.FixedFiber.UniversalExcess
import CollatzLean.Collatz3.FixedFiber.PrependExcess

import CollatzLean.Collatz3.Critical.Beatty
import CollatzLean.Collatz3.Critical.FirstPassage
import CollatzLean.Collatz3.Critical.Profile
import CollatzLean.Collatz3.Critical.ProfileAffine
import CollatzLean.Collatz3.Critical.ProfileCanonical
import CollatzLean.Collatz3.Critical.ProfileExtraction
import CollatzLean.Collatz3.Critical.Ferrers
import CollatzLean.Collatz3.Critical.RecordFerrers

import CollatzLean.Collatz3.Semantics.FirstPassage

import CollatzLean.Collatz3.Bridge.SufficiencyConsequences
import CollatzLean.Collatz3.Bridge.RunsToCanonical
import CollatzLean.Collatz3.Bridge.ReachOneConsequences
import CollatzLean.Collatz3.Bridge.PeriodicOrbitConsequences
import CollatzLean.Collatz3.Bridge.ProfileWordCanonical
import CollatzLean.Collatz3.Bridge.FirstPassageProfile
import CollatzLean.Collatz3.Bridge.PredecessorExcess
import CollatzLean.Collatz3.Bridge.FerrersRealization

set_option linter.style.header false
/-!
# Collatz3: thin definitions + derived theorems kernel

旧体系を import しない。

canonical arithmetic の正本を affine data `(p,H,B)` に一本化し、
Word / Profile はその薄い wrapper とする。

fixed-fiber では signed baseline / signed `E_RF` / signed prepend coordinate を正本とし、
Nat-valued excess は valid word 上の互換 view とする。

pure fixed-fiber arithmetic は actual predecessor semantics を import せず、
逆コラッツ木との接続は Bridge 層だけに置く。

さらに actual critical first-passage から有限 profile を抽出し、
checkpoint / affine numerator / canonical `R,Y,Q` まで lossless に接続する。

Ferrers / Record 層も同じ原則に従う。

1. `Combinatorics.YoungFerrers` は一般の ordered finite diagram と古典 Ferrers 条件だけ。
2. `Critical.Ferrers` は Profile を diagram として読む derived view。
3. `Combinatorics.Record` は任意 rank に対する generic record 語彙。
4. `Critical.RecordFerrers` は profile rank を generic record に渡す薄い接着。
5. actual Collatz run との一致は `Bridge.FerrersRealization` だけに置く。
-/
