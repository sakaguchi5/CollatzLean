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
import CollatzLean.Collatz3.Semantics.OddOrbit
import CollatzLean.Collatz3.Semantics.FutureMinimum
import CollatzLean.Collatz3.Semantics.StandardFutureMinimum

import CollatzLean.Collatz3.Combinatorics.WordRepetition
import CollatzLean.Collatz3.Combinatorics.YoungFerrers
import CollatzLean.Collatz3.Combinatorics.Record

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
import CollatzLean.Collatz3.Critical.RecordFerrers

import CollatzLean.Collatz3.Ferrers.RecordView
import CollatzLean.Collatz3.Ferrers.RecordFerrers

import CollatzLean.Collatz3.Semantics.FirstPassage

import CollatzLean.Collatz3.Bridge.SufficiencyConsequences
import CollatzLean.Collatz3.Bridge.RunsToCanonical
import CollatzLean.Collatz3.Bridge.ReachOneConsequences
import CollatzLean.Collatz3.Bridge.PeriodicOrbitConsequences
import CollatzLean.Collatz3.Bridge.ProfileWordCanonical
import CollatzLean.Collatz3.Bridge.FirstPassageProfile
import CollatzLean.Collatz3.Bridge.PredecessorExcess
import CollatzLean.Collatz3.Bridge.FerrersRealization
import CollatzLean.Collatz3.Bridge.CriticalRecord
import CollatzLean.Collatz3.Bridge.CriticalRecordEquiv

set_option linter.style.header false
/-!
# Collatz3: thin definitions + derived theorems kernel

旧体系を import しない。

canonical arithmetic の正本を affine data `(p,H,B)` に一本化し、
Word / Profile はその薄い wrapper とする。

fixed-fiber では signed baseline / signed `E_RF` / signed prepend coordinate を正本とし、
Nat-valued excess は valid word 上の互換 view とする。

actual semantics、pure critical shape、Ferrers/record 幾何を混ぜない。

Record/Ferrers 層は次の三段に分離する。

1. `Ferrers.RecordView`
   任意の admissible profile に deterministic な strict record-low cut list を付ける弱い view。
   Profile と exact `Equiv` であり、cut 抽出は finite computable。

2. `Critical.CriticalRecordSkeleton`
   canonical positive roof anchor `[1]` から terminal まで strict rank excursions を連結し、
   interior endpoint が critical roof に戻ることだけを持つ pure skeleton。
   local first-passage 性はここには保存しない。

3. `Critical.RecordFerrers`
   width-only best-upper arithmetic と terminal minimal input を加え、
   各 skeleton block の local critical geometry を theorem として導く full 層。

critical slope arithmetic では旧 `ContractingExponentPair` を基礎に置かない。
`criticalTwoDepth m` が width `m` だけで決まることを使い、

* `IsBestUpperWidth m`,
* `criticalStripWidth m r`,
* `IsPrimitiveWidth m`,
* `primitiveWidth m`

を一変数 width 理論として扱う。旧 `StripReduced` は
`IsBestUpperWidth` と同値な compatibility view に降格する。

primitive 性は weak RecordView から strict skeleton へ上げる際の rank-tie 排除に使う語彙で、
full RecordFerrers の定義には埋め込まない。

`0` を record anchor にすると start/terminal rank がともに 0 となるため、
critical record skeleton では positive roof anchor を採用する。
actual future-minimum は pure anchor と別概念であり、必要な接続は Bridge 層だけに置く。

無限 actual semantics は `OddOrbit` / `FutureMinimum` / `StandardFutureMinimum` に分割する。
stable root が公開するのは future-minimum 性と `FutureMinima.IsStandard` までであり、
無限 tail から canonical witness を classical に選ぶ実装は
`Semantics.StandardFutureMinimumChoice` に隔離して root から import しない。
-/
