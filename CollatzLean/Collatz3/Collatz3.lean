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

--独立実験層
import CollatzLean.Collatz3.Experimental2
--独立実験層との橋
import CollatzLean.Collatz3.Bridge.Experimental2Realization
--
import CollatzLean.Collatz3.Bridge.Experimental2BeattyInverse
import CollatzLean.Collatz3.Bridge.Experimental2SturmianBoundary

set_option linter.style.header false
/-!
# Collatz3: thin definitions + derived theorems kernel

旧体系を import しない。

canonical arithmetic の正本を affine data `(p,H,B)` に一本化し、
Word / Profile はその薄い wrapper とする。

fixed-fiber では signed baseline / signed `E_RF` / signed prepend coordinate を正本とし、
Nat-valued excess は valid word 上の互換 view とする。

actual semantics、pure critical shape、Ferrers/record 幾何を混ぜない。

actual semantics の最終挙動も同じ原則で分離する。

* `ReachesOne x` は指数語を忘れた「1 への有限到達」だけを表す。
* `EndsAtOne w x` はその到達を実現する有限 run 証明書であり、`FirstHitsOne` はその正規形。
* `Merges` 上で `ReachesOne` は不変であり、sufficiency 側はこの semantic theorem を利用する。
* `OddOrbit.HitsOne` / `HasNontrivialRepeat` / `DivergesToInfinity` は無限軌道の3つの薄い最終挙動述語。
* 第1枝は唯一の first-hit word、第2枝は primitive return、第3枝は任意に遠い exponent-1 future minimum
  へ derived theorem で正規化する。
* repeated state から値列だけでなく exponent / finite segment word の周期性も theorem として導く。
* 三枝の相互排他性は stable 層で構成的に証明する。
* `FiniteOrbitFate` では有限深度の三分法を構成的に閉じる。
* 無限軌道の完全三分法の網羅性だけを `Semantics.OrbitFateClassical` に隔離し、stable root から import しない。

これにより「終点 1」は pure shape の追加条件ではなく、第1の軌道終局型を有限に証明する意味論的条件として扱う。
三分類から finite affine / canonical arithmetic への接続は Bridge 層だけに置く。

Record/Ferrers 層では deterministic partition を data の正本とする。

* `initialRecordCuts` と `canonicalRecordLengths` は有限計算。
* cuts と lengths は純データとして相互 inverse。
* canonical exact carry は `NoRecordLevelTie` を派生させる。
* canonical exact carry は
  `NoRecordLevelTie ∧ LocalCriticalBlocksFrom canonicalRecordLengths` と exact に同値。
* 任意の `CriticalRecordSkeleton` の length 列は underlying profile の
  `canonicalRecordLengths` と一致する。
* interior / terminal 一 block の local criticality は exact carry 条件へ局所分解される。
* 真の `RecordFerrers` は
  `AdmissibleProfile + 1 < width + canonical exact carry law`
  だけを保存する最小 subtype とし、skeleton / tie / local criticality は重複保存しない。
* canonical local words は `[1]` の後ろの word を lossless に分解し、各 local word は
  対応する block width の genuine `CriticalWord` になる。
* width / total two-depth / Beatty index / affine translation `B` はこの canonical block 列へ
  exact に factorize される。

critical slope arithmetic では旧 `ContractingExponentPair` を基礎に置かない。
`criticalTwoDepth m` が width `m` だけで決まることを使い、

* `IsBestUpperWidth m`,
* `criticalStripWidth m r`,
* `IsPrimitiveWidth m`,
* `primitiveWidth m`

を一変数 width 理論として扱う。旧 `StripReduced` は
`IsBestUpperWidth` と同値な compatibility view に降格する。

primitive 性と best-upper は RecordFerrers の field ではない。
前者は record-level tie 排除、後者は local criticality を一括保証する十分条件であり、
`RecordFerrers.ofPrimitiveBestUpper` で構成用 certificate としてだけ使う。

`0` を record anchor にすると start/terminal rank がともに 0 となるため、
critical record skeleton では positive roof anchor を採用する。
actual future-minimum は pure anchor と別概念であり、必要な接続は Bridge 層だけに置く。

無限 actual semantics は `OddOrbit` / `OrbitFate` / `FutureMinimum` / `StandardFutureMinimum` に分割する。
future minimum の局所正本は `NextFutureMinimum` とし、無限 selector の
`IsStandard` はその隣接 compatibility view とする。
stable root が公開するのは構成的な有限深度三分法、三枝の相互排他性、局所 future-minimum 性までであり、
無限軌道の完全三分法の網羅性は `Semantics.OrbitFateClassical` に隔離する。
-/
