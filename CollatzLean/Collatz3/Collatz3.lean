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
import CollatzLean.Collatz3.Semantics.OrbitFate
import CollatzLean.Collatz3.Semantics.FiniteOrbitFate
import CollatzLean.Collatz3.Semantics.FutureMinimum
import CollatzLean.Collatz3.Semantics.StandardFutureMinimum
import CollatzLean.Collatz3.Semantics.OrbitFateFutureMinimum

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
import CollatzLean.Collatz3.Critical.RecordRankArithmetic
import CollatzLean.Collatz3.Critical.RecordLocalGeometry
import CollatzLean.Collatz3.Critical.RecordTerminal
import CollatzLean.Collatz3.Critical.RecordCarryExact

import CollatzLean.Collatz3.Ferrers.RecordView
import CollatzLean.Collatz3.Ferrers.RecordCanonical
import CollatzLean.Collatz3.Ferrers.RecordCarryCanonical
import CollatzLean.Collatz3.Ferrers.RecordCarryBridge

import CollatzLean.Collatz3.Semantics.FirstPassage

import CollatzLean.Collatz3.Bridge.SufficiencyConsequences
import CollatzLean.Collatz3.Bridge.RunsToCanonical
import CollatzLean.Collatz3.Bridge.ReachOneConsequences
import CollatzLean.Collatz3.Bridge.PeriodicOrbitConsequences
import CollatzLean.Collatz3.Bridge.OrbitFateConsequences
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

actual semantics の最終挙動も同じ原則で分離する。

* `ReachesOne x` は指数語を忘れた「1 への有限到達」だけを表す。
* `EndsAtOne w x` はその到達を実現する有限 run 証明書であり、`FirstHitsOne` はその正規形。
* `OddOrbit.HitsOne` / `HasNontrivialRepeat` / `DivergesToInfinity` は無限軌道の3つの薄い最終挙動述語。
* 第1枝は唯一の first-hit word、第2枝は primitive return、第3枝は任意に遠い exponent-1 future minimum
   へ derived theorem で正規化する。
* 三枝の相互排他性は stable 層で構成的に証明する。
* `FiniteOrbitFate` では有限深度の三分法を構成的に閉じる。
* 無限軌道の完全三分法の網羅性だけを `Semantics.OrbitFateClassical` に隔離し、stable root から import しない。

これにより「終点 1」は pure shape の追加条件ではなく、第1の軌道終局型を有限に証明する意味論的条件として扱う。
三分類から finite affine / canonical arithmetic への接続は `Bridge.OrbitFateConsequences` にだけ置く。

Record/Ferrers 層で現在確定しているのは次の三段である。

1. `Ferrers.RecordView`
   任意の admissible profile に deterministic な strict record-low cut list を付ける弱い view。
   Profile と exact `Equiv` であり、cut 抽出は finite computable。

2. `Critical.CriticalRecordSkeleton`
   canonical positive roof anchor `[1]` から terminal まで strict rank excursions を連結し、
   interior endpoint が critical roof に戻ることだけを持つ pure skeleton。
   local first-passage 性はここには保存しない。

3. `Ferrers.RecordCanonical` / `Ferrers.RecordCarryCanonical` /
   `Ferrers.RecordCarryBridge` / `Critical.RecordLocalGeometry` /
   `Critical.RecordTerminal` / `Critical.RecordCarryExact`
   weak record から canonical skeleton への bridge と、その skeleton から local critical geometry を
   導くための定義・補題群。`NoRecordLevelTie` が exact な record-level tie 排除条件であり、
   `IsPrimitiveWidth` はそれを保証する十分条件として使う。
   local geometry 側では、premature carry-1 roof return の禁止と terminal carry `0` が
   exact 条件であり、`RecordCarryCompatibleFrom` と `LocalCriticalBlocksFrom` は同値。
   さらに deterministic `initialRecordCuts` から block lengths を有限計算し、
   canonical carry law が weak record excursion を strict excursion へ昇格させる。
   cuts 表現と block-lengths 表現も strict realization / exact carry law の双方で exact に一致する。
   `IsBestUpperWidth` は必要条件とはせず、`m > 2` で exact carry 条件を一括保証する
   十分条件として使う。

真の `RecordFerrers` structure は現段階ではまだ定義しない。
canonical skeleton と exact local carry 条件が確定したので、次段で必要最小限の条件だけで再導入する。

critical slope arithmetic では旧 `ContractingExponentPair` を基礎に置かない。
`criticalTwoDepth m` が width `m` だけで決まることを使い、

* `IsBestUpperWidth m`,
* `criticalStripWidth m r`,
* `IsPrimitiveWidth m`,
* `primitiveWidth m`

を一変数 width 理論として扱う。旧 `StripReduced` は
`IsBestUpperWidth` と同値な compatibility view に降格する。

primitive 性は weak RecordView から strict skeleton へ上げる際の
record-level tie 排除を保証する十分条件として扱い、structure には埋め込まない。

`0` を record anchor にすると start/terminal rank がともに 0 となるため、
critical record skeleton では positive roof anchor を採用する。
actual future-minimum は pure anchor と別概念であり、必要な接続は Bridge 層だけに置く。

無限 actual semantics は `OddOrbit` / `OrbitFate` / `FutureMinimum` / `StandardFutureMinimum` に分割する。
future minimum の局所正本は `NextFutureMinimum` とし、無限 selector の
 `IsStandard` はその隣接 compatibility view とする。
stable root が公開するのは構成的な有限深度三分法、三枝の相互排他性、局所 future-minimum 性までであり、
無限軌道の完全三分法の網羅性は `Semantics.OrbitFateClassical` に隔離する。
-/
