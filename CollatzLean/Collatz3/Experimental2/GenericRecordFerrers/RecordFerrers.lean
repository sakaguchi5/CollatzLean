import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.CanonicalCarryExact

/-!
# Collatz3 Experimental2: 一般 RecordFerrers の薄い完成形

第1--6段階で

* deterministic chord-rank record partition,
* canonical record cut が genuine roof cut であること,
* canonical lengths が `RoofBlockChainFrom` を成すこと,
* canonical interior carry `1` の自動導出,
* canonical carry compatibility と local criticality の exact 同値

までを一般の unit-carry roof に対して分離した。

ここでは新しい巨大 structure を作らない。

まず、record/carry の本体だけを `HasCanonicalRecordLaw` として置く。これは

* `HasUnitCarry β`,
* `1 < m`,
* deterministic canonical partition 上の exact carry compatibility

だけを持つ。

その上で、完成 path に必要な

* admissible roof path,
* 標準座標 `β 1 = 1`

を加えたものを `IsRecordFerrersPath` とし、その subtype を `RecordFerrers` とする。

この分離により、第8段階では整数直線成分を加えたときに
record/carry law 自体は exact に不変である一方、`β 1 = 1` は gauge 固定条件であることを
明確に扱える。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
一般 RecordFerrers の本質的な canonical record/carry law。

admissibility と標準座標 `β 1 = 1` はここには保存しない。
-/
def HasCanonicalRecordLaw
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  HasUnitCarry β ∧
    1 < m ∧
      CanonicalCarryCompatible β m height

/--
標準座標 `β 1 = 1` に正規化された一般 RecordFerrers path。

canonical partition 自体は `height` から有限計算されるので保存しない。
-/
def IsRecordFerrersPath
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  β 1 = 1 ∧
    IsAdmissibleRoofPath β m height ∧
      HasCanonicalRecordLaw β m height

/--
一般 RecordFerrers。

屋根 `β` と幅 `m` を固定し、完成条件を満たす path の subtype として取る。
-/
abbrev RecordFerrers
    (β : ℕ → ℕ)
    (m : ℕ) :=
  {height : ℕ → ℕ // IsRecordFerrersPath β m height}

namespace RecordFerrers

/-- underlying height path。 -/
def height
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) : ℕ → ℕ :=
  R.1

/-- 標準座標条件 `β 1 = 1`。 -/
theorem roof_one
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    β 1 = 1 :=
  R.2.1

/-- underlying path は admissible。 -/
theorem admissible
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    IsAdmissibleRoofPath β m R.height :=
  R.2.2.1

/-- 完成 RecordFerrers から本質的 canonical law を忘却する。 -/
theorem canonicalLaw
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    HasCanonicalRecordLaw β m R.height :=
  R.2.2.2

/-- underlying roof は unit-carry。 -/
theorem unitCarry
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    HasUnitCarry β :=
  R.canonicalLaw.1

/-- canonical positive anchor `1` は terminal より手前。 -/
theorem one_lt_width
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    1 < m :=
  R.canonicalLaw.2.1

/-- deterministic canonical partition 上の exact carry law。 -/
theorem carryCompatible
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    CanonicalCarryCompatible β m R.height :=
  R.canonicalLaw.2.2

/--
unit-carry roof、admissible path、標準座標、幅、canonical carry law から
直接 RecordFerrers を作る。
-/
def ofCanonicalCarry
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m)
    (C : CanonicalCarryCompatible β m height) :
    RecordFerrers β m :=
  ⟨height, hβ1, A, U, hm, C⟩

/--
canonical 全 block の local criticality から exact theorem の逆向きで
RecordFerrers を構成する。
-/
def ofLocalCritical
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m)
    (L : LocalRoofCriticalBlocksFrom
      β m height canonicalAnchor (canonicalRecordLengths β m height)) :
    RecordFerrers β m :=
  ofCanonicalCarry U A hβ1 hm
    ((canonicalCarryCompatible_iff_localRoofCriticalBlocks
      U A hβ1 hm).2 L)

/-- canonical anchor `1` は proper roof cut。 -/
theorem canonicalAnchor_roof
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    IsProperRoofCut β m R.height canonicalAnchor :=
  canonicalAnchor_isProperRoofCut
    R.unitCarry R.admissible R.roof_one R.one_lt_width

/-- finite computation で得た canonical cuts はすべて genuine roof cuts。 -/
theorem canonicalCut_roof
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    {k : ℕ}
    (hk : k ∈ canonicalRecordCuts β m R.height) :
    IsProperRoofCut β m R.height k :=
  isProperRoofCut_of_mem_canonicalRecordCuts
    R.unitCarry R.admissible R.roof_one R.one_lt_width hk

/-- canonical lengths は anchor `1` から terminal までの genuine roof block chain。 -/
theorem roofBlockChain
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    RoofBlockChainFrom β m R.height canonicalAnchor
      (canonicalRecordLengths β m R.height) :=
  canonicalRecordLengths_roofBlockChain
    R.unitCarry R.admissible R.roof_one R.one_lt_width

/-- canonical interior boundary carry はすべて自動的に `1`。 -/
theorem interiorCarryOne
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    InteriorCarryOneFrom β canonicalAnchor
      (canonicalRecordLengths β m R.height) :=
  canonicalRecordLengths_interiorCarryOne
    R.unitCarry R.admissible R.roof_one R.one_lt_width

/-- canonical contextual carry law は full carry law に昇格する。 -/
theorem fullCarryCompatible
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    FullCarryCompatibleFrom β m R.height canonicalAnchor
      (canonicalRecordLengths β m R.height) :=
  (canonicalCarryCompatible_iff_fullCarryCompatible
    R.unitCarry R.admissible R.roof_one R.one_lt_width).1
    R.carryCompatible

/-- canonical 全 block は local critical geometry を持つ。 -/
theorem localCriticalBlocks
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    LocalRoofCriticalBlocksFrom β m R.height canonicalAnchor
      (canonicalRecordLengths β m R.height) :=
  (canonicalCarryCompatible_iff_localRoofCriticalBlocks
    R.unitCarry R.admissible R.roof_one R.one_lt_width).1
    R.carryCompatible

/--
primitive width は RecordFerrers の定義条件ではない。
追加で primitive 性が分かる場合だけ record-level tie 排除を得る。
-/
theorem noRecordLevelTie_of_primitive
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (P : IsPrimitiveWidth β m) :
    NoRecordLevelTie β m R.height canonicalAnchor :=
  canonical_noRecordLevelTie_of_primitive P

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
