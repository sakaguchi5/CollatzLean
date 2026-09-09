import CollatzLean.Collatz3.Ferrers.RecordExactConsequences
import CollatzLean.Collatz3.Critical.RecordTerminal

/-!
# Collatz3: 真の RecordFerrers

ここで初めて完成形の `RecordFerrers` を定義する。

保存するのは次の三つだけである。

1. admissible critical profile、
2. canonical positive roof anchor `1` が terminal より手前にあること `1 < m`、
3. deterministic `initialRecordCuts` 上の exact carry compatibility。

`initialRecordCuts` / `canonicalRecordLengths` / `CriticalRecordSkeleton` /
`NoRecordLevelTie` / `LocalCriticalBlocksFrom` はすべて profile と carry law から導く。
`IsPrimitiveWidth` と `IsBestUpperWidth` は structure field にせず、十分条件としてだけ使う。
-/

namespace Collatz3
namespace Ferrers

open Critical

/--
幅 `m` の admissible profile が真の Record--Ferrers 条件を満たすこと。

canonical partition は profile から有限計算されるので保存しない。
-/
def IsRecordFerrersProfile
    {m : ℕ}
    (H : AdmissibleProfile m) : Prop :=
  1 < m ∧
    CanonicalCarryCompatibleFrom
      H.1 initialRoofAnchor (initialRecordCuts H.1)

/--
真の RecordFerrers。

新しい巨大 structure を作らず、admissible profile のうち exact canonical carry law を
満たすものだけを subtype として取る。
-/
abbrev RecordFerrers (m : ℕ) :=
  {H : AdmissibleProfile m // IsRecordFerrersProfile H}

namespace RecordFerrers

/-- underlying admissible profile。 -/
def profile
    {m : ℕ}
    (R : RecordFerrers m) : AdmissibleProfile m :=
  R.1

/-- canonical positive anchor `1` は terminal より手前。 -/
theorem one_lt_width
    {m : ℕ}
    (R : RecordFerrers m) :
    1 < m :=
  R.2.1

/-- RecordFerrers に保存された唯一の Collatz-critical local law。 -/
theorem carryCompatible
    {m : ℕ}
    (R : RecordFerrers m) :
    CanonicalCarryCompatibleFrom
      R.profile.1 initialRoofAnchor (initialRecordCuts R.profile.1) :=
  R.2.2

/-- admissible profile と exact canonical carry law から直接 RecordFerrers を作る。 -/
def ofCanonicalCarry
    {m : ℕ}
    (H : AdmissibleProfile m)
    (hm : 1 < m)
    (C : CanonicalCarryCompatibleFrom
      H.1 initialRoofAnchor (initialRecordCuts H.1)) :
    RecordFerrers m :=
  ⟨H, hm, C⟩

/-- canonical carry law から record-level tie 排除を導く。 -/
theorem noRecordLevelTie
    {m : ℕ}
    (R : RecordFerrers m) :
    NoRecordLevelTie R.profile.1 initialRoofAnchor :=
  noRecordLevelTie_of_canonicalCarry
    R.profile.2 R.one_lt_width R.carryCompatible

/-- canonical block lengths 上の全 block は local critical geometry を持つ。 -/
theorem localCriticalBlocks
    {m : ℕ}
    (R : RecordFerrers m) :
    LocalCriticalBlocksFrom
      R.profile.1 initialRoofAnchor
      (canonicalRecordLengths R.profile.1) := by
  exact
    ((canonicalCarryCompatible_iff_noRecordLevelTie_and_localCriticalBlocks
      R.profile.2 R.one_lt_width).1 R.carryCompatible).2

/-- RecordFerrers から canonical critical record skeleton を派生 view として作る。 -/
def toCriticalRecordSkeleton
    {m : ℕ}
    (R : RecordFerrers m) : CriticalRecordSkeleton m :=
  criticalRecordSkeletonOfProfile
    R.profile R.one_lt_width R.noRecordLevelTie

@[simp] theorem toCriticalRecordSkeleton_profile
    {m : ℕ}
    (R : RecordFerrers m) :
    R.toCriticalRecordSkeleton.profile = R.profile :=
  rfl

/-- 派生 skeleton の length 列は deterministic `canonicalRecordLengths` そのもの。 -/
theorem toCriticalRecordSkeleton_lengths
    {m : ℕ}
    (R : RecordFerrers m) :
    R.toCriticalRecordSkeleton.skeleton.lengths =
      canonicalRecordLengths R.profile.1 := by
  exact criticalRecordSkeleton_lengths_eq_canonicalRecordLengths
    R.toCriticalRecordSkeleton

/-- 派生 skeleton の endpoint 列は deterministic `initialRecordCuts` そのもの。 -/
theorem toCriticalRecordSkeleton_endpoints
    {m : ℕ}
    (R : RecordFerrers m) :
    criticalRecordSkeletonEndpoints R.toCriticalRecordSkeleton =
      initialRecordCuts R.profile.1 := by
  simpa using
    criticalRecordSkeletonEndpoints_eq_initialRecordCuts
      R.toCriticalRecordSkeleton

/--
`NoRecordLevelTie` と canonical local criticality が分かれば、exact theorem の逆向きから
RecordFerrers を構成できる。
-/
def ofTieFreeLocalCritical
    {m : ℕ}
    (H : AdmissibleProfile m)
    (hm : 1 < m)
    (T : NoRecordLevelTie H.1 initialRoofAnchor)
    (L : LocalCriticalBlocksFrom
      H.1 initialRoofAnchor (canonicalRecordLengths H.1)) :
    RecordFerrers m :=
  ⟨H, hm,
    (canonicalCarryCompatible_iff_noRecordLevelTie_and_localCriticalBlocks
      H.2 hm).2 ⟨T, L⟩⟩

/--
primitive width と best-upper は RecordFerrers の定義条件ではないが、`m>2` なら
RecordFerrers を一括して構成する十分条件になる。
-/
def ofPrimitiveBestUpper
    {m : ℕ}
    (H : AdmissibleProfile m)
    (hm : 2 < m)
    (P : IsPrimitiveWidth m)
    (Best : IsBestUpperWidth m) :
    RecordFerrers m := by
  have hm1 : 1 < m := by omega
  have T : NoRecordLevelTie H.1 initialRoofAnchor :=
    noRecordLevelTie_of_primitive P
  let S : CriticalRecordSkeleton m :=
    criticalRecordSkeletonOfProfile H hm1 T
  have Ls :
      LocalCriticalBlocksFrom
        S.profile.1 initialRoofAnchor S.skeleton.lengths :=
    S.localCriticalBlocks_of_bestUpper Best hm
  have hProfile : S.profile = H := by
    rfl
  have hLengths :
      S.skeleton.lengths = canonicalRecordLengths S.profile.1 :=
    criticalRecordSkeleton_lengths_eq_canonicalRecordLengths S
  rw [hProfile] at hLengths Ls
  have L :
      LocalCriticalBlocksFrom
        H.1 initialRoofAnchor (canonicalRecordLengths H.1) := by
    rw [hLengths] at Ls
    exact Ls
  exact ofTieFreeLocalCritical H hm1 T L

end RecordFerrers
end Ferrers
end Collatz3
