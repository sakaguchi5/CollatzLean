import CollatzLean.Collatz3.Combinatorics.RecordDerived

import CollatzLean.Collatz3.Ferrers.RecordPartitionInverse
import CollatzLean.Collatz3.Ferrers.RecordCarryBridge
import CollatzLean.Collatz3.Critical.RecordCarryBlockExact

/-!
# Collatz3: canonical record/carry の exact consequences

真の `RecordFerrers` を定義する前に、既存の deterministic partition・strict skeleton・
exact carry law の間で既に従う結果を名前付き theorem として閉じる。

ここでは新しい完成 structure を導入しない。
-/

namespace Collatz3
namespace Ferrers

open Critical

/-! ## record-level tie 排除の公開局所補題 -/

/--
relative record start `a` の後で、endpoint rank が start 以下、interior が start 以上なら、
その endpoint は元 anchor から見た weak record cut である。
-/
theorem weakRecordCutAfter_of_relativeStart
    {m : ℕ}
    {h : Profile m}
    {anchor a k : ℕ}
    (haRecord : IsRelativeRecordStart h anchor a)
    (hak : a < k)
    (hkm : k < m)
    (hEndLe :
      profileChordRank h k ≤ profileChordRank h a)
    (hInteriorLe :
      ∀ t : ℕ,
        a < t →
        t < k →
        profileChordRank h a ≤ profileChordRank h t) :
    IsWeakRecordCutAfter h anchor k := by
  apply (isWeakRecordCutAfter_iff).2
  refine ⟨lt_of_le_of_lt haRecord.1 hak, hkm, ?_⟩
  intro t hat htk
  by_cases hta : t < a
  · have hPrev :
        profileChordRank h a < profileChordRank h t :=
      haRecord.2.2 t hat hta
    exact le_of_lt (lt_of_le_of_lt hEndLe hPrev)
  · have hatLe : a ≤ t := Nat.le_of_not_gt hta
    by_cases htaEq : t = a
    · subst t
      exact hEndLe
    · have hatStrict : a < t :=
        lt_of_le_of_ne hatLe (Ne.symm htaEq)
      exact le_trans hEndLe (hInteriorLe t hatStrict htk)

/--
`NoRecordLevelTie` の下では、relative record start より後の weak inequality は
実際には strict inequality になる。
-/
theorem strictRankAbove_of_noRecordLevelTie
    {m : ℕ}
    {h : Profile m}
    {anchor a j : ℕ}
    (T : NoRecordLevelTie h anchor)
    (haRecord : IsRelativeRecordStart h anchor a)
    (haj : a < j)
    (hjm : j < m)
    (hLe :
      profileChordRank h a ≤ profileChordRank h j)
    (hInteriorLe :
      ∀ t : ℕ,
        a < t →
        t < j →
        profileChordRank h a ≤ profileChordRank h t) :
    profileChordRank h a < profileChordRank h j := by
  apply lt_of_le_of_ne hLe
  intro hEq
  have hWeakJ : IsWeakRecordCutAfter h anchor j :=
    weakRecordCutAfter_of_relativeStart
      haRecord haj hjm (le_of_eq hEq.symm) hInteriorLe
  have hRecordJ : IsRecordCutAfter h anchor j := T j hWeakJ
  have hRJ := (isRecordCutAfter_iff).1 hRecordJ
  have hDrop :
      profileChordRank h j < profileChordRank h a :=
    hRJ.2.2 a haRecord.1 haj
  exact (ne_of_lt hDrop) hEq.symm

/--
weak record block は `NoRecordLevelTie` の下で genuine strict record block に昇格する。
-/
theorem isRecordBlock_of_weak_of_noRecordLevelTie
    {m : ℕ}
    {h : Profile m}
    {anchor a r : ℕ}
    (T : NoRecordLevelTie h anchor)
    (haRecord : IsRelativeRecordStart h anchor a)
    (hEnd : a + r ≤ m)
    (W : IsWeakRecordBlock h a r) :
    Combinatorics.IsRecordBlock (profileChordRank h) a r := by
  refine ⟨W.length_pos, ?_, W.end_drop⟩
  intro j hjPos hjLt
  have haj : a < a + j := by omega
  have hjm : a + j < m := by omega
  have hLe :
      profileChordRank h a ≤ profileChordRank h (a + j) :=
    W.interior hjPos hjLt
  have hInteriorLe :
      ∀ t : ℕ,
        a < t →
        t < a + j →
        profileChordRank h a ≤ profileChordRank h t := by
    intro t hat htj
    have htPos : 0 < t - a := by omega
    have htLt : t - a < r := by omega
    have hInt := W.interior (j := t - a) htPos htLt
    have hIndex : a + (t - a) = t := by omega
    rw [hIndex] at hInt
    exact hInt
  exact strictRankAbove_of_noRecordLevelTie
    T haRecord haj hjm hLe hInteriorLe

/--
relative record start の後で最初に start rank を strict に下回る点は、元 anchor から見ても
strict record cut である。
-/
theorem firstLower_isRecordCutAfter
    {m : ℕ}
    {h : Profile m}
    {anchor a k : ℕ}
    (haRecord : IsRelativeRecordStart h anchor a)
    (hak : a < k)
    (hkm : k < m)
    (hLower : profileChordRank h k < profileChordRank h a)
    (hFirst :
      ∀ j : ℕ,
        a < j →
        j < k →
        profileChordRank h a ≤ profileChordRank h j) :
    IsRecordCutAfter h anchor k := by
  apply (isRecordCutAfter_iff).2
  refine ⟨lt_of_le_of_lt haRecord.1 hak, hkm, ?_⟩
  intro j haj hjk
  by_cases hja : j < a
  · exact lt_trans hLower (haRecord.2.2 j haj hja)
  by_cases hEq : j = a
  · subst j
    exact hLower
  · have hajStrict : a < j := by omega
    exact lt_of_lt_of_le hLower (hFirst j hajStrict hjk)

/-! ## carry / tie / local critical geometry の exact 合成 -/

/--
canonical exact carry law だけで record-level tie は排除される。
carry から deterministic canonical lengths の strict realization を作り、
既存の skeleton -> tie-free theorem を使う。
-/
theorem noRecordLevelTie_of_canonicalCarry
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m)
    (C : CanonicalCarryCompatibleFrom
      h initialRoofAnchor (initialRecordCuts h)) :
    NoRecordLevelTie h initialRoofAnchor := by
  have hRealizes :
      RoofRecordSkeleton.RealizesBlocksFrom
        h initialRoofAnchor (canonicalRecordLengths h) :=
    realizesCanonicalRecordLengths_of_carry A hm C
  let S : Combinatorics.RecordSkeleton :=
    { lengths := canonicalRecordLengths h
      positive := canonicalRecordLengths_pos (h := h) hm }
  let R : CriticalRecordSkeleton m :=
    { profile := ⟨h, A⟩
      skeleton := S
      realizes :=
        ⟨initialRoofAnchor_isRoofCut A hm, hRealizes⟩ }
  exact noRecordLevelTie_of_criticalRecordSkeleton R

/--
canonical carry law は exact に

* record-level tie が無いこと、
* canonical block lengths の全 block が local critical geometry を持つこと

の conjunction と同値。
-/
theorem canonicalCarryCompatible_iff_noRecordLevelTie_and_localCriticalBlocks
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m) :
    CanonicalCarryCompatibleFrom
        h initialRoofAnchor (initialRecordCuts h) ↔
      (NoRecordLevelTie h initialRoofAnchor ∧
        LocalCriticalBlocksFrom
          h initialRoofAnchor (canonicalRecordLengths h)) := by
  constructor
  · intro C
    have hTie := noRecordLevelTie_of_canonicalCarry A hm C
    have hRealizes := realizesCanonicalRecordLengths_of_carry A hm C
    have hCarryLengths :=
      (canonicalCarryCompatibleFrom_iff_recordCarryCompatibleCanonicalRecordLengths
        (h := h) hm).1 C
    have hLocal :=
      (recordCarryCompatibleFrom_iff_localCriticalBlocksFrom
        A initialRoofAnchor (canonicalRecordLengths h)
        (initialRoofAnchor_isRoofCut A hm) hRealizes).1
        hCarryLengths
    exact ⟨hTie, hLocal⟩
  · rintro ⟨T, hLocal⟩
    have hRealizes :=
      realizesCanonicalRecordLengths_of_noRecordLevelTie A hm T
    have hCarryLengths :=
      (recordCarryCompatibleFrom_iff_localCriticalBlocksFrom
        A initialRoofAnchor (canonicalRecordLengths h)
        (initialRoofAnchor_isRoofCut A hm) hRealizes).2
        hLocal
    exact
      (canonicalCarryCompatibleFrom_iff_recordCarryCompatibleCanonicalRecordLengths
        (h := h) hm).2 hCarryLengths

/--
任意の critical record skeleton の length 列は underlying profile から計算される
`canonicalRecordLengths` と exact に一致する。
-/
theorem criticalRecordSkeleton_lengths_eq_canonicalRecordLengths
    {m : ℕ}
    (R : CriticalRecordSkeleton m) :
    R.skeleton.lengths = canonicalRecordLengths R.profile.1 := by
  have hTie := noRecordLevelTie_of_criticalRecordSkeleton R
  have hCanonical :=
    realizesCanonicalRecordLengths_of_noRecordLevelTie
      R.profile.2 R.one_lt_width hTie
  exact
    realizesBlocksFrom_unique
      initialRoofAnchor
      R.skeleton.lengths
      (canonicalRecordLengths R.profile.1)
      R.realizes.2
      hCanonical

/-- 旧 `properEndpointsFrom` と pure `cutsFromBlockLengths` は同じ有限変換。 -/
theorem properEndpointsFrom_eq_cutsFromBlockLengths :
    ∀ (a : ℕ) (rs : List ℕ),
      properEndpointsFrom a rs = cutsFromBlockLengths a rs
  | _a, [] => rfl
  | _a, [_r] => rfl
  | a, r :: s :: rs => by
      simp only [properEndpointsFrom, cutsFromBlockLengths]
      rw [properEndpointsFrom_eq_cutsFromBlockLengths (a + r) (s :: rs)]

/--
critical record skeleton の proper endpoint list は membership だけでなく
list 自体として deterministic `initialRecordCuts` と一致する。
-/
theorem criticalRecordSkeletonEndpoints_eq_initialRecordCuts
    {m : ℕ}
    (R : CriticalRecordSkeleton m) :
    criticalRecordSkeletonEndpoints R = initialRecordCuts R.profile.1 := by
  unfold criticalRecordSkeletonEndpoints
  rw [criticalRecordSkeleton_lengths_eq_canonicalRecordLengths R]
  rw [properEndpointsFrom_eq_cutsFromBlockLengths]
  exact
    cutsFromCanonicalRecordLengths_eq_initialRecordCuts
      (h := R.profile.1) R.one_lt_width

/--
canonical carry law は、「同じ profile を持つ critical record skeleton が一意に存在し、
その skeleton の全 block が local critical geometry を持つ」ことと exact に同値。

skeleton の一意性は追加 field ではなく既存の strict record geometry から従う。
-/
theorem canonicalCarryCompatible_iff_existsUnique_skeleton_with_localCritical
    {m : ℕ}
    (H : AdmissibleProfile m)
    (hm : 1 < m) :
    CanonicalCarryCompatibleFrom
        H.1 initialRoofAnchor (initialRecordCuts H.1) ↔
      ∃! R : CriticalRecordSkeleton m,
        R.profile = H ∧
          LocalCriticalBlocksFrom
            H.1 initialRoofAnchor R.skeleton.lengths := by
  constructor
  · intro C
    have T := noRecordLevelTie_of_canonicalCarry H.2 hm C
    let R : CriticalRecordSkeleton m :=
      criticalRecordSkeletonOfProfile H hm T
    have hPair :=
      (canonicalCarryCompatible_iff_noRecordLevelTie_and_localCriticalBlocks
        H.2 hm).1 C
    have hLocalCanonical := hPair.2
    have hLengths :=
      criticalRecordSkeleton_lengths_eq_canonicalRecordLengths R
    have hLocalR :
        LocalCriticalBlocksFrom
          H.1 initialRoofAnchor R.skeleton.lengths := by
      rw [hLengths]
      exact hLocalCanonical
    have hRProfile : R.profile = H := by rfl
    refine ⟨R, ⟨hRProfile, hLocalR⟩, ?_⟩
    intro S hS
    apply criticalRecordSkeleton_ext
    exact hS.1.trans hRProfile.symm
  · rintro ⟨R, hR, _hUnique⟩
    have hProfile : R.profile = H := hR.1
    have hTieR := noRecordLevelTie_of_criticalRecordSkeleton R
    have hTie : NoRecordLevelTie H.1 initialRoofAnchor := by
      simpa [hProfile] using hTieR
    have hLengthsR :=
      criticalRecordSkeleton_lengths_eq_canonicalRecordLengths R
    have hLengths :
        R.skeleton.lengths = canonicalRecordLengths H.1 := by
      simpa [hProfile] using hLengthsR
    have hLocalCanonical :
        LocalCriticalBlocksFrom
          H.1 initialRoofAnchor (canonicalRecordLengths H.1) := by
      rw [← hLengths]
      exact hR.2
    exact
      (canonicalCarryCompatible_iff_noRecordLevelTie_and_localCriticalBlocks
        H.2 hm).2 ⟨hTie, hLocalCanonical⟩

end Ferrers
end Collatz3
