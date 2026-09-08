import CollatzLean.Collatz3.Ferrers.RecordCarryCanonical

/-!
# Collatz3: canonical cuts 表現と block lengths 表現の exact bridge

6A--6C では deterministic `initialRecordCuts` を直接たどる canonical 表現を導入した。
一方、既存の `Critical.RoofRecordSkeleton.RealizesBlocksFrom` と
`Critical.RecordCarryCompatibleFrom` は block length 列をたどる。

このファイルでは両者が同じ区間分割を表していることを exact に閉じる。

中心結果は次の二つ。

1. `CanonicalStrictBlocksFrom` と、`blockLengthsFromCuts` 上の
   `RoofRecordSkeleton.RealizesBlocksFrom` は同値。
2. `CanonicalCarryCompatibleFrom` と、同じ length 列上の
   `RecordCarryCompatibleFrom` は同値。

ここでは RecordFerrers 自体はまだ定義しない。
Admissible / primitive / best-upper も表現変換そのものには不要である。
-/

namespace Collatz3
namespace Ferrers

open Critical

/--
strict cut chain を隣接差へ変換しても、strict block realization は exact に保存される。

cuts 表現
`a < k₁ < ... < kₛ < m`
と lengths 表現
`[k₁-a, ..., m-kₛ]`
が同じ strict roof-record chain を表すことを述べる。
-/
theorem canonicalStrictBlocksFrom_iff_realizesBlocksFrom_blockLengths
    {m : ℕ}
    {h : Profile m} :
    ∀ (a : ℕ) (cuts : List ℕ),
      StrictCutChainFrom m a cuts →
      (CanonicalStrictBlocksFrom h a cuts ↔
        RoofRecordSkeleton.RealizesBlocksFrom
          h a (blockLengthsFromCuts m a cuts))
  | a, [], hChain => by
      simp only [StrictCutChainFrom] at hChain
      simp only [
        CanonicalStrictBlocksFrom,
        blockLengthsFromCuts,
        RoofRecordSkeleton.RealizesBlocksFrom
      ]
      have hTerminal : a + (m - a) = m :=
        Nat.add_sub_of_le (Nat.le_of_lt hChain)
      constructor
      · intro hBlock
        exact ⟨hBlock, hTerminal⟩
      · intro hRealizes
        exact hRealizes.1
  | a, k :: ks, hChain => by
      simp only [StrictCutChainFrom] at hChain
      have hak : a < k := hChain.1
      have hIndex : a + (k - a) = k :=
        Nat.add_sub_of_le (Nat.le_of_lt hak)
      let tailLengths : List ℕ :=
        blockLengthsFromCuts m k ks
      have hTailNe : tailLengths ≠ [] := by
        dsimp [tailLengths]
        exact blockLengthsFromCuts_ne_nil m k ks
      cases hTailEq : tailLengths with
      | nil =>
          exact False.elim (hTailNe hTailEq)
      | cons s ss =>
          have hTailIff :=
            canonicalStrictBlocksFrom_iff_realizesBlocksFrom_blockLengths
              (m := m) (h := h) k ks hChain.2.2
          change
            CanonicalStrictBlocksFrom h k ks ↔
              RoofRecordSkeleton.RealizesBlocksFrom
                h k tailLengths
            at hTailIff
          rw [hTailEq] at hTailIff
          simp only [CanonicalStrictBlocksFrom, blockLengthsFromCuts]
          change
            (Combinatorics.IsRecordBlock
                (profileChordRank h) a (k - a) ∧
              IsRoofCut h k ∧
              CanonicalStrictBlocksFrom h k ks) ↔
              RoofRecordSkeleton.RealizesBlocksFrom
                h a ((k - a) :: tailLengths)
          rw [hTailEq]
          simp only [RoofRecordSkeleton.RealizesBlocksFrom]
          rw [hIndex]
          constructor
          · rintro ⟨hBlock, hRoof, hTail⟩
            exact ⟨hBlock, hRoof, hTailIff.1 hTail⟩
          · rintro ⟨hBlock, hRoof, hTail⟩
            exact ⟨hBlock, hRoof, hTailIff.2 hTail⟩

/--
strict cut chain を隣接差へ変換しても、exact carry compatibility は exact に保存される。

terminal carry `0` を含め、cuts 表現と lengths 表現は同一条件を読む。
順序仮定は `a + (k-a) = k` を保証するためだけに使う。
-/
theorem canonicalCarryCompatibleFrom_iff_recordCarryCompatibleFrom_blockLengths
    {m : ℕ}
    {h : Profile m} :
    ∀ (a : ℕ) (cuts : List ℕ),
      StrictCutChainFrom m a cuts →
      (CanonicalCarryCompatibleFrom h a cuts ↔
        RecordCarryCompatibleFrom
          h a (blockLengthsFromCuts m a cuts))
  | a, [], _hChain => by
      simp only [
        CanonicalCarryCompatibleFrom,
        blockLengthsFromCuts,
        RecordCarryCompatibleFrom
      ]
  | a, k :: ks, hChain => by
      simp only [StrictCutChainFrom] at hChain
      have hak : a < k := hChain.1
      have hIndex : a + (k - a) = k :=
        Nat.add_sub_of_le (Nat.le_of_lt hak)
      let tailLengths : List ℕ :=
        blockLengthsFromCuts m k ks
      have hTailNe : tailLengths ≠ [] := by
        dsimp [tailLengths]
        exact blockLengthsFromCuts_ne_nil m k ks
      cases hTailEq : tailLengths with
      | nil =>
          exact False.elim (hTailNe hTailEq)
      | cons s ss =>
          have hTailIff :=
            canonicalCarryCompatibleFrom_iff_recordCarryCompatibleFrom_blockLengths
              (m := m) (h := h) k ks hChain.2.2
          change
            CanonicalCarryCompatibleFrom h k ks ↔
              RecordCarryCompatibleFrom h k tailLengths
            at hTailIff
          rw [hTailEq] at hTailIff
          simp only [CanonicalCarryCompatibleFrom, blockLengthsFromCuts]
          change
            (NoPrematureCarryOneRoofReturn h a (k - a) ∧
              CanonicalCarryCompatibleFrom h k ks) ↔
              RecordCarryCompatibleFrom
                h a ((k - a) :: tailLengths)
          rw [hTailEq]
          simp only [RecordCarryCompatibleFrom]
          rw [hIndex]
          constructor
          · rintro ⟨hHead, hTail⟩
            exact ⟨hHead, hTailIff.1 hTail⟩
          · rintro ⟨hHead, hTail⟩
            exact ⟨hHead, hTailIff.2 hTail⟩

/--
canonical initial record partition について、cuts 版 strict blocks と
`canonicalRecordLengths` 版 roof-record realization は exact に同値。
-/
theorem canonicalStrictBlocksFrom_iff_realizesCanonicalRecordLengths
    {m : ℕ}
    {h : Profile m}
    (hm : 1 < m) :
    (CanonicalStrictBlocksFrom
        h initialRoofAnchor (initialRecordCuts h) ↔
      RoofRecordSkeleton.RealizesBlocksFrom
        h initialRoofAnchor (canonicalRecordLengths h)) := by
  simpa [canonicalRecordLengths] using
    canonicalStrictBlocksFrom_iff_realizesBlocksFrom_blockLengths
      (m := m) (h := h)
      initialRoofAnchor (initialRecordCuts h)
      (initialRecordCuts_strictCutChain (h := h) hm)

/--
canonical initial record partition について、cuts 版 carry law と
`canonicalRecordLengths` 版 `RecordCarryCompatibleFrom` は exact に同値。
-/
theorem canonicalCarryCompatibleFrom_iff_recordCarryCompatibleCanonicalRecordLengths
    {m : ℕ}
    {h : Profile m}
    (hm : 1 < m) :
    (CanonicalCarryCompatibleFrom
        h initialRoofAnchor (initialRecordCuts h) ↔
      RecordCarryCompatibleFrom
        h initialRoofAnchor (canonicalRecordLengths h)) := by
  simpa [canonicalRecordLengths] using
    canonicalCarryCompatibleFrom_iff_recordCarryCompatibleFrom_blockLengths
      (m := m) (h := h)
      initialRoofAnchor (initialRecordCuts h)
      (initialRecordCuts_strictCutChain (h := h) hm)

/--
6C の canonical carry law から、計算で得た `canonicalRecordLengths` が
既存の roof-record realization を実現する。

これは次段で `CriticalRecordSkeleton` view を構成するための直接 bridge。
-/
theorem realizesCanonicalRecordLengths_of_carry
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 1 < m)
    (C : CanonicalCarryCompatibleFrom
      h initialRoofAnchor (initialRecordCuts h)) :
    RoofRecordSkeleton.RealizesBlocksFrom
      h initialRoofAnchor (canonicalRecordLengths h) := by
  apply
    (canonicalStrictBlocksFrom_iff_realizesCanonicalRecordLengths
      (h := h) hm).1
  exact canonicalStrictBlocksFrom_of_carry A hm C

end Ferrers
end Collatz3
