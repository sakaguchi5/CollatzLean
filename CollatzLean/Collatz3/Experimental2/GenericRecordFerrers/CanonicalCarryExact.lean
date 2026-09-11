import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.CanonicalRecordChain
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordTie
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: canonical record partition の exact carry law

第5段階で、`canonicalRecordLengths` が標準 anchor `1` から terminal `m` までの
実際の `RoofBlockChainFrom` を成すことまで示した。

このファイルでは、その deterministic canonical chain と既存の
`Experimental2.RecordCarryLaw` を接続する。

中心は次の三点である。

1. canonical strict record drop と roof endpoint から interior carry `1` は自動的に従う。
2. したがって canonical 側で保存すべき carry 条件は contextual 版だけでよい。
3. canonical contextual carry compatibility は、canonical 全 block の local criticality と
   exact に同値である。

`Critical.beattyIndex`、`Critical.Profile`、実際の Collatz 軌道には依存しない。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
roof 上の start `a` から roof 上の endpoint `a+r` へ進んだとき、
endpoint の弦順位が strict に下がるなら、その接合 carry は必ず `1`。

carry が `0` なら rank drop は

`criticalDepth β m * r < m * β r`

を要求するが、`HasUnitCarry.below_criticalChord` は逆向きの strict inequality を与える。
-/
theorem roofCarry_eq_one_of_roof_rank_drop
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    {a r : ℕ}
    (hr : 0 < r)
    (hStart : IsProperRoofCut β m height a)
    (hEnd : IsProperRoofCut β m height (a + r))
    (hDrop :
      chordRank β m height (a + r) <
        chordRank β m height a) :
    roofCarry β a r = 1 := by
  rcases U.carry_eq_zero_or_one a r with hZero | hOne
  · have hAdd := U.add_eq a r
    rw [hZero] at hAdd
    have hAddZ :
        (β (a + r) : ℤ) = (β a : ℤ) + (β r : ℤ) := by
      exact_mod_cast hAdd
    have hChord :
        m * β r < criticalDepth β m * r :=
      U.below_criticalChord hr
    have hChordZ :
        (m : ℤ) * (β r : ℤ) <
          (criticalDepth β m : ℤ) * (r : ℤ) := by
      exact_mod_cast hChord
    rw [chordRank_of_lt (β := β) (height := height) hEnd.2.1] at hDrop
    rw [chordRank_of_lt (β := β) (height := height) hStart.2.1] at hDrop
    rw [hEnd.2.2, hStart.2.2] at hDrop
    have hIndexZ :
        ((a + r : ℕ) : ℤ) = (a : ℤ) + (r : ℤ) := by
      push_cast
      ring
    rw [hIndexZ, hAddZ] at hDrop
    linarith
  · exact hOne

/--
strict canonical cut chain を隣接差へ変換した block length 列では、
全 interior boundary carry が `1` になる。

必要なのは

* start が roof cut、
* 各 canonical block が weak record block、
* cut 列が strict に増加すること

だけである。terminal block の carry はここでは要求しない。
-/
theorem interiorCarryOneFrom_blockLengths_of_canonicalWeakBlocks
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∀ (a : ℕ) (cuts : List ℕ),
      IsProperRoofCut β m height a →
      StrictCutChainFrom m a cuts →
      CanonicalWeakBlocksFrom β m height a cuts →
      InteriorCarryOneFrom β a (blockLengthsFromCuts m a cuts)
  | _a, [], _hStart, _hChain, _hWeak => by
      simp [blockLengthsFromCuts, InteriorCarryOneFrom]
  | a, k :: ks, hStart, hChain, hWeak => by
      simp only [StrictCutChainFrom] at hChain
      simp only [CanonicalWeakBlocksFrom] at hWeak
      have hak : a < k := hChain.1
      have hIndex : a + (k - a) = k :=
        Nat.add_sub_of_le (Nat.le_of_lt hak)
      have hDrop :
          chordRank β m height k < chordRank β m height a := by
        have h := hWeak.1.end_drop
        simpa [hIndex] using h
      have hCarry : roofCarry β a (k - a) = 1 := by
        apply roofCarry_eq_one_of_roof_rank_drop U
        · exact Nat.sub_pos_of_lt hak
        · exact hStart
        · simpa [hIndex] using hWeak.2.1
        · simpa [hIndex] using hDrop
      have hTail :=
        interiorCarryOneFrom_blockLengths_of_canonicalWeakBlocks
          U k ks hWeak.2.1 hChain.2.2 hWeak.2.2
      let tailLengths : List ℕ :=
        blockLengthsFromCuts m k ks
      have hTailNe : tailLengths ≠ [] := by
        dsimp [tailLengths]
        exact blockLengthsFromCuts_ne_nil m k ks
      change
        InteriorCarryOneFrom β a
          ((k - a) :: tailLengths)
      change
        InteriorCarryOneFrom β k tailLengths
        at hTail
      cases hTailEq : tailLengths with
      | nil =>
          exact False.elim (hTailNe hTailEq)
      | cons s ss =>
          simp only [InteriorCarryOneFrom]
          refine ⟨hCarry, ?_⟩
          rw [hIndex]
          rw [hTailEq] at hTail
          exact hTail

/--
標準 canonical record partition の全 interior boundary carry は自動的に `1`。

したがって一般 RecordFerrers の定義に interior carry `1` を保存する必要はない。
-/
theorem canonicalRecordLengths_interiorCarryOne
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    InteriorCarryOneFrom β canonicalAnchor
      (canonicalRecordLengths β m height) := by
  have hStart : IsProperRoofCut β m height canonicalAnchor :=
    canonicalAnchor_isProperRoofCut U A hβ1 hm
  have hChain :
      StrictCutChainFrom m canonicalAnchor
        (canonicalRecordCuts β m height) := by
    unfold canonicalRecordCuts
    exact
      recordCutsAfter_strictCutChain
        (β := β) (m := m) (height := height)
        (anchor := canonicalAnchor)
        hStart.2.1
  have hWeak :=
    canonicalWeakBlocksFrom_canonicalRecordCuts U A hβ1 hm
  unfold canonicalRecordLengths recordLengthsAfter
  exact
    interiorCarryOneFrom_blockLengths_of_canonicalWeakBlocks
      U canonicalAnchor
      (recordCutsAfter β m height canonicalAnchor)
      hStart hChain hWeak

/--
canonical record partition に保存する exact carry 条件。

interior carry `1` は record 幾何から自動的に従うため保存せず、

* 各 block の proper prefix で carry-1 roof return が起きないこと、
* 最終 block の terminal carry が `0` であること

だけを `ContextualCarryCompatibleFrom` として保存する。
-/
def CanonicalCarryCompatible
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  ContextualCarryCompatibleFrom
    β m height canonicalAnchor (canonicalRecordLengths β m height)

/-- canonical carry compatibility の定義展開用 theorem。 -/
theorem canonicalCarryCompatible_iff_contextual
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ} :
    CanonicalCarryCompatible β m height ↔
      ContextualCarryCompatibleFrom
        β m height canonicalAnchor (canonicalRecordLengths β m height) := by
  rfl

/--
canonical contextual carry compatibility は、canonical 全 block の local criticality と exact に同値。

第5段階の `RoofBlockChainFrom` と、このファイルで得た interior carry `1` を
既存 `contextualCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom` に渡すだけである。
-/
theorem canonicalCarryCompatible_iff_localRoofCriticalBlocks
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    CanonicalCarryCompatible β m height ↔
      LocalRoofCriticalBlocksFrom
        β m height canonicalAnchor (canonicalRecordLengths β m height) := by
  have hStart : IsProperRoofCut β m height canonicalAnchor :=
    canonicalAnchor_isProperRoofCut U A hβ1 hm
  have hChain := canonicalRecordLengths_roofBlockChain U A hβ1 hm
  have hInterior := canonicalRecordLengths_interiorCarryOne U A hβ1 hm
  simpa [CanonicalCarryCompatible] using
    (contextualCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
      U A canonicalAnchor (canonicalRecordLengths β m height)
      hStart hChain hInterior)

/--
canonical では contextual compatibility と full compatibility も exact に同値。
interior carry `1` が deterministic record geometry から既に供給されるためである。
-/
theorem canonicalCarryCompatible_iff_fullCarryCompatible
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    CanonicalCarryCompatible β m height ↔
      FullCarryCompatibleFrom
        β m height canonicalAnchor (canonicalRecordLengths β m height) := by
  have hStart : IsProperRoofCut β m height canonicalAnchor :=
    canonicalAnchor_isProperRoofCut U A hβ1 hm
  have hChain := canonicalRecordLengths_roofBlockChain U A hβ1 hm
  have hContextualIff :=
    canonicalCarryCompatible_iff_localRoofCriticalBlocks U A hβ1 hm
  have hFullIff :=
    fullCarryCompatibleFrom_iff_localRoofCriticalBlocksFrom
      U A canonicalAnchor (canonicalRecordLengths β m height)
      hStart hChain
  constructor
  · intro C
    exact hFullIff.2 (hContextualIff.1 C)
  · intro F
    exact hContextualIff.2 (hFullIff.1 F)

/--
primitive width では record-level tie が独立に排除されるため、
canonical carry compatibility は

* `NoRecordLevelTie`,
* canonical 全 block の local criticality

の conjunction と exact に同値になる。

primitive 性は canonical carry の定義条件ではなく、tie-free を得る算術的な十分条件に留める。
-/
theorem canonicalCarryCompatible_iff_noRecordLevelTie_and_localCritical_of_primitive
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (U : HasUnitCarry β)
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m)
    (P : IsPrimitiveWidth β m) :
    CanonicalCarryCompatible β m height ↔
      (NoRecordLevelTie β m height canonicalAnchor ∧
        LocalRoofCriticalBlocksFrom
          β m height canonicalAnchor (canonicalRecordLengths β m height)) := by
  have hTie : NoRecordLevelTie β m height canonicalAnchor :=
    canonical_noRecordLevelTie_of_primitive P
  have hLocalIff :=
    canonicalCarryCompatible_iff_localRoofCriticalBlocks U A hβ1 hm
  constructor
  · intro C
    exact ⟨hTie, hLocalIff.1 C⟩
  · rintro ⟨_T, L⟩
    exact hLocalIff.2 L

end GenericRecordFerrers
end Experimental2
end Collatz3
