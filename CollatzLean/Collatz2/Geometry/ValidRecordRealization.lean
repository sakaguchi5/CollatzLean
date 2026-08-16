import CollatzLean.Collatz2.Geometry.InitialAnchorFirstCrossing
import CollatzLean.Collatz2.Canonical.CenterResidue

/-!
# Collatz2 Geometry: valid local record decorations から genuine Runs を回収

`InitialAnchorFirstCrossing` では、initial anchor `[1]` と carry-compatible な
`MinimalCrossingBlock` 列から whole `MinimalCrossingBlock` と
`RankRecordDecomposition` を復元した。

このファイルでは local atom を `ValidMinimalCrossingBlock` に強めることで、
assembled whole word の `Valid` も自動回収し、既存 `canonicalRuns` を通して
stepwise normalized odd-only `Runs` まで持ち上げる。

さらに primitive + StripReduced を仮定した版では、同じ whole word に対して

* genuine `Runs`
* whole `MinimalCrossingBlock`
* `RankRecordDecomposition`

を同時に得る。
-/

namespace Collatz2
namespace Word

/-- valid minimal block 列の flatten は valid。 -/
theorem valid_flatten_of_validMinimalBlocks
    (bs : List Word)
    (hBlocks : ∀ b ∈ bs, ValidMinimalCrossingBlock b) :
    Valid bs.flatten := by
  induction bs with
  | nil =>
      simp [Valid]
  | cons b bs ih =>
      have hb : ValidMinimalCrossingBlock b :=
        hBlocks b (by simp)
      have hTailBlocks :
          ∀ c ∈ bs, ValidMinimalCrossingBlock c := by
        intro c hc
        exact hBlocks c (by simp [hc])
      have hTailValid : Valid bs.flatten :=
        ih hTailBlocks
      simpa only [List.flatten_cons] using
        hb.valid.append hTailValid

/-- initial anchor `[1]` を付けても valid 性は保存される。 -/
theorem valid_one_append_of_validMinimalBlocks
    (bs : List Word)
    (hBlocks : ∀ b ∈ bs, ValidMinimalCrossingBlock b) :
    Valid (([1] : Word) ++ bs.flatten) := by
  have hOne : Valid ([1] : Word) := by
    simp [Valid]
  exact hOne.append
    (valid_flatten_of_validMinimalBlocks bs hBlocks)

/-- valid local block から underlying minimal block を忘却する。 -/
theorem minimalBlocks_of_validMinimalBlocks
    (bs : List Word)
    (hBlocks : ∀ b ∈ bs, ValidMinimalCrossingBlock b) :
    ∀ b ∈ bs, MinimalCrossingBlock b := by
  intro b hb
  exact (hBlocks b hb).toMinimalCrossingBlock

/--
initial `[1]` anchor 上で、valid minimal local blocks と full carry condition だけから
whole の genuine normalized odd-only `Runs` と whole `MinimalCrossingBlock` を得る。

`Runs` は canonical start/end realization を使って構成する。
-/
theorem runs_one_append_of_validMinimalBlocks_carryCondition
    (bs : List Word)
    (hBlocks : ∀ b ∈ bs, ValidMinimalCrossingBlock b)
    (hCarry :
      RecordSkeleton.carryConditionFrom
        1 (bs.map oddSteps)) :
    ∃ X Y : ℕ,
      Runs (([1] : Word) ++ bs.flatten) X Y ∧
      MinimalCrossingBlock (([1] : Word) ++ bs.flatten) := by
  have hMinimal :
      ∀ b ∈ bs, MinimalCrossingBlock b :=
    minimalBlocks_of_validMinimalBlocks bs hBlocks
  have hWholeMinimal :
      MinimalCrossingBlock (([1] : Word) ++ bs.flatten) :=
    minimalCrossingBlock_one_append_of_minimalBlocks_carryCondition
      bs hMinimal hCarry
  have hWholeValid :
      Valid (([1] : Word) ++ bs.flatten) :=
    valid_one_append_of_validMinimalBlocks bs hBlocks
  have hRuns :
      Runs
        (([1] : Word) ++ bs.flatten)
        (canonicalStart (([1] : Word) ++ bs.flatten))
        (canonicalEnd (([1] : Word) ++ bs.flatten)) :=
    canonicalRuns hWholeValid
  exact
    ⟨canonicalStart (([1] : Word) ++ bs.flatten),
      canonicalEnd (([1] : Word) ++ bs.flatten),
      hRuns,
      hWholeMinimal⟩

/--
valid local atoms + carry + primitive + StripReduced から、同じ assembled whole word に

* genuine normalized odd-only `Runs`
* whole `MinimalCrossingBlock`
* genuine `RankRecordDecomposition`

を同時に回収する。
-/
theorem exists_runs_minimal_rankRecord_one_of_validMinimalPrimitiveReduced
    (bs : List Word)
    (hBlocks : ∀ b ∈ bs, ValidMinimalCrossingBlock b)
    (hCarry :
      RecordSkeleton.carryConditionFrom
        1 (bs.map oddSteps))
    (hPrimitive :
      Nat.Coprime
        (twoSteps (([1] : Word) ++ bs.flatten))
        (oddSteps (([1] : Word) ++ bs.flatten)))
    (hReduced :
      ∀ r : ℕ,
        0 < r →
        r < oddSteps (([1] : Word) ++ bs.flatten) →
        stripRank (([1] : Word) ++ bs.flatten) r ≤
          oddSteps (([1] : Word) ++ bs.flatten)) :
    ∃ X Y : ℕ,
      Runs (([1] : Word) ++ bs.flatten) X Y ∧
      MinimalCrossingBlock (([1] : Word) ++ bs.flatten) ∧
      Nonempty
        (RankRecordDecomposition
          (([1] : Word) ++ bs.flatten) 1) := by
  obtain ⟨X, Y, hRuns, hWholeMinimal⟩ :=
    runs_one_append_of_validMinimalBlocks_carryCondition
      bs hBlocks hCarry
  have hMinimal :
      ∀ b ∈ bs, MinimalCrossingBlock b :=
    minimalBlocks_of_validMinimalBlocks bs hBlocks
  let hRecord :
      RankRecordDecomposition
        (([1] : Word) ++ bs.flatten) 1 :=
    rankRecordDecomposition_one_of_primitiveReduced
      bs hMinimal hCarry hPrimitive hReduced
  exact ⟨X, Y, hRuns, hWholeMinimal, ⟨hRecord⟩⟩

end Word
end Collatz2
