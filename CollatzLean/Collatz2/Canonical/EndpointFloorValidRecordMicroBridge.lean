import CollatzLean.Collatz2.Canonical.EndpointFloorRecordFactorizationBridge
import CollatzLean.Collatz2.Geometry.ValidRecordRealization

/-!
# Collatz2 Canonical: primitive-reduced current A -> valid record micro packet

primitive + StripReduced current A から、initial `[1]` anchor 上の generic record blocks を

* `ValidMinimalCrossingBlock`
* full critical carry condition
* exact assembly back to the current-A word

として一度に取り出す。

さらに primitive / StripReduced を assembled word 側の pure 条件へ移し、
`ValidRecordRealization` の one-shot inverse を通して

* genuine normalized odd-only `Runs`
* whole `MinimalCrossingBlock`
* genuine `RankRecordDecomposition`

を current-A word 自身へ戻す。
-/

namespace Collatz2
namespace Word

/-- whole valid word の任意 record slice は valid。 -/
private theorem valid_recordBlockWord_of_valid
    {w : Word}
    (hValid : Valid w)
    (a r : ℕ) :
    Valid (recordBlockWord w a r) := by
  have hDropValid : Valid (w.drop a) := by
    have hSplit : Valid (w.take a ++ w.drop a) := by
      rw [List.take_append_drop]
      exact hValid
    exact hSplit.suffix
  have hTakeValid : Valid ((w.drop a).take r) := by
    have hSplit :
        Valid ((w.drop a).take r ++ (w.drop a).drop r) := by
      rw [List.take_append_drop]
      exact hDropValid
    exact hSplit.prefix
  simpa [recordBlockWord] using hTakeValid

namespace RankRecordDecomposition

/-- valid whole word の generic record decomposition に属する全 block は valid。 -/
theorem blocks_valid_of_valid
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (hValid : Valid w) :
    ∀ b ∈ D.blocks, Valid b := by
  induction D with
  | terminal block hterm =>
      intro b hb
      simp only [blocks, List.mem_singleton] at hb
      subst b
      exact valid_recordBlockWord_of_valid hValid _ _
  | step block hinterior tail ih =>
      intro b hb
      simp only [blocks, List.mem_cons] at hb
      rcases hb with hEq | hb
      · subst b
        exact valid_recordBlockWord_of_valid hValid _ _
      · exact ih b hb

/-- valid whole word の generic record blocks は全て valid minimal local atoms。 -/
theorem blocks_validMinimal_of_valid
    {w : Word}
    {a : ℕ}
    (D : RankRecordDecomposition w a)
    (hValid : Valid w) :
    ∀ b ∈ D.blocks, ValidMinimalCrossingBlock b := by
  intro b hb
  exact {
    toMinimalCrossingBlock := D.blocks_minimal b hb
    valid := D.blocks_valid_of_valid hValid b hb
  }

end RankRecordDecomposition
end Word

namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/--
primitive+reduced current A から external-combinatorics-ready な valid record micro packet を得る。

返す block list は既存 initial record chain の block list そのもので、
`[1] ++ flatten blocks` は exact に元の current-A word へ戻る。
-/
theorem exists_validRecordMicroPacket_of_primitiveReduced
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced) :
    ∃ bs : List Word,
      (∀ b ∈ bs, Word.ValidMinimalCrossingBlock b) ∧
      Word.RecordSkeleton.carryConditionFrom
        1 (bs.map Word.oddSteps) ∧
      ([1] : Word) ++ bs.flatten = D.word := by
  obtain ⟨C⟩ := D.exists_initialRecordChain hPrimitive hReduced
  let R := C.toRankRecordDecomposition
  let bs : List Word := R.blocks
  have hBlocks :
      ∀ b ∈ bs, Word.ValidMinimalCrossingBlock b := by
    dsimp [bs, R]
    exact C.toRankRecordDecomposition.blocks_validMinimal_of_valid
      D.word_valid
  have hCarry :
      Word.RecordSkeleton.carryConditionFrom
        1 (bs.map Word.oddSteps) := by
    have hBase := C.recordSkeleton_carryCondition
    have hLengths := C.toRankRecordDecomposition.blocks_oddSteps_eq_lengths
    dsimp [bs, R]
    rw [hLengths]
    exact hBase
  have hTakeOne : D.word.take 1 = ([1] : Word) := by
    obtain ⟨v, hWord, _hv⟩ := D.exists_prependOne_tail
    rw [hWord]
    simp
  have hAssemble :
      ([1] : Word) ++ bs.flatten = D.word := by
    have hWhole := C.take_append_recordBlocks_eq_word
    dsimp [bs, R]
    rw [hTakeOne] at hWhole
    simpa using hWhole
  exact ⟨bs, hBlocks, hCarry, hAssemble⟩

/--
上の micro packet に、primitive / StripReduced を assembled word 自身の pure 条件として
同時に付けた one-shot extraction。
-/
theorem exists_validRecordMicroPacket_full_of_primitiveReduced
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced) :
    ∃ bs : List Word,
      (∀ b ∈ bs, Word.ValidMinimalCrossingBlock b) ∧
      Word.RecordSkeleton.carryConditionFrom
        1 (bs.map Word.oddSteps) ∧
      ([1] : Word) ++ bs.flatten = D.word ∧
      Nat.Coprime
        (Word.twoSteps (([1] : Word) ++ bs.flatten))
        (Word.oddSteps (([1] : Word) ++ bs.flatten)) ∧
      (∀ r : ℕ,
        0 < r →
        r < Word.oddSteps (([1] : Word) ++ bs.flatten) →
        Word.stripRank (([1] : Word) ++ bs.flatten) r ≤
          Word.oddSteps (([1] : Word) ++ bs.flatten)) := by
  obtain ⟨bs, hBlocks, hCarry, hAssemble⟩ :=
    D.exists_validRecordMicroPacket_of_primitiveReduced
      hPrimitive hReduced
  have hPrimitiveWord :
      Nat.Coprime (Word.twoSteps D.word) (Word.oddSteps D.word) := by
    simpa [Word.ContractingExponentPair.IsPrimitive] using hPrimitive
  have hPrimitiveAssembled :
      Nat.Coprime
        (Word.twoSteps (([1] : Word) ++ bs.flatten))
        (Word.oddSteps (([1] : Word) ++ bs.flatten)) := by
    rw [hAssemble]
    exact hPrimitiveWord
  have hReducedAssembled :
      ∀ r : ℕ,
        0 < r →
        r < Word.oddSteps (([1] : Word) ++ bs.flatten) →
        Word.stripRank (([1] : Word) ++ bs.flatten) r ≤
          Word.oddSteps (([1] : Word) ++ bs.flatten) := by
    intro r hrPos hrLt
    rw [hAssemble] at hrLt ⊢
    rw [← D.exponentPair_stripRank_eq r]
    simpa using hReduced r hrPos (by simpa using hrLt)
  exact
    ⟨bs, hBlocks, hCarry, hAssemble,
      hPrimitiveAssembled, hReducedAssembled⟩

/--
primitive+reduced current A を valid local record micro data へ落としてから再構成し、
元の current-A word 自身について

* genuine `Runs`
* whole minimal FirstCrossing
* rank-record decomposition

を一度に回収する current-A specialization。
-/
theorem exists_runs_minimal_rankRecord_of_primitiveReduced
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced) :
    ∃ X Y : ℕ,
      Runs D.word X Y ∧
      Word.MinimalCrossingBlock D.word ∧
      Nonempty (Word.RankRecordDecomposition D.word 1) := by
  obtain
      ⟨bs, hBlocks, hCarry, hAssemble,
        hPrimitiveAssembled, hReducedAssembled⟩ :=
    D.exists_validRecordMicroPacket_full_of_primitiveReduced
      hPrimitive hReduced
  obtain ⟨X, Y, hRuns, hMinimal, hRecord⟩ :=
    Word.exists_runs_minimal_rankRecord_one_of_validMinimalPrimitiveReduced
      bs hBlocks hCarry hPrimitiveAssembled hReducedAssembled
  refine ⟨X, Y, ?_, ?_, ?_⟩
  · simpa only [hAssemble] using hRuns
  · simpa only [hAssemble] using hMinimal
  · simpa only [hAssemble] using hRecord

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
