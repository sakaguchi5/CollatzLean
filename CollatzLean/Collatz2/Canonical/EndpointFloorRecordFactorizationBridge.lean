import CollatzLean.Collatz2.Canonical.EndpointFloorRecordChain
import CollatzLean.Collatz2.Geometry.RecordFerrersFactorization
import CollatzLean.Collatz2.Geometry.BlockFerrersDeficit

/-!
# Collatz2 Canonical: current-A record chain -> generic Record/Ferrers factorization

既存 current A 専用 `RecordChainData` を、Collatz2.Geometry の generic
`RankRecordDecomposition` へ忘却する bridge。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

namespace NextRecordBlockData

/-- current A one-step packet を generic rank-record block へ落とす。 -/
def toRankRecordBlock
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (B : NextRecordBlockData D a) :
    Word.RankRecordBlock D.word a := by
  let r := B.trap.crossingLength
  have hBlockEq :
      Word.recordBlockWord D.word a r = B.trap.block := by
    rfl
  have hBlockLen :
      Word.oddSteps (Word.recordBlockWord D.word a r) = r := by
    rw [hBlockEq]
    unfold CutRecordTrapData.block Word.oddSteps
    exact List.length_take_of_le B.trap.crossingLength_le_suffix
  refine {
    length := r
    length_pos := B.trap.crossingLength_pos
    next_le_terminal := by
      simpa [r, CutRecordTrapData.nextIndex] using B.trap.next_le_terminal
    block_length := hBlockLen
    minimal := ?_
    start_roof := B.start_roof
    before_record := ?_
    rank_strict := ?_
    next_roof_if_interior := ?_
  }
  · refine {
      firstCrossing := ?_
      minimalDepth := ?_
    }
    · simpa [hBlockEq] using B.trap.firstCrossing
    · have hLenBlock :
          Word.oddSteps B.trap.block = r := by
        rw [← hBlockEq]
        exact hBlockLen
      rw [hBlockEq, hLenBlock]
      simpa [r, CutRecordTrapData.block] using
        B.block_minimal_depth
  · intro j hjPos hjLt
    exact B.trap.before_record j hjPos (by simpa [r] using hjLt)
  · simpa [r, CutRecordTrapData.nextIndex] using B.rank_strict
  · intro hInterior
    apply B.next_roof_if_interior
    simpa [r, CutRecordTrapData.nextIndex] using hInterior

/-- generic block の length は既存 crossingLength。 -/
@[simp] theorem toRankRecordBlock_length
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (B : NextRecordBlockData D a) :
    B.toRankRecordBlock.length = B.trap.crossingLength := by
  rfl

end NextRecordBlockData

namespace RecordChainData

/-- existing current-A chain の generic forward decomposition。 -/
def toRankRecordDecomposition
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ} :
    RecordChainData D a → Word.RankRecordDecomposition D.word a
  | .terminal block hterm =>
      .terminal block.toRankRecordBlock (by
        simpa [NextRecordBlockData.toRankRecordBlock_length,
          CutRecordTrapData.nextIndex] using hterm)
  | .step block hinterior tail =>
      .step block.toRankRecordBlock
        (by
          simpa [NextRecordBlockData.toRankRecordBlock_length,
            CutRecordTrapData.nextIndex] using hinterior)
        (by
          simpa [NextRecordBlockData.toRankRecordBlock_length,
            CutRecordTrapData.nextIndex] using
              toRankRecordDecomposition tail)

/-- current A chain の record skeleton を generic object として読む。 -/
def toRecordSkeleton
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) : Word.RecordSkeleton :=
  Word.RecordSkeleton.ofDecomposition C.toRankRecordDecomposition

/-- current A generic record skeleton は純 criticalHeight 0/1 carry 条件を満たす。 -/
theorem recordSkeleton_carryCondition
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    Word.RecordSkeleton.carryConditionFrom a C.toRankRecordDecomposition.lengths := by
  exact C.toRankRecordDecomposition.carryConditionFrom_of_firstCrossing
    D.wordFirstCrossing

/-- current A に generic record chain があれば whole exponent depth は minimal contracting depth。 -/
theorem word_twoSteps_eq_criticalHeight_add_one
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    Word.twoSteps D.word = Word.criticalHeight (Word.oddSteps D.word) + 1 := by
  exact C.toRankRecordDecomposition.wholeMinimalDepth_of_firstCrossing
    D.wordFirstCrossing

/-- current A chain の local decorations。 -/
def toDecoratedRecordSkeleton
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    Word.DecoratedRecordSkeleton C.toRecordSkeleton :=
  C.toRankRecordDecomposition.toDecoratedSkeleton

/-- current A word は anchor prefix と generic record blocks の flatten に exact 分解される。 -/
theorem take_append_recordBlocks_eq_word
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    D.word.take a ++ C.toRankRecordDecomposition.blocks.flatten = D.word := by
  rw [C.toRankRecordDecomposition.blocks_flatten_eq_drop]
  exact List.take_append_drop a D.word

/--
current A の global integer Ferrers deficit を、record local deficits と signed carry correctionへ
直接 factorize する。
-/
theorem integerFerrersDeficit_eq_recordFactorization
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    (Word.integerFerrersDeficit D.word : ℤ) =
      Word.recordCriticalCarryCorrectionZ
        (D.word.take a) C.toRankRecordDecomposition.blocks +
      (Word.weightedRecordLocalFerrersDeficit
        (D.word.take a) C.toRankRecordDecomposition.blocks : ℤ) := by
  let blocks := C.toRankRecordDecomposition.blocks
  have hWholeEq : D.word.take a ++ blocks.flatten = D.word := by
    simpa [blocks] using C.take_append_recordBlocks_eq_word
  have hWhole : Word.FirstCrossing (D.word.take a ++ blocks.flatten) := by
    rw [hWholeEq]
    exact D.wordFirstCrossing
  have hMinimal : ∀ b ∈ blocks, Word.MinimalCrossingBlock b := by
    dsimp [blocks]
    exact C.toRankRecordDecomposition.blocks_minimal
  have hEq :=
    Word.integerFerrersDeficit_anchor_eq_carryCorrection_add_weightedLocal_of_minimal
      (D.word.take a) blocks hWhole hMinimal
  simpa [blocks, hWholeEq] using hEq

/-- forward -> inverse concatenate は current A の start cut 以後の suffix を exact に戻す。 -/
theorem assemble_toDecoratedRecordSkeleton
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    C.toDecoratedRecordSkeleton.assemble = D.word.drop a := by
  exact Word.DecoratedRecordSkeleton.assemble_of_decomposition
    C.toRankRecordDecomposition


end RecordChainData

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
