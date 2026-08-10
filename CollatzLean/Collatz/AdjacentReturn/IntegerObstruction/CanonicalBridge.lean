import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Canonical
import CollatzLean.Collatz.AdjacentReturn.CanonicalContractingChain
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.ExactLate

/-!
# canonical actual chain と integer obstruction の bridge

現在の `IntegerObstruction` 正本から既存 `CanonicalLatePacket` machinery を
再利用する変換と、actual `CanonicalContractingChain` が供給する finite canonical data をまとめる。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

namespace CanonicalLateArithmeticData

/-- canonical Late integer data は既存 finite `CanonicalLatePacket` を与える。 -/
theorem toCanonicalLatePacket
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (K : CanonicalLateArithmeticData L) :
    CanonicalLatePacket L.crossing.word L.suffix := by
  refine {
    valid := ?_
    crossing := L.crossing.crossing
    suffix_nonempty := L.suffix_nonempty
    suffix_allSuffixesContracting := L.suffix_allSuffixesContracting
    zeroDigit := K.zeroDigit
    source_lt_endpoint := ?_
    endpoint_lt_peak := ?_
  }
  · rw [← L.word_eq_crossing_append_suffix]
    exact C.base.word_valid
  · rw [← K.crossingCanonical.start_eq, ← K.fullEnd_eq]
    have hgap := C.base.valueGap_pos
    omega
  · rw [← K.fullEnd_eq, ← K.crossingCanonical.endpoint_eq]
    rw [L.crossing.endpoint_eq_start_add_gap]
    exact
      Nat.add_lt_add_left
        L.valueGap_lt_returnGap
        C.base.startValue

/-- bridge 後の packet source は integer block start と一致する。 -/
theorem packet_source_eq_startValue
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (K : CanonicalLateArithmeticData L) :
    K.toCanonicalLatePacket.source = C.base.startValue := by
  unfold CanonicalLatePacket.source
  exact K.crossingCanonical.start_eq.symm

/-- bridge 後の packet peak は first-crossing endpoint と一致する。 -/
theorem packet_peak_eq_crossingEndpoint
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (K : CanonicalLateArithmeticData L) :
    K.toCanonicalLatePacket.peak = L.crossing.endpointValue := by
  unfold CanonicalLatePacket.peak
  exact K.crossingCanonical.endpoint_eq.symm

/-- bridge 後の packet endpoint は adjacent endpoint と一致する。 -/
theorem packet_endpoint_eq_nextValue
    {C : ContractingBlockArithmetic}
    {L : LateBlockArithmeticData C}
    (K : CanonicalLateArithmeticData L) :
    K.toCanonicalLatePacket.endpoint = C.base.nextValue := by
  unfold CanonicalLatePacket.endpoint BlockArithmeticData.nextValue
  exact K.fullEnd_eq.symm

end CanonicalLateArithmeticData

end IntegerObstruction

namespace CanonicalContractingChain

/-- actual canonical chain の first crossing は integer canonical data を与える。 -/
theorem firstCrossingArithmetic_canonical
    {O : OddOrbit}
    (C : CanonicalContractingChain O)
    (n : ℕ)
    (F : FirstCrossingData (C.state n)) :
    IntegerObstruction.CanonicalFirstCrossingArithmeticData
      (IntegerObstruction.FirstCrossingArithmeticData.ofFirstCrossing F) := by
  refine {
    start_eq := ?_
    endpoint_eq := ?_
  }
  · change
      (C.state n).startValue =
        Word.canonicalStart ((C.state n).word.take F.length)
    exact C.firstCrossingCanonical n F
  · change
      F.endpointValue =
        Word.canonicalEnd ((C.state n).word.take F.length)
    exact C.firstCrossingEndpoint_eq_canonicalEnd n F

/--
actual canonical chain の Late first crossing から、対応する integer Late data と
その crossing canonical refinement を同時に得る。
-/
theorem exists_lateData_with_crossingCanonical
    {O : OddOrbit}
    (C : CanonicalContractingChain O)
    (n : ℕ)
    (F : FirstCrossingData (C.state n))
    (hLate : F.IsLate) :
    ∃ L : IntegerObstruction.LateBlockArithmeticData
        (IntegerObstruction.ContractingBlockArithmetic.ofState
          (C.state n) (C.blockData n).contracting),
      L.crossing =
          IntegerObstruction.FirstCrossingArithmeticData.ofFirstCrossing F ∧
      IntegerObstruction.CanonicalFirstCrossingArithmeticData L.crossing := by
  let L : IntegerObstruction.LateBlockArithmeticData
      (IntegerObstruction.ContractingBlockArithmetic.ofState
        (C.state n) (C.blockData n).contracting) :=
    IntegerObstruction.LateBlockArithmeticData.ofActualFirstCrossing
      (C.blockData n).contracting F hLate
  refine ⟨L, ?_, ?_⟩
  · rfl
  · change
      IntegerObstruction.CanonicalFirstCrossingArithmeticData
        (IntegerObstruction.FirstCrossingArithmeticData.ofFirstCrossing F)
    exact C.firstCrossingArithmetic_canonical n F

/--
actual canonical chain の Late first crossing は、full-word canonicality と
zero-cylinder を含む integer `CanonicalLateArithmeticData` を実際に持つ。
-/
theorem exists_canonicalLateArithmeticData
    {O : OddOrbit}
    (C : CanonicalContractingChain O)
    (n : ℕ)
    (F : FirstCrossingData (C.state n))
    (hLate : F.IsLate) :
    ∃ L : IntegerObstruction.LateBlockArithmeticData
        (IntegerObstruction.ContractingBlockArithmetic.ofState
          (C.state n) (C.blockData n).contracting),
      L.crossing =
          IntegerObstruction.FirstCrossingArithmeticData.ofFirstCrossing F ∧
      IntegerObstruction.CanonicalLateArithmeticData L := by
  let L : IntegerObstruction.LateBlockArithmeticData
      (IntegerObstruction.ContractingBlockArithmetic.ofState
        (C.state n) (C.blockData n).contracting) :=
    IntegerObstruction.LateBlockArithmeticData.ofActualFirstCrossing
      (C.blockData n).contracting F hLate
  have hcross :
      IntegerObstruction.CanonicalFirstCrossingArithmeticData L.crossing := by
    change
    @IntegerObstruction.CanonicalFirstCrossingArithmeticData
      (IntegerObstruction.BlockArithmeticData.ofState (C.state n))
      (IntegerObstruction.FirstCrossingArithmeticData.ofFirstCrossing F)
    exact C.firstCrossingArithmetic_canonical n F
  have hvalid :
      (L.crossing.word ++ L.suffix).Valid := by
    rw [← L.word_eq_crossing_append_suffix]
    exact (C.state n).word_valid
  have hfullStart :
      (C.state n).startValue =
        Word.canonicalStart (L.crossing.word ++ L.suffix) := by
    rw [← L.word_eq_crossing_append_suffix]
    exact (C.blockData n).startCanonical
  have hfullEnd :
      (C.state n).startValue + (C.state n).valueGap =
        Word.canonicalEnd (L.crossing.word ++ L.suffix) := by
    rw [← (C.state n).nextValue_eq_startValue_add_valueGap]
    rw [← L.word_eq_crossing_append_suffix]
    exact (C.blockData n).endCanonical
  have hzero :
      Word.extensionDigit L.crossing.word L.suffix = 0 := by
    have happ :=
      Word.canonicalStart_append_eq
        (u := L.crossing.word)
        (v := L.suffix)
        hvalid
        L.crossing.crossing.nonempty
    have heq :
        Word.canonicalStart (L.crossing.word ++ L.suffix) =
          Word.canonicalStart L.crossing.word := by
      calc
        Word.canonicalStart (L.crossing.word ++ L.suffix)
            = (C.state n).startValue := hfullStart.symm
        _ = Word.canonicalStart L.crossing.word := hcross.start_eq
    have hsum :
        Word.canonicalStart L.crossing.word +
            Word.residueModulus L.crossing.word *
              Word.extensionDigit L.crossing.word L.suffix =
          Word.canonicalStart L.crossing.word :=
      happ.symm.trans heq
    have hsumZero :
        Word.canonicalStart L.crossing.word +
            Word.residueModulus L.crossing.word *
              Word.extensionDigit L.crossing.word L.suffix =
          Word.canonicalStart L.crossing.word + 0 := by
      simpa using hsum
    have hmul :
        Word.residueModulus L.crossing.word *
            Word.extensionDigit L.crossing.word L.suffix = 0 :=
      Nat.add_left_cancel hsumZero
    rcases Nat.mul_eq_zero.mp hmul with hmod | hdigit
    · have hmodPos :
          0 < Word.residueModulus L.crossing.word := by
        simp [Word.residueModulus]
      exact False.elim ((Nat.ne_of_gt hmodPos) hmod)
    · exact hdigit
  have hallZero :
      Word.AllExtensionDigitsZero L.crossing.word L.suffix :=
    Word.allExtensionDigitsZero_of_extensionDigit_eq_zero
      hvalid L.crossing.crossing.nonempty hzero
  refine ⟨L, rfl, ?_⟩
  exact {
    crossingCanonical := hcross
    fullStart_eq := hfullStart
    fullEnd_eq := hfullEnd
    zeroDigit := hzero
    allExtensionDigitsZero := hallZero
  }

end CanonicalContractingChain

end AdjacentReturn
end Collatz
