import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Canonical
import CollatzLean.Collatz.AdjacentReturn.CanonicalContractingChain
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.ExactLate

/-!
# canonical actual chain と integer obstruction の bridge

pure な `CanonicalLateArithmeticData -> CanonicalLatePacket` 変換は
`IntegerObstruction/Canonical.lean` に置き、このファイルでは
actual `CanonicalContractingChain` から pure integer obstruction を
同じ shifted actual state 列・同じ first-crossing choice 上で構成する。

これにより canonical shift を失わずに

CanonicalContractingChain
  -> ContractingIntegerChain
  -> ExactLateContractingIntegerChain
  -> CanonicalIntegerRefinement

を同一 core 上で接続する。
-/

namespace Collatz
namespace AdjacentReturn

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
canonical chain 上の first crossing を各 index で一つ固定する。
以後の pure integer core と canonical refinement は同じ choice を共有する。
-/
noncomputable def chosenFirstCrossing
    {O : OddOrbit}
    (C : CanonicalContractingChain O)
    (n : ℕ) :
    FirstCrossingData (C.state n) := by
  classical
  exact Classical.choice
    ((C.state n).existsFirstCrossingData (C.blockData n).contracting)

/--
canonical shifted actual state 列から直接 `ContractingIntegerChain` を作る。

`CanonicalContractingChain.state` をそのまま使うため、
内部 shift はこの境界で pure chain の index 0 に吸収される。
-/
noncomputable def toContractingIntegerChain
    {O : OddOrbit}
    (C : CanonicalContractingChain O) :
    IntegerObstruction.ContractingIntegerChain := by
  classical
  let V : ∀ n : ℕ, State.ValuationData (C.state n) :=
    fun n => C.valuationData n
  let G : ∀ n : ℕ, FirstCrossingData (C.state n) :=
    fun n => C.chosenFirstCrossing n
  refine {
    chain :=
      IntegerObstruction.AdjacentIntegerChain.ofStateSequence
        (fun n => C.state n)
        (fun n => C.nextValue_eq_next_startValue n)
    block := fun n =>
      IntegerObstruction.ContractingBlockArithmetic.ofState
        (C.state n) (C.blockData n).contracting
    block_base_eq := ?_
    startDepth := fun n => (V n).startDepth
    startOddPart := fun n => (V n).startOddPart
    nextDepth := fun n => (V n).nextDepth
    nextOddPart := fun n => (V n).nextOddPart
    gapDepth := fun n => (V n).gapDepth
    gapOddPart := fun n => (V n).gapOddPart
    startFactor := ?_
    nextFactor := ?_
    gapFactor := ?_
    depth_coherent := ?_
    startDepth_two_le := ?_
    gapDepth_two_le := ?_
    rise_gap_eq := ?_
    fall_gap_eq := ?_
    equal_lt_gap := ?_
    firstCrossing := fun n =>
      IntegerObstruction.FirstCrossingArithmeticData.ofFirstCrossing (G n)
    firstCrossing_lengths_tend_to_infinity := ?_
  }
  · intro n
    rfl
  · intro n
    change
      TwoAdic.ExactFactor
        ((C.state n).startValue + 1)
        (V n).startDepth (V n).startOddPart
    exact (V n).startFactor
  · intro n
    change
      TwoAdic.ExactFactor
        ((C.state n).startValue + (C.state n).valueGap + 1)
        (V n).nextDepth (V n).nextOddPart
    rw [← (C.state n).nextValue_eq_startValue_add_valueGap]
    exact (V n).nextFactor
  · intro n
    change
      TwoAdic.ExactFactor
        (C.state n).valueGap
        (V n).gapDepth (V n).gapOddPart
    exact (V n).gapFactor
  · intro n
    exact C.valuationDepth_coherent n
  · intro n
    exact (V n).startDepth_two_le
  · intro n
    exact (V n).gapDepth_two_le
  · intro n hRise
    have hcoh := C.valuationDepth_coherent n
    have hlocal : (V n).startDepth < (V n).nextDepth := by
      rw [hcoh]
      exact hRise
    exact (V n).gapDepth_eq_startDepth_of_lt hlocal
  · intro n hFall
    have hcoh := C.valuationDepth_coherent n
    have hlocal : (V n).nextDepth < (V n).startDepth := by
      rw [hcoh]
      exact hFall
    have h := (V n).gapDepth_eq_nextDepth_of_lt hlocal
    rw [hcoh] at h
    exact h
  · intro n hEq
    have hcoh := C.valuationDepth_coherent n
    have hlocal : (V n).startDepth = (V n).nextDepth := by
      rw [hcoh]
      exact hEq
    exact (V n).startDepth_lt_gapDepth_of_eq hlocal
  · intro M
    obtain ⟨J, hJ⟩ := C.firstCrossing_lengths_tend_to_infinity M
    refine ⟨J, ?_⟩
    intro n hn
    exact hJ n hn (G n)

/--
canonical chain から作った pure contracting core の first crossing は
定義上 `chosenFirstCrossing` と一致する。
-/
@[simp] theorem toContractingIntegerChain_firstCrossing
    {O : OddOrbit}
    (C : CanonicalContractingChain O)
    (n : ℕ) :
    (C.toContractingIntegerChain.firstCrossing n) =
      IntegerObstruction.FirstCrossingArithmeticData.ofFirstCrossing
        (C.chosenFirstCrossing n) := by
  rfl

/--
canonical chain の pure block は同じ actual state から作られている。
-/
@[simp] theorem toContractingIntegerChain_block
    {O : OddOrbit}
    (C : CanonicalContractingChain O)
    (n : ℕ) :
    C.toContractingIntegerChain.block n =
      IntegerObstruction.ContractingBlockArithmetic.ofState
        (C.state n) (C.blockData n).contracting := by
  rfl

/--
canonical chain から、actual endpoint floor を保持した
`ExactLateContractingIntegerChain` を同じ first-crossing choice 上で作る。
-/
noncomputable def toExactLateContractingIntegerChain
    {O : OddOrbit}
    (C : CanonicalContractingChain O) :
    IntegerObstruction.ExactLateContractingIntegerChain := by
  classical
  let B : IntegerObstruction.ContractingIntegerChain :=
    C.toContractingIntegerChain
  refine {
    core := B
    lateWitness := ?_
  }
  intro n hLate
  let F : FirstCrossingData (C.state n) :=
    C.chosenFirstCrossing n
  have hLateActual : F.IsLate := by
    unfold IntegerObstruction.ContractingIntegerChain.LateAt at hLate
    change F.length < (C.state n).length at hLate
    exact hLate
  let L : IntegerObstruction.LateBlockArithmeticData (B.block n) := by
    change
      IntegerObstruction.LateBlockArithmeticData
        (IntegerObstruction.ContractingBlockArithmetic.ofState
          (C.state n) (C.blockData n).contracting)
    exact
      IntegerObstruction.LateBlockArithmeticData.ofActualFirstCrossing
        (C.blockData n).contracting F hLateActual
  refine {
    data := L
    crossing_eq := ?_
    floor := ?_
  }
  · change
      IntegerObstruction.FirstCrossingArithmeticData.ofFirstCrossing F =
        B.firstCrossing n
    rfl
  · change
      IntegerObstruction.LateSuffixEndpointFloorData
        (IntegerObstruction.LateBlockArithmeticData.ofActualFirstCrossing
          (C.blockData n).contracting F hLateActual)
    exact
      IntegerObstruction.LateSuffixEndpointFloorData.ofActualFirstCrossing
        (C.blockData n).contracting F hLateActual

/--
任意の Late arithmetic witness が canonical chain の同じ first crossing を
表すなら、その witness 自身が canonical / zero-cylinder refinement を持つ。
-/
theorem canonicalLateArithmetic_of_crossing_eq
    {O : OddOrbit}
    (C : CanonicalContractingChain O)
    (n : ℕ)
    (L : IntegerObstruction.LateBlockArithmeticData
      (C.toContractingIntegerChain.block n))
    (hL :
      L.crossing = C.toContractingIntegerChain.firstCrossing n) :
    IntegerObstruction.CanonicalLateArithmeticData L := by
  have hcross :
      IntegerObstruction.CanonicalFirstCrossingArithmeticData L.crossing := by
    rw [hL, C.toContractingIntegerChain_firstCrossing n]
    exact
      C.firstCrossingArithmetic_canonical n
        (C.chosenFirstCrossing n)
  have hvalid :
      (L.crossing.word ++ L.suffix).Valid := by
    rw [← L.word_eq_crossing_append_suffix]
    change (C.state n).word.Valid
    exact (C.state n).word_valid
  have hfullStart :
      (C.toContractingIntegerChain.block n).base.startValue =
        Word.canonicalStart (L.crossing.word ++ L.suffix) := by
    rw [← L.word_eq_crossing_append_suffix]
    change
      (C.state n).startValue =
        Word.canonicalStart (C.state n).word
    exact (C.blockData n).startCanonical
  have hfullEnd :
      (C.toContractingIntegerChain.block n).base.startValue +
          (C.toContractingIntegerChain.block n).base.valueGap =
        Word.canonicalEnd (L.crossing.word ++ L.suffix) := by
    rw [← L.word_eq_crossing_append_suffix]
    change
      (C.state n).startValue + (C.state n).valueGap =
        Word.canonicalEnd (C.state n).word
    rw [← (C.state n).nextValue_eq_startValue_add_valueGap]
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
            = (C.toContractingIntegerChain.block n).base.startValue :=
              hfullStart.symm
        _ = Word.canonicalStart L.crossing.word :=
              hcross.start_eq
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
  exact {
    crossingCanonical := hcross
    fullStart_eq := hfullStart
    fullEnd_eq := hfullEnd
    zeroDigit := hzero
    allExtensionDigitsZero := hallZero
  }

/--
canonical chain から作った pure contracting core は cutoff 0 で
`CanonicalIntegerRefinement` を持つ。
-/
noncomputable def toCanonicalIntegerRefinement
    {O : OddOrbit}
    (C : CanonicalContractingChain O) :
    IntegerObstruction.CanonicalIntegerRefinement
      C.toContractingIntegerChain := by
  refine {
    cutoff := 0
    crossingCanonical := ?_
    lateCanonical := ?_
  }
  · intro n hn
    rw [C.toContractingIntegerChain_firstCrossing n]
    exact
      C.firstCrossingArithmetic_canonical n
        (C.chosenFirstCrossing n)
  · intro n hn
    unfold IntegerObstruction.CanonicalLateAt
    intro L hL
    exact C.canonicalLateArithmetic_of_crossing_eq n L hL

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

namespace IntegerObstruction

/--
canonical shift 済み actual chain から得た Exact/Late core と、
その同一 core 上の canonical refinement をまとめる。
-/
structure CanonicalExactLateContractingIntegerChain where
  core : ExactLateContractingIntegerChain
  canonical : CanonicalIntegerRefinement core.core

end IntegerObstruction

namespace CanonicalContractingChain

/--
canonical actual chain を pure Exact/Late + canonical obstruction へ落とす。
-/
noncomputable def toCanonicalExactLateContractingIntegerChain
    {O : OddOrbit}
    (C : CanonicalContractingChain O) :
    IntegerObstruction.CanonicalExactLateContractingIntegerChain := by
  refine {
    core := C.toExactLateContractingIntegerChain
    canonical := ?_
  }
  change
    IntegerObstruction.CanonicalIntegerRefinement
      C.toContractingIntegerChain
  exact C.toCanonicalIntegerRefinement

end CanonicalContractingChain

end AdjacentReturn
end Collatz
