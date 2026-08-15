import CollatzLean.Collatz2.Canonical.EndpointFloorRecordDescent

/-!
# Collatz2 Canonical: primitive-reduced record chain と telescope

`EndpointFloorRecordDescent` では primitive + StripReduced current A の任意 proper record
`a` から、一段の packet

  NextRecordBlockData D a

を構成した。その一段は

* `nextIndex > a`
* `d_next < d_a`
* block depth = `criticalHeight(r)+1`
* `d_a-d_next = p-stripRank(r)`
* interior next point は再び critical roof 上

を保持する。

このファイルでは rank `d_a` による strong induction でその one-step kernel を最後まで反復し、
terminal `p` に必ず到達する有限 `RecordChainData` を構成する。
さらに block lengths `r_i` について

  a + sum r_i = p

  h_a + sum (criticalHeight(r_i)+1) = H

  d_a = sum (p-stripRank(r_i))

を exact に telescope する。

これで「full record-chain iteration / telescope」を閉じる。
-/

namespace Collatz2

namespace Word

/-- terminal prefix depth は whole two-depth。 -/
@[simp] theorem prefixTwoDepth_terminal_eq_twoSteps
    (w : Word) :
    prefixTwoDepth w (oddSteps w) = twoSteps w := by
  unfold prefixTwoDepth oddSteps
  simp

end Word

namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

namespace CutRecordTrapData

/-- one-step block が cumulative prefix depth に与える exact increment。 -/
theorem prefixTwoDepth_nextIndex
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (R : CutRecordTrapData D a) :
    Word.prefixTwoDepth D.word R.nextIndex =
      Word.prefixTwoDepth D.word a + Word.twoSteps R.block := by
  have hAdd :=
    Word.prefixTwoDepth_add D.word a R.crossingLength
  simpa [nextIndex, block, cutSuffix] using hAdd

end CutRecordTrapData

/--
record descent の有限 chain。

`step` constructor は interior record から次の chain へ続き、`terminal` constructor で
`nextIndex=p` に到達する。
-/
inductive RecordChainData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    (startIndex : ℕ) → Type
  | terminal
      {a : ℕ}
      (block : NextRecordBlockData D a)
      (terminal_eq : block.trap.nextIndex = Word.oddSteps D.word) :
      RecordChainData D a
  | step
      {a : ℕ}
      (block : NextRecordBlockData D a)
      (interior : block.trap.nextIndex < Word.oddSteps D.word)
      (tail : RecordChainData D block.trap.nextIndex) :
      RecordChainData D a

namespace RecordChainData

/-- chain の block lengths。 -/
def lengths
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ} :
    RecordChainData D a → List ℕ
  | .terminal block _ => [block.trap.crossingLength]
  | .step block _ tail => block.trap.crossingLength :: tail.lengths

/-- chain の minimal contracting depths の総和。 -/
def minimalDepthSum
    (rs : List ℕ) : ℕ :=
  (rs.map (fun r => Word.criticalHeight r + 1)).sum

/-- chain の rank drops の総和。 -/
def rankDropSum
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (rs : List ℕ) : ℤ :=
  (rs.map
    (fun r =>
      (Word.oddSteps D.word : ℤ) -
        (Word.stripRank D.word r : ℤ))).sum

/-- record chain は必ず少なくとも一 block を持つ。 -/
theorem lengths_nonempty
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    C.lengths ≠ [] := by
  cases C <;> simp [lengths]

/-- 全 block length は正。 -/
theorem lengths_pos
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    ∀ r ∈ C.lengths, 0 < r := by
  induction C with
  | terminal block hterm =>
      intro r hr
      simp only [lengths, List.mem_singleton] at hr
      subst r
      exact block.trap.crossingLength_pos
  | step block hinterior tail ih =>
      intro r hr
      simp only [lengths, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact block.trap.crossingLength_pos
      · exact ih r hr

/-- 全 block length は whole denominator より strict に小さい。 -/
theorem lengths_lt_whole
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    ∀ r ∈ C.lengths, r < Word.oddSteps D.word := by
  induction C with
  | terminal block hterm =>
      intro r hr
      simp only [lengths, List.mem_singleton] at hr
      subst r
      exact block.trap.crossingLength_lt_whole
  | step block hinterior tail ih =>
      intro r hr
      simp only [lengths, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact block.trap.crossingLength_lt_whole
      · exact ih r hr

/-- block lengths は start から terminal `p` までを exact に分割する。 -/
theorem start_add_lengths_sum_eq_terminal
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    a + C.lengths.sum = Word.oddSteps D.word := by
  induction C with
  | terminal block hterm =>
      simpa [lengths, CutRecordTrapData.nextIndex] using hterm
  | step block hinterior tail ih =>
      simpa [lengths, CutRecordTrapData.nextIndex, Nat.add_assoc] using ih

/-- minimal block depths は start prefix depth から whole `H` まで exact に telescope する。 -/
theorem prefixDepth_add_minimalDepthSum_eq_twoSteps
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    Word.prefixTwoDepth D.word a + minimalDepthSum C.lengths =
      Word.twoSteps D.word := by
  induction C with
  | terminal block hterm =>
      have hInc := block.trap.prefixTwoDepth_nextIndex
      have hMin := block.block_minimal_depth
      rw [hterm] at hInc
      rw [Word.prefixTwoDepth_terminal_eq_twoSteps] at hInc
      simp only [lengths, minimalDepthSum, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      omega
  | step block hinterior tail ih =>
      have hInc := block.trap.prefixTwoDepth_nextIndex
      have hMin := block.block_minimal_depth
      simp only [lengths, minimalDepthSum, List.map_cons, List.sum_cons]
      dsimp [minimalDepthSum] at ih
      omega

/-- one-step exact rank drop は chain 全体で terminal rank 0 まで telescope する。 -/
theorem chordRankInt_eq_rankDropSum
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    {a : ℕ}
    (C : RecordChainData D a) :
    Word.chordRankInt D.word a = rankDropSum D C.lengths := by
  induction C with
  | terminal block hterm =>
      have hDrop := block.rank_drop_exact
      rw [hterm, Word.chordRankInt_terminal_eq_zero] at hDrop
      simp only [lengths, rankDropSum, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero]
      linarith
  | step block hinterior tail ih =>
      have hDrop := block.rank_drop_exact
      simp only [lengths, rankDropSum, List.map_cons, List.sum_cons]
      dsimp [rankDropSum] at ih
      linarith

end RecordChainData

/--
rank strong induction 用の内部 theorem。
`0 < a < p`, `d_a < p` なら primitive+reduced branch の record chain は terminal まで到達する。
-/
private theorem exists_recordChain_aux
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced)
    (d : ℕ) :
    ∀ a : ℕ,
      0 < a →
      a < Word.oddSteps D.word →
      Word.chordRank D.word a = d →
      d < Word.oddSteps D.word →
      Nonempty (RecordChainData D a) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      intro a haPos haLt hRankEq hdLt
      have hRankLt :
          Word.chordRank D.word a < Word.oddSteps D.word := by
        rw [hRankEq]
        exact hdLt
      let B :=
        D.exists_nextRecordBlock
          a haPos haLt hPrimitive hReduced hRankLt
      by_cases hTerminal :
          B.trap.nextIndex = Word.oddSteps D.word
      · exact ⟨RecordChainData.terminal B hTerminal⟩
      · have hInterior :
          B.trap.nextIndex < Word.oddSteps D.word := by
          have hLe :
              B.trap.nextIndex ≤ Word.oddSteps D.word := by
            simpa [CutRecordTrapData.nextIndex] using
              B.trap.next_le_terminal
          exact lt_of_le_of_ne hLe hTerminal
        have hNextPos : 0 < B.trap.nextIndex := by
          have hStartLtNext := B.trap.cutIndex_lt_nextIndex
          omega
        have hF := D.wordFirstCrossing
        have hStartInt :=
          hF.chordRankInt_eq_natCast haPos haLt
        have hNextInt :=
          hF.chordRankInt_eq_natCast hNextPos hInterior
        have hNatStrict :
            Word.chordRank D.word B.trap.nextIndex <
              Word.chordRank D.word a := by
          have hStrict := B.rank_strict
          rw [hStartInt, hNextInt] at hStrict
          exact_mod_cast hStrict
        have hMeasure :
            Word.chordRank D.word B.trap.nextIndex < d := by
          rw [← hRankEq]
          exact hNatStrict
        have hNextLt :
            Word.chordRank D.word B.trap.nextIndex <
              Word.oddSteps D.word :=
          lt_trans hNatStrict hRankLt
        obtain ⟨tail⟩ :=
          ih
            (Word.chordRank D.word B.trap.nextIndex)
            hMeasure
            B.trap.nextIndex
            hNextPos
            hInterior
            rfl
            hNextLt
        exact ⟨RecordChainData.step B hInterior tail⟩

/--
primitive + reduced branch の任意 proper start rank `<p` から full record chain を構成する。
-/
theorem exists_recordChain
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (a : ℕ)
    (haPos : 0 < a)
    (haLt : a < Word.oddSteps D.word)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced)
    (hRankLt : Word.chordRank D.word a < Word.oddSteps D.word) :
    Nonempty (RecordChainData D a) := by
  exact
    exists_recordChain_aux D hPrimitive hReduced
      (Word.chordRank D.word a)
      a haPos haLt rfl hRankLt

/-- primitive+reduced current A の initial cut `a=1` から terminal までの full chain。 -/
theorem exists_initialRecordChain
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced) :
    Nonempty (RecordChainData D 1) := by
  have hRange :=
    D.firstRank_pos_lt_of_primitive_reduced hPrimitive hReduced
  have hOneLt : 1 < Word.oddSteps D.word := by
    simpa [Word.oddSteps] using D.word_length_gt_one
  exact
    D.exists_recordChain
      1 (by omega) hOneLt hPrimitive hReduced hRange.2

/--
full record-chain decomposition を block-length list だけへ射影した exact packet。
-/
structure RecordBlockDecompositionData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) where
  lengths : List ℕ
  nonempty : lengths ≠ []
  lengths_pos : ∀ r ∈ lengths, 0 < r
  lengths_lt_whole : ∀ r ∈ lengths, r < Word.oddSteps D.word
  odd_length_telescope :
    1 + lengths.sum = Word.oddSteps D.word
  two_depth_telescope :
    1 + RecordChainData.minimalDepthSum lengths = Word.twoSteps D.word
  rank_telescope :
    Word.chordRankInt D.word 1 =
      RecordChainData.rankDropSum D lengths

/--
primitive+reduced current A は minimal FirstCrossing blocks の有限列へ exact に分解される。
-/
theorem exists_recordBlockDecomposition
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O)
    (hPrimitive : D.exponentPair.IsPrimitive)
    (hReduced : D.exponentPair.StripReduced) :
    Nonempty (RecordBlockDecompositionData D) := by
  obtain ⟨C⟩ := D.exists_initialRecordChain hPrimitive hReduced
  let R : RecordBlockDecompositionData D := {
    lengths := C.lengths
    nonempty := C.lengths_nonempty
    lengths_pos := C.lengths_pos
    lengths_lt_whole := C.lengths_lt_whole
    odd_length_telescope := C.start_add_lengths_sum_eq_terminal
    two_depth_telescope := by
      have hDepth := C.prefixDepth_add_minimalDepthSum_eq_twoSteps
      rw [D.prefixTwoDepth_one_eq_one] at hDepth
      exact hDepth
    rank_telescope := C.chordRankInt_eq_rankDropSum
  }
  exact ⟨R⟩

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
