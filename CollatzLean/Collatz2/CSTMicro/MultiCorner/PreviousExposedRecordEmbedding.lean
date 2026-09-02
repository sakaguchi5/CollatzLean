import CollatzLean.Collatz2.CSTMicro.MultiCorner.RecordFerrersExposedProvenance

/-!
# MultiCorner: previous exposed cut の record 内部埋め込み

hard Case II で現れる canonical previous exposed cut は、一般には record start ではない。
record start は critical roof 上にあり defect が zero だが、exposed cut は positive depth を持つ。

このファイルでは次の三段を固定する。

1. rank-record decomposition の start と terminal の間にある positive-defect cut は、
   record 境界には置けないため、必ずどれか一つの record block の strict interior に入る。
2. actual minimal-B から得られる Pure-B profile depth は、actual exponent word の
   `criticalDefect` と exact に一致する。
3. canonical previous exposed cut を containing record block の内部 cut として表し、
   Record--Ferrers factorization から `RecordFerrersCutProvenance` を構成する。

重要: previous exposed cut 自身を `RankRecordDecomposition` の start としてはいない。
-/

namespace Collatz2
namespace Word

/--
rank-record decomposition 内の strict interior cut を表す最小 packet。
`cut = recordStart + offset` で、`offset` は containing block の真の内部にある。
-/
structure InternalRecordCutEmbedding
    (w : Word)
    (cut : ℕ) where
  recordStart : ℕ
  block : RankRecordBlock w recordStart
  offset : ℕ
  cut_eq : cut = recordStart + offset
  offset_pos : 0 < offset
  offset_lt : offset < block.length

namespace RankRecordDecomposition

/--
positive critical defect を持つ proper cut は、rank-record decomposition の
どれか一つの block の strict interior に必ず入る。

record 境界では `next_roof_if_interior` により actual depth = critical roof なので
`criticalDefect = 0`。従って positive-defect cut は境界に一致できない。
-/
theorem exists_internalRecordCutEmbedding_of_criticalDefect_pos
    {w : Word}
    {a k : ℕ}
    (D : RankRecordDecomposition w a)
    (haLt : a < k)
    (hkLt : k < oddSteps w)
    (hDefPos : 0 < criticalDefect w k) :
    Nonempty (InternalRecordCutEmbedding w k) := by
  induction D generalizing k with
  | terminal block hTerminal =>
      rename_i a0
      let j : ℕ := k - a0
      have hCutEq : k = a0 + j := by
        dsimp [j]
        omega
      have hjPos : 0 < j := by
        dsimp [j]
        omega
      have hjLt : j < block.length := by
        dsimp [j]
        omega
      exact ⟨{
        recordStart := a0
        block := block
        offset := j
        cut_eq := hCutEq
        offset_pos := hjPos
        offset_lt := hjLt
      }⟩
  | step block hInterior tail ih =>
      rename_i a0
      by_cases hkBlock : k < a0 + block.length
      · let j : ℕ := k - a0
        have hCutEq : k = a0 + j := by
          dsimp [j]
          omega
        have hjPos : 0 < j := by
          dsimp [j]
          omega
        have hjLt : j < block.length := by
          dsimp [j]
          omega
        exact ⟨{
          recordStart := a0
          block := block
          offset := j
          cut_eq := hCutEq
          offset_pos := hjPos
          offset_lt := hjLt
        }⟩
      · by_cases hkBoundary : k = a0 + block.length
        · have hRoof :
              prefixTwoDepth w k = criticalHeight k := by
            have h := block.next_roof_if_interior hInterior
            rw [← hkBoundary] at h
            exact h
          have hZero : criticalDefect w k = 0 := by
            unfold criticalDefect
            rw [hRoof]
            omega
          rw [hZero] at hDefPos
          omega
        · have hNextLt : a0 + block.length < k := by
            omega
          exact ih hNextLt hkLt hDefPos

end RankRecordDecomposition
end Word

namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
containing record block の exact factorization から CSTMicro provenance を作る。
ここでは global profile depth と word の `criticalDefect` の一致だけを bridge 仮定として受け取る。
-/
def RecordFerrersCutProvenance.ofInternalRecordCut
    (P : PureBProfileObstruction)
    (w : Word)
    {a j : ℕ}
    (R : Word.RankRecordBlock w a)
    (hjPos : 0 < j)
    (hjLt : j < R.length)
    (hDepth : P.h (a + j) = Word.criticalDefect w (a + j)) :
    RecordFerrersCutProvenance P (a + j) :=
  RecordFerrersCutProvenance.ofFactorization
    P
    (a + j)
    (Word.criticalDefect R.word j)
    (Word.criticalCarry a j)
    (by
      calc
        P.h (a + j) = Word.criticalDefect w (a + j) := hDepth
        _ = Word.criticalDefect R.word j + Word.criticalCarry a j :=
          Word.criticalDefect_recordBlock_interior R hjPos hjLt)
    (Word.criticalCarry_le_one a j)

/--
actual minimal-B の Pure-B profile depth は、actual exponent word の
`criticalDefect` そのもの。

これは `profileEndpointCheckpoint = actual prefixTwoDepth` と
`profileCheckpoint = beattyIndex - h` を引き算するだけの exact bridge。
-/
theorem MinimalActualABObstructionPacket.profileDepth_eq_actualCriticalDefect
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (hk : k < (M.toPureBProfileObstruction hL).m) :
    (M.toPureBProfileObstruction hL).h k =
      Word.criticalDefect (exponentWordOfParity M.word) k := by
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  have hCheckpoint :=
    M.profileEndpointCheckpoint_eq_actualPrefixTwoDepth
      hL (k := k) (Nat.le_of_lt hk)
  have hDepthLe : P.h k ≤ beattyIndex k :=
    P.admissible.depth_le hk
  have hCheckpoint' :
      profileCheckpoint P.h k = Word.prefixTwoDepth w k := by
    calc
      profileCheckpoint P.h k = P.profileEndpointCheckpoint k :=
        (P.profileEndpointCheckpoint_of_lt hk).symm
      _ = Word.prefixTwoDepth w k := by
        simpa [P, w] using hCheckpoint
  unfold profileCheckpoint at hCheckpoint'
  unfold Word.criticalDefect
  rw [← beattyIndex_eq_wordCriticalHeight_all]
  simpa [P, w] using (show P.h k = beattyIndex k - Word.prefixTwoDepth w k by
    omega)

/--
canonical previous exposed cut の containing record block と provenance をまとめる packet。
previous exposed 自身は record start ではなく、`offset > 0` の strict interior cut。
-/
structure PreviousExposedRecordEmbedding
    (P : PureBProfileObstruction)
    (w : Word)
    (N : LastTwoExposedNormalForm P) where
  recordStart : ℕ
  block : Word.RankRecordBlock w recordStart
  offset : ℕ
  previous_eq : N.previous = recordStart + offset
  offset_pos : 0 < offset
  offset_lt : offset < block.length
  provenance : RecordFerrersCutProvenance P N.previous
  provenance_localDefect_eq :
    provenance.localDefect = Word.criticalDefect block.word offset
  provenance_glueCarry_eq :
    provenance.glueCarry = Word.criticalCarry recordStart offset

namespace PreviousExposedRecordEmbedding

/-- containing block の start は canonical previous exposed より strict に左。 -/
theorem recordStart_lt_previous
    {P : PureBProfileObstruction}
    {w : Word}
    {N : LastTwoExposedNormalForm P}
    (E : PreviousExposedRecordEmbedding P w N) :
    E.recordStart < N.previous := by
  rw [E.previous_eq]
  exact Nat.lt_add_of_pos_right E.offset_pos

/-- canonical previous exposed は containing block の終端より strict に左。 -/
theorem previous_lt_recordEnd
    {P : PureBProfileObstruction}
    {w : Word}
    {N : LastTwoExposedNormalForm P}
    (E : PreviousExposedRecordEmbedding P w N) :
    N.previous < E.recordStart + E.block.length := by
  rw [E.previous_eq]
  exact Nat.add_lt_add_left E.offset_lt E.recordStart

/-- canonical previous exposed は実際に positive provenance source を持つ。 -/
theorem source
    {P : PureBProfileObstruction}
    {w : Word}
    {N : LastTwoExposedNormalForm P}
    (E : PreviousExposedRecordEmbedding P w N) :
    0 < E.provenance.localDefect ∨ E.provenance.glueCarry = 1 := by
  have hExposed : P.IsExposedPredecessorIndex N.previous :=
    (P.mem_exposedPredecessorSet_iff).1 N.previous_mem
  exact E.provenance.source_of_exposed hExposed

end PreviousExposedRecordEmbedding

namespace MinimalActualABObstructionPacket

/--
actual minimal-B の canonical previous exposed cut を、0 から始まる rank-record decomposition
の containing block 内へ埋め込む。

入力 `D` は actual exponent word 全体の record decomposition。
出力では previous exposed が strict interior cut であることに加え、
local Ferrers defect + 0/1 critical carry という provenance まで exact に保持する。
-/
noncomputable def previousExposedRecordEmbedding
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL))
    (D : Word.RankRecordDecomposition
      (exponentWordOfParity M.word) 0) :
    PreviousExposedRecordEmbedding
      (M.toPureBProfileObstruction hL)
      (exponentWordOfParity M.word)
      N := by
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  have hExposed : P.IsExposedPredecessorIndex N.previous := by
    exact (P.mem_exposedPredecessorSet_iff).1 N.previous_mem
  have hPrevPos : 0 < N.previous := by
    by_contra hNot
    have hZero : N.previous = 0 := Nat.eq_zero_of_not_pos hNot
    have hDepthPos : 0 < P.h N.previous := hExposed.depth_pos
    have hDepthLe : P.h N.previous ≤ beattyIndex N.previous :=
      P.admissible.depth_le hExposed.lt_m
    rw [hZero] at hDepthPos hDepthLe
    rw [beattyIndex_zero] at hDepthLe
    omega
  have hm : P.m = Word.oddSteps w := by
    calc
      P.m = oddCount M.word := by
        simpa [P] using
          M.toPureBProfileObstruction_m_eq_wordOddCount hL
      _ = Word.oddSteps w := by
        simp [w, oddSteps_exponentWordOfParity]
  have hPrevLt : N.previous < Word.oddSteps w := by
    rw [← hm]
    exact hExposed.lt_m
  have hDepth :
      P.h N.previous = Word.criticalDefect w N.previous := by
    simpa [P, w] using
      profileDepth_eq_actualCriticalDefect M hL hExposed.lt_m
  have hDefPos : 0 < Word.criticalDefect w N.previous := by
    rw [← hDepth]
    exact hExposed.depth_pos
  have hI :
      Nonempty (Word.InternalRecordCutEmbedding w N.previous) :=
    D.exists_internalRecordCutEmbedding_of_criticalDefect_pos
      hPrevPos hPrevLt hDefPos
  let I : Word.InternalRecordCutEmbedding w N.previous :=
    Classical.choice hI
  have hDepthAt :
      P.h (I.recordStart + I.offset) =
        Word.criticalDefect w (I.recordStart + I.offset) := by
    rw [← I.cut_eq]
    exact hDepth
  have hFactorization :
      P.h N.previous =
        Word.criticalDefect I.block.word I.offset +
          Word.criticalCarry I.recordStart I.offset := by
    calc
      P.h N.previous =
          P.h (I.recordStart + I.offset) := by
            exact congrArg (fun k => P.h k) I.cut_eq
      _ =
          Word.criticalDefect I.block.word I.offset +
            Word.criticalCarry I.recordStart I.offset := by
            exact
              (RecordFerrersCutProvenance.ofInternalRecordCut
                P w I.block I.offset_pos I.offset_lt hDepthAt).factorization
  let Q : RecordFerrersCutProvenance P N.previous :=
    RecordFerrersCutProvenance.ofFactorization
      P
      N.previous
      (Word.criticalDefect I.block.word I.offset)
      (Word.criticalCarry I.recordStart I.offset)
      hFactorization
      (Word.criticalCarry_le_one I.recordStart I.offset)
  exact {
    recordStart := I.recordStart
    block := I.block
    offset := I.offset
    previous_eq := I.cut_eq
    offset_pos := I.offset_pos
    offset_lt := I.offset_lt
    provenance := Q
    provenance_localDefect_eq := rfl
    provenance_glueCarry_eq := rfl
  }

end MinimalActualABObstructionPacket

end MultiCorner
end CSTMicro
end Collatz2
