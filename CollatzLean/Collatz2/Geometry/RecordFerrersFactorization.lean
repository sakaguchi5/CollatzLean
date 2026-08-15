import CollatzLean.Collatz2.Geometry.RecordDecomposition
import CollatzLean.Collatz2.Core.BlockAffineFactorization

/-!
# Collatz2 Geometry: Record--Ferrers factorization

record skeleton と local minimal-crossing decorations を分離し、
local Ferrers defect を deterministic critical carry で global defect へ gluing する。
-/

namespace Collatz2
namespace Word

/-- record skeleton は block length 列だけを保持する。 -/
structure RecordSkeleton where
  lengths : List ℕ
  positive : ∀ r ∈ lengths, 0 < r

/-- skeleton に local minimal-crossing words を載せた decoration。 -/
structure DecoratedRecordSkeleton (S : RecordSkeleton) where
  blocks : List Word
  lengths_eq : blocks.map oddSteps = S.lengths
  minimal : ∀ b ∈ blocks, MinimalCrossingBlock b

namespace RecordSkeleton

/-- interior record edges が roof -> roof であるための pure carry 条件。 -/
def interiorCarryConditionFrom (startIndex : ℕ) : List ℕ → Prop
  | [] => False
  | [_r] => True
  | r :: s :: rs =>
      criticalCarry startIndex r = 1 ∧
        interiorCarryConditionFrom (startIndex + r) (s :: rs)

/--
minimal-terminal record skeleton の純 `criticalHeight` carry 条件。
interior edge は roof -> roof なので carry=1、最後は roof -> terminal minimal depth なので carry=0。
-/
def carryConditionFrom (startIndex : ℕ) : List ℕ → Prop
  | [] => False
  | [r] => criticalCarry startIndex r = 0
  | r :: s :: rs =>
      criticalCarry startIndex r = 1 ∧
        carryConditionFrom (startIndex + r) (s :: rs)

/-- full minimal-terminal carry condition は interior carry condition を含む。 -/
theorem interiorCarryConditionFrom_of_carryConditionFrom
    (startIndex : ℕ)
    (rs : List ℕ)
    (h : carryConditionFrom startIndex rs) :
    interiorCarryConditionFrom startIndex rs := by
  induction rs generalizing startIndex with
  | nil =>
      simp [carryConditionFrom] at h
  | cons r rs ih =>
      cases rs with
      | nil =>
          simp [interiorCarryConditionFrom]
      | cons s ss =>
          change
            criticalCarry startIndex r = 1 ∧
              carryConditionFrom (startIndex + r) (s :: ss) at h
          change
            criticalCarry startIndex r = 1 ∧
              interiorCarryConditionFrom (startIndex + r) (s :: ss)
          exact ⟨h.1, ih (startIndex + r) h.2⟩

/-- generic record decomposition から skeleton を忘却する。 -/
def ofDecomposition
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a) : RecordSkeleton :=
  { lengths := D.lengths
    positive := D.lengths_pos }

end RecordSkeleton

namespace RankRecordDecomposition

/-- whole terminal も minimal depth なら record skeleton は純 0/1 carry 条件を満たす。 -/
theorem carryConditionFrom
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a)
    (hWholeMinimal : twoSteps w = criticalHeight (oddSteps w) + 1) :
    RecordSkeleton.carryConditionFrom a D.lengths := by
  induction D with
  | terminal block hterm =>
      simp only [lengths, RecordSkeleton.carryConditionFrom]
      exact block.terminal_criticalCarry_eq_zero_of_whole_minimal
        hterm hWholeMinimal
  | step block hinterior tail ih =>
      have hCarry := block.interior_criticalCarry_eq_one hinterior
      have hTailNe := tail.lengths_nonempty
      cases hLs : tail.lengths with
      | nil =>
          exact False.elim (hTailNe hLs)
      | cons s rs =>
          rw [hLs] at ih
          simp [lengths, hLs, RecordSkeleton.carryConditionFrom, hCarry, ih]

/-- whole FirstCrossing なら record skeleton の final carry `0` も自動的に回収できる。 -/
theorem carryConditionFrom_of_firstCrossing
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a)
    (hWhole : FirstCrossing w) :
    RecordSkeleton.carryConditionFrom a D.lengths := by
  induction D with
  | terminal block hterm =>
      simp only [lengths, RecordSkeleton.carryConditionFrom]
      exact (block.terminal_carry_zero_and_whole_minimal_of_firstCrossing
        hterm hWhole).1
  | step block hinterior tail ih =>
      have hCarry := block.interior_criticalCarry_eq_one hinterior
      have hTailNe := tail.lengths_nonempty
      cases hLs : tail.lengths with
      | nil =>
          exact False.elim (hTailNe hLs)
      | cons s rs =>
          rw [hLs] at ih
          simp [lengths, hLs, RecordSkeleton.carryConditionFrom, hCarry, ih]

/-- generic record decomposition + whole FirstCrossing は whole minimal depth も強制する。 -/
theorem wholeMinimalDepth_of_firstCrossing
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a)
    (hWhole : FirstCrossing w) :
    twoSteps w = criticalHeight (oddSteps w) + 1 := by
  induction D with
  | terminal block hterm =>
      exact (block.terminal_carry_zero_and_whole_minimal_of_firstCrossing
        hterm hWhole).2
  | step block hinterior tail ih =>
      exact ih

/-- generic record decomposition の forward decoration。 -/
def toDecoratedSkeleton
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a) :
    DecoratedRecordSkeleton (RecordSkeleton.ofDecomposition D) :=
  { blocks := D.blocks
    lengths_eq := D.blocks_oddSteps_eq_lengths
    minimal := D.blocks_minimal }

end RankRecordDecomposition

namespace DecoratedRecordSkeleton

/-- local blocks を逆に concatenate した word。 -/
def assemble
    {S : RecordSkeleton}
    (D : DecoratedRecordSkeleton S) : Word :=
  D.blocks.flatten

/-- skeleton の minimal depth 総和。 -/
def minimalDepthSum (S : RecordSkeleton) : ℕ :=
  (S.lengths.map (fun r => criticalHeight r + 1)).sum

/-- decoration が保持する block-length skeleton は入力 skeleton と exact に同一。 -/
theorem blockLengths_eq_skeleton
    {S : RecordSkeleton}
    (D : DecoratedRecordSkeleton S) :
    D.blocks.map oddSteps = S.lengths :=
  D.lengths_eq

/-- forward record decomposition で skeleton は一切変化しない。 -/
theorem forward_blockLengths_eq_recordLengths
    {w : Word} {a : ℕ}
    (R : RankRecordDecomposition w a) :
    (R.toDecoratedSkeleton).blocks.map oddSteps = R.lengths := by
  exact R.blocks_oddSteps_eq_lengths

/-- inverse concatenation は skeleton の odd-step 数を保つ。 -/
theorem assemble_oddSteps
    {S : RecordSkeleton}
    (D : DecoratedRecordSkeleton S) :
    oddSteps D.assemble = S.lengths.sum := by
  unfold assemble
  rw [oddSteps_flatten_blocks]
  unfold blockOddSteps
  rw [D.lengths_eq]

private theorem sum_twoSteps_eq_minimalDepthSum_aux
    (blocks : List Word)
    (lengths : List ℕ)
    (hLengths : blocks.map oddSteps = lengths)
    (hMinimal : ∀ b ∈ blocks, MinimalCrossingBlock b) :
    (blocks.map twoSteps).sum =
      (lengths.map (fun r => criticalHeight r + 1)).sum := by
  induction blocks generalizing lengths with
  | nil =>
      simp at hLengths
      subst lengths
      simp
  | cons b bs ih =>
      cases lengths with
      | nil =>
          simp at hLengths
      | cons r rs =>
          simp only [List.map_cons] at hLengths
          injection hLengths with hbr htail
          have hMb : MinimalCrossingBlock b :=
            hMinimal b (by simp)
          have hTail : ∀ c ∈ bs, MinimalCrossingBlock c := by
            intro c hc
            exact hMinimal c (by simp [hc])
          have hIH := ih rs htail hTail
          simp [hMb.minimalDepth, hbr, hIH]

/-- inverse concatenation の total depth も skeleton だけで決まる。 -/
theorem assemble_twoSteps
    {S : RecordSkeleton}
    (D : DecoratedRecordSkeleton S) :
    twoSteps D.assemble = minimalDepthSum S := by
  unfold assemble minimalDepthSum
  rw [twoSteps_flatten_blocks]
  unfold blockTwoSteps
  exact sum_twoSteps_eq_minimalDepthSum_aux
    D.blocks S.lengths D.lengths_eq D.minimal

/-- forward decomposition を inverse concatenate すると元 suffix に戻る。 -/
theorem assemble_of_decomposition
    {w : Word} {a : ℕ}
    (R : RankRecordDecomposition w a) :
    (R.toDecoratedSkeleton).assemble = w.drop a := by
  exact R.blocks_flatten_eq_drop

end DecoratedRecordSkeleton

/--
critical roof 上の anchor に minimal block を付け、
その境界 carry が `1` なら、新しい anchor も critical roof 上にある。
-/
theorem criticalRoof_append_of_carry_one
    (anchor b : Word)
    (hAnchorRoof :
      twoSteps anchor = criticalHeight (oddSteps anchor))
    (hMb : MinimalCrossingBlock b)
    (hCarryOne :
      criticalCarry (oddSteps anchor) (oddSteps b) = 1) :
    twoSteps (anchor ++ b) =
      criticalHeight (oddSteps (anchor ++ b)) := by
  have hCritAdd :=
    criticalHeight_add_eq (oddSteps anchor) (oddSteps b)
  rw [hCarryOne] at hCritAdd
  rw [
    twoSteps_append,
    oddSteps_append,
    hAnchorRoof,
    hMb.minimalDepth
  ]
  omega

/--
一つの minimal block が global chord を跨ぐなら、
singleton の terminal rank-record decomposition を構成できる。
-/
def terminalRankRecordDecomposition_of_single
    (anchor b : Word)
    (hMb : MinimalCrossingBlock b)
    (hAnchorRoof :
      twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCriticalBelow :
      ∀ j : ℕ, 0 < j →
        oddSteps (anchor ++ b) * criticalHeight j <
          twoSteps (anchor ++ b) * j)
    (hDropB :
      twoSteps (anchor ++ b) * oddSteps b <
        oddSteps (anchor ++ b) *
          (criticalHeight (oddSteps b) + 1)) :
    RankRecordDecomposition
      (anchor ++ b) (oddSteps anchor) := by
  let w : Word := anchor ++ b
  let a : ℕ := oddSteps anchor
  let r : ℕ := oddSteps b
  have hBlockEq :
      recordBlockWord w a r = b := by
    dsimp [w, a, r]
    simp [recordBlockWord, oddSteps]
  have hBlockLen :
      oddSteps (recordBlockWord w a r) = r := by
    rw [hBlockEq]
  have hStartRoofW :
      prefixTwoDepth w a = criticalHeight a := by
    have h := prefixTwoDepth_append_left anchor b
    exact h.trans hAnchorRoof
  have hNextEq :
      a + r = oddSteps w := by
    dsimp [w, a, r]
    simp
  have hCrit :
      ∀ j : ℕ, 0 < j → j < r →
        oddSteps w * criticalHeight j <
          twoSteps w * j := by
    intro j hjPos hjLt
    simpa [w] using hCriticalBelow j hjPos
  have M' :
      MinimalCrossingBlock (recordBlockWord w a r) := by
    simpa [hBlockEq] using hMb
  let R : RankRecordBlock w a :=
    RankRecordBlock.ofMinimalAtRoof
      hMb.oddSteps_pos
      (Nat.le_of_eq hNextEq)
      hBlockLen
      M'
      hStartRoofW
      hCrit
      (by
        simpa [w, r] using hDropB)
      (by
        intro hInterior
        omega)
  have hRLength : R.length = r := by
    rfl
  have hTerm :
      a + R.length = oddSteps w := by
    rw [hRLength]
    exact hNextEq
  simpa [w] using
    (RankRecordDecomposition.terminal R hTerm)

/--
一つの rank-record block を既存の tail decomposition の前へ付ける。
再帰そのものは行わない pure prepend constructor。
-/
def prependRankRecordDecomposition
    (anchor b : Word)
    (tailBlocks : List Word)
    (hMb : MinimalCrossingBlock b)
    (hAnchorRoof :
      twoSteps anchor = criticalHeight (oddSteps anchor))
    (hNextAnchorRoof :
      twoSteps (anchor ++ b) =
        criticalHeight (oddSteps (anchor ++ b)))
    (hTailOddPos :
      0 < oddSteps tailBlocks.flatten)
    (hCriticalBelow :
      ∀ j : ℕ, 0 < j →
        oddSteps (anchor ++ (b :: tailBlocks).flatten) *
            criticalHeight j <
          twoSteps (anchor ++ (b :: tailBlocks).flatten) * j)
    (hDropB :
      twoSteps (anchor ++ (b :: tailBlocks).flatten) *
          oddSteps b <
        oddSteps (anchor ++ (b :: tailBlocks).flatten) *
          (criticalHeight (oddSteps b) + 1))
    (tailD :
      RankRecordDecomposition
        ((anchor ++ b) ++ tailBlocks.flatten)
        (oddSteps (anchor ++ b))) :
    RankRecordDecomposition
      (anchor ++ (b :: tailBlocks).flatten)
      (oddSteps anchor) := by
  let w : Word :=
    anchor ++ (b :: tailBlocks).flatten
  let a : ℕ := oddSteps anchor
  let r : ℕ := oddSteps b
  have hBlockEq :
      recordBlockWord w a r = b := by
    dsimp [w, a, r]
    simp [recordBlockWord, oddSteps]
  have hBlockLen :
      oddSteps (recordBlockWord w a r) = r := by
    rw [hBlockEq]
  have hStartRoofW :
      prefixTwoDepth w a = criticalHeight a := by
    have h :=
      prefixTwoDepth_append_left
        anchor (b :: tailBlocks).flatten
    exact h.trans hAnchorRoof
  have hNextRoofEq :
      prefixTwoDepth w (a + r) =
        criticalHeight (a + r) := by
    have h :=
      prefixTwoDepth_append_left
        (anchor ++ b) tailBlocks.flatten
    have h' := h.trans hNextAnchorRoof
    simpa [w, a, r, List.append_assoc] using h'
  have hInterior : a + r < oddSteps w := by
    dsimp [w, a, r]
    simp only [oddSteps_append]
    omega
  have hCrit :
      ∀ j : ℕ, 0 < j → j < r →
        oddSteps w * criticalHeight j <
          twoSteps w * j := by
    intro j hjPos hjLt
    simpa [w] using hCriticalBelow j hjPos
  have M' :
      MinimalCrossingBlock
        (recordBlockWord w a r) := by
    simpa [hBlockEq] using hMb
  let R : RankRecordBlock w a :=
    RankRecordBlock.ofMinimalAtRoof
      hMb.oddSteps_pos
      (Nat.le_of_lt hInterior)
      hBlockLen
      M'
      hStartRoofW
      hCrit
      (by
        simpa [w, r] using hDropB)
      (fun _ => hNextRoofEq)
  have hTailD' :
      RankRecordDecomposition w (a + r) := by
    simpa [
      w,
      a,
      r,
      List.append_assoc,
      oddSteps_append
    ] using tailD
  have hRLength : R.length = r := by
    rfl
  have hRInterior :
      a + R.length < oddSteps w := by
    rw [hRLength]
    exact hInterior
  exact
    RankRecordDecomposition.step
      R hRInterior hTailD'

/--
global critical-below 条件は append の括弧を変えても tail 側へ移送できる。
-/
theorem criticalBelow_of_tail
    (anchor b : Word)
    (tailBlocks : List Word)
    (hCriticalBelow :
      ∀ j : ℕ, 0 < j →
        oddSteps (anchor ++ (b :: tailBlocks).flatten) *
            criticalHeight j <
          twoSteps (anchor ++ (b :: tailBlocks).flatten) * j) :
    ∀ j : ℕ, 0 < j →
      oddSteps ((anchor ++ b) ++ tailBlocks.flatten) *
          criticalHeight j <
        twoSteps ((anchor ++ b) ++ tailBlocks.flatten) * j := by
  intro j hjPos
  simpa [List.append_assoc] using
    hCriticalBelow j hjPos

/--
global drop 条件は tail の各 block にそのまま移送できる。
-/
theorem dropCondition_of_tail
    (anchor b : Word)
    (tailBlocks : List Word)
    (hDrop :
      ∀ d ∈ b :: tailBlocks,
        twoSteps (anchor ++ (b :: tailBlocks).flatten) *
            oddSteps d <
          oddSteps (anchor ++ (b :: tailBlocks).flatten) *
            (criticalHeight (oddSteps d) + 1)) :
    ∀ d ∈ tailBlocks,
      twoSteps ((anchor ++ b) ++ tailBlocks.flatten) *
          oddSteps d <
        oddSteps ((anchor ++ b) ++ tailBlocks.flatten) *
          (criticalHeight (oddSteps d) + 1) := by
  intro d hd
  have hd' : d ∈ b :: tailBlocks := by
    simp [hd]
  simpa [List.append_assoc] using
    hDrop d hd'

/-- nonempty minimal blocks の flatten は少なくとも一つ odd step を持つ。 -/
theorem oddSteps_flatten_pos_of_nonempty_minimal
    (bs : List Word)
    (hNonempty : bs ≠ [])
    (hMinimal : ∀ b ∈ bs, MinimalCrossingBlock b) :
    0 < oddSteps bs.flatten := by
  cases bs with
  | nil =>
      exact False.elim (hNonempty rfl)
  | cons b bs =>
      have hMb : MinimalCrossingBlock b :=
        hMinimal b (by simp)
      change 0 < oddSteps (b ++ bs.flatten)
      rw [oddSteps_append]
      exact Nat.add_pos_left hMb.oddSteps_pos _

/--
`b :: tailBlocks` の nonterminal inverse step に必要な
再帰側の仮定をまとめた packet。
-/
structure MinimalBlocksTailStepData
    (anchor b : Word)
    (tailBlocks : List Word) : Prop where

  headMinimal :
    MinimalCrossingBlock b

  tail_nonempty :
    tailBlocks ≠ []

  nextAnchorRoof :
    twoSteps (anchor ++ b) =
      criticalHeight (oddSteps (anchor ++ b))

  tailMinimal :
    ∀ d ∈ tailBlocks,
      MinimalCrossingBlock d

  tailCarry :
    RecordSkeleton.interiorCarryConditionFrom
      (oddSteps (anchor ++ b))
      (tailBlocks.map oddSteps)

  tailCriticalBelow :
    ∀ j : ℕ, 0 < j →
      oddSteps ((anchor ++ b) ++ tailBlocks.flatten) *
          criticalHeight j <
        twoSteps ((anchor ++ b) ++ tailBlocks.flatten) * j

  tailDrop :
    ∀ d ∈ tailBlocks,
      twoSteps ((anchor ++ b) ++ tailBlocks.flatten) *
          oddSteps d <
        oddSteps ((anchor ++ b) ++ tailBlocks.flatten) *
          (criticalHeight (oddSteps d) + 1)

  tailOddPos :
    0 < oddSteps tailBlocks.flatten

  headDrop :
    twoSteps (anchor ++ (b :: tailBlocks).flatten) *
        oddSteps b <
      oddSteps (anchor ++ (b :: tailBlocks).flatten) *
        (criticalHeight (oddSteps b) + 1)

/--
nonterminal `b :: tailBlocks` の global hypotheses から、
再帰に必要な tail packet を生成する。
-/
theorem minimalBlocksTailStepData_of_cons
    (anchor b : Word)
    (tailBlocks : List Word)
    (hTailNonempty : tailBlocks ≠ [])
    (hMinimal :
      ∀ d ∈ b :: tailBlocks,
        MinimalCrossingBlock d)
    (hAnchorRoof :
      twoSteps anchor =
        criticalHeight (oddSteps anchor))
    (hCarry :
      RecordSkeleton.interiorCarryConditionFrom
        (oddSteps anchor)
        ((b :: tailBlocks).map oddSteps))
    (hCriticalBelow :
      ∀ j : ℕ, 0 < j →
        oddSteps (anchor ++ (b :: tailBlocks).flatten) *
            criticalHeight j <
          twoSteps (anchor ++ (b :: tailBlocks).flatten) * j)
    (hDrop :
      ∀ d ∈ b :: tailBlocks,
        twoSteps (anchor ++ (b :: tailBlocks).flatten) *
            oddSteps d <
          oddSteps (anchor ++ (b :: tailBlocks).flatten) *
            (criticalHeight (oddSteps d) + 1)) :
    MinimalBlocksTailStepData
      anchor b tailBlocks := by
  cases tailBlocks with
  | nil =>
      exact False.elim (hTailNonempty rfl)
  | cons c cs =>
      have hMb :
          MinimalCrossingBlock b := by
        exact hMinimal b (by simp)
      have hTailMinimal :
          ∀ d ∈ c :: cs,
            MinimalCrossingBlock d := by
        intro d hd
        apply hMinimal d
        exact List.mem_cons_of_mem b hd
      change
        criticalCarry
            (oddSteps anchor)
            (oddSteps b) = 1 ∧
          RecordSkeleton.interiorCarryConditionFrom
            (oddSteps anchor + oddSteps b)
            ((c :: cs).map oddSteps)
        at hCarry
      have hNextAnchorRoof :
          twoSteps (anchor ++ b) =
            criticalHeight (oddSteps (anchor ++ b)) :=
        criticalRoof_append_of_carry_one
          anchor
          b
          hAnchorRoof
          hMb
          hCarry.1
      have hTailCarry :
          RecordSkeleton.interiorCarryConditionFrom
            (oddSteps (anchor ++ b))
            ((c :: cs).map oddSteps) := by
        simpa [oddSteps_append] using hCarry.2
      have hTailCritical :
          ∀ j : ℕ, 0 < j →
            oddSteps
                ((anchor ++ b) ++ (c :: cs).flatten) *
                criticalHeight j <
              twoSteps
                ((anchor ++ b) ++ (c :: cs).flatten) * j := by
        exact
          criticalBelow_of_tail
            anchor
            b
            (c :: cs)
            hCriticalBelow
      have hTailDrop :
          ∀ d ∈ c :: cs,
            twoSteps
                ((anchor ++ b) ++ (c :: cs).flatten) *
                oddSteps d <
              oddSteps
                ((anchor ++ b) ++ (c :: cs).flatten) *
                (criticalHeight (oddSteps d) + 1) := by
        exact
          dropCondition_of_tail
            anchor
            b
            (c :: cs)
            hDrop
      have hTailOddPos :
          0 < oddSteps (c :: cs).flatten :=
        oddSteps_flatten_pos_of_nonempty_minimal
          (c :: cs)
          (by simp)
          hTailMinimal
      have hHeadDrop :
          twoSteps
              (anchor ++ (b :: c :: cs).flatten) *
              oddSteps b <
            oddSteps
                (anchor ++ (b :: c :: cs).flatten) *
                (criticalHeight (oddSteps b) + 1) := by
        exact hDrop b (by simp)
      exact {
        headMinimal := hMb
        tail_nonempty := by
          simp
        nextAnchorRoof := hNextAnchorRoof
        tailMinimal := hTailMinimal
        tailCarry := hTailCarry
        tailCriticalBelow := hTailCritical
        tailDrop := hTailDrop
        tailOddPos := hTailOddPos
        headDrop := hHeadDrop
      }

/--
任意の local minimal blocks を concatenate しても、

* start が critical roof 上、
* interior skeleton carry が 1、
* global chord が各 local critical roof より上、
* 各 block terminal が global chord を strict に跨ぐ

なら、同じ block-length skeleton を持つ genuine rank-record decomposition を逆構成できる。
-/
def rankRecordDecomposition_of_minimalBlocks
    (anchor : Word)
    (bs : List Word)
    (hNonempty : bs ≠ [])
    (hMinimal :
      ∀ b ∈ bs, MinimalCrossingBlock b)
    (hAnchorRoof :
      twoSteps anchor =
        criticalHeight (oddSteps anchor))
    (hCarry :
      RecordSkeleton.interiorCarryConditionFrom
        (oddSteps anchor) (bs.map oddSteps))
    (hCriticalBelow :
      ∀ j : ℕ, 0 < j →
        oddSteps (anchor ++ bs.flatten) *
            criticalHeight j <
          twoSteps (anchor ++ bs.flatten) * j)
    (hDrop :
      ∀ b ∈ bs,
        twoSteps (anchor ++ bs.flatten) *
            oddSteps b <
          oddSteps (anchor ++ bs.flatten) *
            (criticalHeight (oddSteps b) + 1)) :
    RankRecordDecomposition
      (anchor ++ bs.flatten)
      (oddSteps anchor) := by
  induction bs generalizing anchor with
  | nil =>
      exact False.elim (hNonempty rfl)
  | cons b bs ih =>
      cases bs with
      | nil =>
          have hMb :
              MinimalCrossingBlock b :=
            hMinimal b (by simp)
          have hCriticalBelowSingle :
              ∀ j : ℕ, 0 < j →
                oddSteps (anchor ++ b) *
                    criticalHeight j <
                  twoSteps (anchor ++ b) * j := by
            intro j hjPos
            simpa using
              hCriticalBelow j hjPos
          have hDropSingle :
              twoSteps (anchor ++ b) *
                  oddSteps b <
                oddSteps (anchor ++ b) *
                  (criticalHeight (oddSteps b) + 1) := by
            simpa using
              hDrop b (by simp)
          have hD :
              RankRecordDecomposition
                (anchor ++ b)
                (oddSteps anchor) :=
            terminalRankRecordDecomposition_of_single
              anchor
              b
              hMb
              hAnchorRoof
              hCriticalBelowSingle
              hDropSingle
          simpa using hD
      | cons c cs =>
          let tailBlocks : List Word := c :: cs
          have hMinimal' :
              ∀ d ∈ b :: tailBlocks,
                MinimalCrossingBlock d := by
            intro d hd
            exact hMinimal d (by
              simpa [tailBlocks] using hd)
          have hCarry' :
              RecordSkeleton.interiorCarryConditionFrom
                (oddSteps anchor)
                ((b :: tailBlocks).map oddSteps) := by
            simpa [tailBlocks] using hCarry
          have hCriticalBelow' :
              ∀ j : ℕ, 0 < j →
                oddSteps
                    (anchor ++
                      (b :: tailBlocks).flatten) *
                    criticalHeight j <
                  twoSteps
                    (anchor ++
                      (b :: tailBlocks).flatten) * j := by
            intro j hjPos
            simpa [tailBlocks] using
              hCriticalBelow j hjPos
          have hDrop' :
              ∀ d ∈ b :: tailBlocks,
                twoSteps
                    (anchor ++
                      (b :: tailBlocks).flatten) *
                    oddSteps d <
                  oddSteps
                    (anchor ++
                      (b :: tailBlocks).flatten) *
                    (criticalHeight
                      (oddSteps d) + 1) := by
            intro d hd
            exact hDrop d (by
              simpa [tailBlocks] using hd)
          have T :
              MinimalBlocksTailStepData
                anchor b tailBlocks :=
            minimalBlocksTailStepData_of_cons
              anchor
              b
              tailBlocks
              (by simp [tailBlocks])
              hMinimal'
              hAnchorRoof
              hCarry'
              hCriticalBelow'
              hDrop'
          have hTailD :=
            ih
              (anchor := anchor ++ b)
              T.tail_nonempty
              T.tailMinimal
              T.nextAnchorRoof
              T.tailCarry
              T.tailCriticalBelow
              T.tailDrop
          have hResult :=
            prependRankRecordDecomposition
              anchor
              b
              tailBlocks
              T.headMinimal
              hAnchorRoof
              T.nextAnchorRoof
              T.tailOddPos
              hCriticalBelow'
              T.headDrop
              hTailD
          simpa [tailBlocks] using hResult

/--
record start `a` が roof 上にあるとき、local interior Ferrers defect は
0/1 critical carry を足すだけで global defect へ移る。
-/
theorem criticalDefect_recordBlock_interior
    {w : Word}
    {a : ℕ}
    (R : RankRecordBlock w a)
    {j : ℕ}
    (hjPos : 0 < j)
    (hjLt : j < R.length) :
    criticalDefect w (a + j) =
      criticalDefect R.word j + criticalCarry a j := by
  have hjLe : j ≤ R.length :=
    Nat.le_of_lt hjLt
  have hLocalLen : j < oddSteps R.word := by
    change j < oddSteps (recordBlockWord w a R.length)
    rw [R.block_length]
    exact hjLt
  have hLocalLe :
      prefixTwoDepth R.word j ≤ criticalHeight j :=
    R.minimal.firstCrossing.prefixTwoDepth_le_criticalHeight
      hjPos hLocalLen
  have hBlockDepth :
      prefixTwoDepth R.word j =
        prefixTwoDepth (w.drop a) j := by
    simpa [RankRecordBlock.word] using
      prefixTwoDepth_recordBlockWord
        w a R.length j hjLe
  have hAdd :=
    prefixTwoDepth_add_drop w a j
  have hCarry :=
    criticalHeight_add_eq a j
  rw [hBlockDepth] at hLocalLe
  unfold criticalDefect
  rw [hAdd, R.start_roof, hCarry, hBlockDepth]
  omega

/-- critical carry は各 interior column で 0/1。 -/
theorem criticalDefect_recordBlock_interior_cases
    {w : Word}
    {a : ℕ}
    (R : RankRecordBlock w a)
    {j : ℕ}
    (hjPos : 0 < j)
    (hjLt : j < R.length) :
    criticalDefect w (a + j) = criticalDefect R.word j ∨
      criticalDefect w (a + j) = criticalDefect R.word j + 1 := by
  rw [criticalDefect_recordBlock_interior R hjPos hjLt]
  rcases criticalCarry_eq_zero_or_one a j with h0 | h1
  · left
    rw [h0, add_zero]
  · right
    rw [h1]

end Word
end Collatz2
