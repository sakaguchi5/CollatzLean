import CollatzLean.Collatz2.Geometry.MinimalCrossingBlock

/-!
# Collatz2 Geometry: generic rank-record decomposition

current A に依存しない record object。
whole word の chord rank に対し、record start から interior では rank が上にあり、
block terminal で strict に下がる minimal FirstCrossing excursion を一段とする。
-/

namespace Collatz2
namespace Word

/-- append の左 block 終端では cumulative depth は左 block の total depth。 -/
theorem prefixTwoDepth_append_left
    (u v : Word) :
    prefixTwoDepth (u ++ v) (oddSteps u) = twoSteps u := by
  unfold prefixTwoDepth oddSteps
  simp

/-- cut `a` から長さ `r` の word block。 -/
def recordBlockWord (w : Word) (a r : ℕ) : Word :=
  (w.drop a).take r

/-- cumulative prefix depth の add/drop 分解。 -/
theorem prefixTwoDepth_add_drop
    (w : Word)
    (a r : ℕ) :
    prefixTwoDepth w (a + r) =
      prefixTwoDepth w a + prefixTwoDepth (w.drop a) r := by
  unfold prefixTwoDepth
  have hTake :
      w.take (a + r) = w.take a ++ (w.drop a).take r := by
    induction a generalizing w with
    | zero => simp
    | succ a ih =>
        cases w with
        | nil => simp
        | cons x w => simp [Nat.succ_add, ih]
  rw [hTake, twoSteps_append]

/-- block prefix を suffix prefix として読む。 -/
theorem prefixTwoDepth_recordBlockWord
    (w : Word)
    (a r j : ℕ)
    (hj : j ≤ r) :
    prefixTwoDepth (recordBlockWord w a r) j =
      prefixTwoDepth (w.drop a) j := by
  unfold recordBlockWord prefixTwoDepth
  simp [List.take_take, Nat.min_eq_left hj]

/-- cut shift による signed rank difference の generic exact formula。 -/
theorem chordRankInt_add_sub
    (w : Word)
    (a r : ℕ) :
    chordRankInt w (a + r) - chordRankInt w a =
      (twoSteps w : ℤ) * (r : ℤ) -
        (oddSteps w : ℤ) * (prefixTwoDepth (w.drop a) r : ℤ) := by
  have hDepth := prefixTwoDepth_add_drop w a r
  unfold chordRankInt
  rw [hDepth]
  push_cast
  ring

/-- whole rank 上の一つの record excursion。 -/
structure RankRecordBlock
    (w : Word)
    (startIndex : ℕ) : Type where
  length : ℕ
  length_pos : 0 < length
  next_le_terminal : startIndex + length ≤ oddSteps w
  block_length :
    oddSteps (recordBlockWord w startIndex length) = length
  minimal :
    MinimalCrossingBlock (recordBlockWord w startIndex length)
  start_roof :
    prefixTwoDepth w startIndex = criticalHeight startIndex
  before_record :
    ∀ j : ℕ,
      0 < j →
      j < length →
      chordRankInt w startIndex <
        chordRankInt w (startIndex + j)
  rank_strict :
    chordRankInt w (startIndex + length) <
      chordRankInt w startIndex
  next_roof_if_interior :
    startIndex + length < oddSteps w →
      prefixTwoDepth w (startIndex + length) =
        criticalHeight (startIndex + length)

namespace RankRecordBlock

/--
local minimal FirstCrossing block が global critical chord の下で一つの record excursion を作る
ための pure constructor。
-/
def ofMinimalAtRoof
    {w : Word}
    {a r : ℕ}
    (hrPos : 0 < r)
    (hNextLe : a + r ≤ oddSteps w)
    (hBlockLen : oddSteps (recordBlockWord w a r) = r)
    (M : MinimalCrossingBlock (recordBlockWord w a r))
    (hStartRoof : prefixTwoDepth w a = criticalHeight a)
    (hCriticalBelow :
      ∀ j : ℕ, 0 < j → j < r →
        oddSteps w * criticalHeight j < twoSteps w * j)
    (hDrop :
      twoSteps w * r < oddSteps w * (criticalHeight r + 1))
    (hNextRoof :
      a + r < oddSteps w →
        prefixTwoDepth w (a + r) = criticalHeight (a + r)) :
    RankRecordBlock w a := by
  refine {
    length := r
    length_pos := hrPos
    next_le_terminal := hNextLe
    block_length := hBlockLen
    minimal := M
    start_roof := hStartRoof
    before_record := ?_
    rank_strict := ?_
    next_roof_if_interior := hNextRoof
  }
  · intro j hjPos hjLt
    have hjLe : j ≤ r := Nat.le_of_lt hjLt
    have hjLtBlock : j < oddSteps (recordBlockWord w a r) := by
      rw [hBlockLen]
      exact hjLt
    have hLocalLe :
        prefixTwoDepth (recordBlockWord w a r) j ≤ criticalHeight j :=
      M.firstCrossing.prefixTwoDepth_le_criticalHeight hjPos hjLtBlock
    have hSlice := prefixTwoDepth_recordBlockWord w a r j hjLe
    rw [hSlice] at hLocalLe
    have hCrit := hCriticalBelow j hjPos hjLt
    have hShift := chordRankInt_add_sub w a j
    have hCritZ :
        (oddSteps w : ℤ) * (criticalHeight j : ℤ) <
          (twoSteps w : ℤ) * (j : ℤ) := by
      exact_mod_cast hCrit
    have hLocalZ :
        (prefixTwoDepth (w.drop a) j : ℤ) ≤ (criticalHeight j : ℤ) := by
      exact_mod_cast hLocalLe
    have hDiffPos :
        0 < (twoSteps w : ℤ) * (j : ℤ) -
          (oddSteps w : ℤ) * (prefixTwoDepth (w.drop a) j : ℤ) := by
      have hpNonneg : 0 ≤ (oddSteps w : ℤ) := by positivity
      nlinarith
    linarith
  · have hShift := chordRankInt_add_sub w a r
    have hLocalDepth :
        prefixTwoDepth (w.drop a) r =
          twoSteps (recordBlockWord w a r) := by
      rfl
    have hMin := M.minimalDepth
    rw [hBlockLen] at hMin
    rw [hLocalDepth, hMin] at hShift
    have hDropZ :
        (twoSteps w : ℤ) * (r : ℤ) <
          (oddSteps w : ℤ) * ((criticalHeight r + 1 : ℕ) : ℤ) := by
      exact_mod_cast hDrop
    have hDiffNeg :
        chordRankInt w (a + r) - chordRankInt w a < 0 := by
      rw [hShift]
      exact sub_neg.mpr hDropZ
    exact sub_neg.mp hDiffNeg

/-- 次の record index。 -/
def nextIndex
    {w : Word} {a : ℕ}
    (R : RankRecordBlock w a) : ℕ :=
  a + R.length

/-- record block の word。 -/
def word
    {w : Word} {a : ℕ}
    (R : RankRecordBlock w a) : Word :=
  recordBlockWord w a R.length

/-- record endpoint の cumulative depth は start depth + local block depth。 -/
theorem prefixTwoDepth_next_eq
    {w : Word} {a : ℕ}
    (R : RankRecordBlock w a) :
    prefixTwoDepth w (a + R.length) =
      prefixTwoDepth w a + twoSteps R.word := by
  have h := prefixTwoDepth_add_drop w a R.length
  simpa [word, recordBlockWord, prefixTwoDepth] using h

/-- interior record endpoint が roof に戻ることは critical carry `1` と同値な側を与える。 -/
theorem interior_criticalCarry_eq_one
    {w : Word} {a : ℕ}
    (R : RankRecordBlock w a)
    (hInterior : a + R.length < oddSteps w) :
    criticalCarry a R.length = 1 := by
  have hDepth := R.prefixTwoDepth_next_eq
  have hNextRoof := R.next_roof_if_interior hInterior
  have hMin := R.minimal.minimalDepth
  have hCarry := criticalHeight_add_eq a R.length
  rw [R.block_length] at hMin
  change
    prefixTwoDepth w (a + R.length) =
      prefixTwoDepth w a +
        twoSteps (recordBlockWord w a R.length)
    at hDepth
  rw [R.start_roof, hMin, hNextRoof] at hDepth
  omega

/--
terminal record block と whole FirstCrossing から、最後の carry は自動的に `0` となり、
whole depth 自身も minimal contracting depth に強制される。
-/
theorem terminal_carry_zero_and_whole_minimal_of_firstCrossing
    {w : Word} {a : ℕ}
    (R : RankRecordBlock w a)
    (hTerminal : a + R.length = oddSteps w)
    (hWhole : FirstCrossing w) :
    criticalCarry a R.length = 0 ∧
      twoSteps w = criticalHeight (oddSteps w) + 1 := by
  have hDepth := R.prefixTwoDepth_next_eq
  have hTerminalDepth :
      prefixTwoDepth w (oddSteps w) = twoSteps w := by
    unfold prefixTwoDepth oddSteps
    simp
  have hMin := R.minimal.minimalDepth
  have hCarry := criticalHeight_add_eq a R.length
  have hCarryLe := criticalCarry_le_one a R.length
  have hpPos : 0 < oddSteps w := by
    unfold oddSteps
    exact List.length_pos_iff.mpr hWhole.nonempty
  have hPow :=
    (contracting_iff_threePow_lt_twoPow).1
      hWhole.terminalContracting
  have hCritLt :
      criticalHeight (oddSteps w) < twoSteps w :=
    criticalHeight_lt_of_threePow_lt_twoPow hpPos hPow
  rw [R.block_length] at hMin
  change
    prefixTwoDepth w (a + R.length) =
      prefixTwoDepth w a +
        twoSteps (recordBlockWord w a R.length)
    at hDepth
  rw [hTerminal, hTerminalDepth, R.start_roof, hMin] at hDepth
  rw [hTerminal] at hCarry
  constructor <;> omega

/-- terminal whole も minimal depth なら最後の carry は `0`。 -/
theorem terminal_criticalCarry_eq_zero_of_whole_minimal
    {w : Word} {a : ℕ}
    (R : RankRecordBlock w a)
    (hTerminal : a + R.length = oddSteps w)
    (hWholeMinimal :
      twoSteps w = criticalHeight (oddSteps w) + 1) :
    criticalCarry a R.length = 0 := by
  have hDepth := R.prefixTwoDepth_next_eq
  have hTerminalDepth :
      prefixTwoDepth w (oddSteps w) = twoSteps w := by
    unfold prefixTwoDepth oddSteps
    simp
  have hMin := R.minimal.minimalDepth
  have hCarry := criticalHeight_add_eq a R.length
  rw [R.block_length] at hMin
  change
    prefixTwoDepth w (a + R.length) =
      prefixTwoDepth w a +
        twoSteps (recordBlockWord w a R.length)
    at hDepth
  rw [
    hTerminal,
    hTerminalDepth,
    hWholeMinimal,
    R.start_roof,
    hMin
  ] at hDepth
  rw [hTerminal] at hCarry
  omega

end RankRecordBlock

/-- record block を terminal まで連結した generic chain。 -/
inductive RankRecordDecomposition
    (w : Word) : (startIndex : ℕ) → Type
  | terminal
      {a : ℕ}
      (block : RankRecordBlock w a)
      (terminal_eq : a + block.length = oddSteps w) :
      RankRecordDecomposition w a
  | step
      {a : ℕ}
      (block : RankRecordBlock w a)
      (interior : a + block.length < oddSteps w)
      (tail : RankRecordDecomposition w (a + block.length)) :
      RankRecordDecomposition w a

namespace RankRecordDecomposition

/-- record skeleton: block lengths の列。 -/
def lengths
    {w : Word} {a : ℕ} :
    RankRecordDecomposition w a → List ℕ
  | .terminal block _ => [block.length]
  | .step block _ tail => block.length :: tail.lengths

/-- local block words。 -/
def blocks
    {w : Word} {a : ℕ} :
    RankRecordDecomposition w a → List Word
  | .terminal block _ => [recordBlockWord w a block.length]
  | .step block _ tail => recordBlockWord w a block.length :: tail.blocks

/-- skeleton は nonempty。 -/
theorem lengths_nonempty
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a) :
    D.lengths ≠ [] := by
  cases D <;> simp [lengths]

/-- 全 record length は正。 -/
theorem lengths_pos
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a) :
    ∀ r ∈ D.lengths, 0 < r := by
  induction D with
  | terminal block hterm =>
      intro r hr
      simp only [lengths, List.mem_singleton] at hr
      subst r
      exact block.length_pos
  | step block hinterior tail ih =>
      intro r hr
      simp only [lengths, List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact block.length_pos
      · exact ih r hr

/-- skeleton は start から terminal まで exact に分割する。 -/
theorem start_add_lengths_sum_eq_terminal
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a) :
    a + D.lengths.sum = oddSteps w := by
  induction D with
  | terminal block hterm =>
      simpa [lengths] using hterm
  | step block hinterior tail ih =>
      simpa [lengths, Nat.add_assoc] using ih

/-- decomposition blocks を flatten すると start 以後の suffix を exact に戻す。 -/
theorem blocks_flatten_eq_drop
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a) :
    D.blocks.flatten = w.drop a := by
  induction D with
  | terminal block hterm =>
      simp only [blocks, List.flatten_cons, List.flatten_nil, List.append_nil]
      unfold recordBlockWord
      apply List.take_of_length_le
      simp [oddSteps] at hterm ⊢
      omega
  | step block hinterior tail ih =>
      simp only [blocks, List.flatten_cons]
      rw [ih]
      unfold recordBlockWord
      rename_i a0
      have hDrop :
          (w.drop a0).drop block.length =
            w.drop (a0 + block.length) := by
        exact List.drop_drop
      rw [← hDrop]
      exact List.take_append_drop block.length (w.drop a0)

/-- block words の odd-step 数列は record skeleton そのもの。 -/
theorem blocks_oddSteps_eq_lengths
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a) :
    D.blocks.map oddSteps = D.lengths := by
  induction D with
  | terminal block hterm =>
      simp [blocks, lengths, block.block_length]
  | step block hinterior tail ih =>
      simp [blocks, lengths, block.block_length, ih]

/-- decomposition 内の全 local word は minimal crossing block。 -/
theorem blocks_minimal
    {w : Word} {a : ℕ}
    (D : RankRecordDecomposition w a) :
    ∀ b ∈ D.blocks, MinimalCrossingBlock b := by
  induction D with
  | terminal block hterm =>
      intro b hb
      simp only [blocks, List.mem_singleton] at hb
      subst b
      exact block.minimal
  | step block hinterior tail ih =>
      intro b hb
      simp only [blocks, List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact block.minimal
      · exact ih b hb

end RankRecordDecomposition

end Word
end Collatz2
