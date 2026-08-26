import CollatzLean.Collatz2.RecordFerrers.Lattice.WeightedArea

/-!
# Record–Ferrers Phase A: record block

fixed-chord fiber 上の global chord rank に対して、record anchor から始まる
minimal FirstCrossing excursion を pure Record–Ferrers object として定義する。

既存 `Geometry.RecordDecomposition` には依存しない shadow implementation。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- cut `start` から長さ `len` の local exponent block。 -/
def blockWord
    {p H : ℕ}
    (x : FiberPoint p H)
    (start len : ℕ) : Word :=
  (x.word.drop start).take len

/-- valid fixed-chord word の任意 block も valid。 -/
theorem blockWord_valid
    {p H : ℕ}
    (x : FiberPoint p H)
    (start len : ℕ) :
    Valid (blockWord x start len) := by
  unfold blockWord
  exact FiberPoint.valid_take (FiberPoint.valid_drop x.valid start) len

/-- endpoint が terminal 以内なら block の odd-step 数は指定長と一致。 -/
theorem oddSteps_blockWord
    {p H : ℕ}
    (x : FiberPoint p H)
    {start len : ℕ}
    (hEnd : start + len ≤ p) :
    oddSteps (blockWord x start len) = len := by
  have hWordLen : x.word.length = p := by
    simpa [oddSteps] using x.oddSteps_eq
  have hLenDrop : (x.word.drop start).length = p - start := by
    rw [List.length_drop, hWordLen]
  have hLenLe : len ≤ (x.word.drop start).length := by
    rw [hLenDrop]
    omega
  unfold blockWord oddSteps
  exact List.length_take_of_le hLenLe

/-- local block prefix は original suffix prefix と同じ。 -/
theorem prefixTwoDepth_blockWord
    {p H : ℕ}
    (x : FiberPoint p H)
    (start len j : ℕ)
    (hj : j ≤ len) :
    prefixTwoDepth (blockWord x start len) j =
      prefixTwoDepth (x.word.drop start) j := by
  unfold blockWord prefixTwoDepth
  simp [List.take_take, Nat.min_eq_left hj]

/-- global height の add/drop formula を block depth で読む。 -/
theorem height_add_eq_add_blockDepth
    {p H : ℕ}
    (x : FiberPoint p H)
    (start len : ℕ) :
    x.height (start + len) =
      x.height start + twoSteps (blockWord x start len) := by
  have h := FiberPoint.prefixTwoDepth_add_drop x.word start len
  unfold FiberPoint.height
  unfold blockWord prefixTwoDepth at h ⊢
  exact h

/-- minimal terminal depthを持つ local FirstCrossing word。 -/
structure MinimalBlock (w : Word) : Prop where
  firstCrossing : FirstCrossing w
  minimalDepth :
    twoSteps w = criticalHeight (oddSteps w) + 1

/-- genuine positive exponent word である minimal block。 -/
structure ValidMinimalBlock (w : Word) : Prop extends MinimalBlock w where
  valid : Valid w

namespace MinimalBlock

/-- minimal block は nonempty。 -/
theorem nonempty
    {w : Word}
    (M : MinimalBlock w) :
    w ≠ [] :=
  M.firstCrossing.nonempty

/-- minimal block の odd-step 数は正。 -/
theorem oddSteps_pos
    {w : Word}
    (M : MinimalBlock w) :
    0 < oddSteps w := by
  unfold oddSteps
  exact List.length_pos_iff.mpr M.nonempty

end MinimalBlock

/--
whole fixed-chord rank 上の一つの record excursion。

* start は critical roof 上
* interior rank は start rank より上
* endpoint で start rank を strict に下回る
* local word は minimal FirstCrossing
* interior endpoint なら再び critical roof 上へ戻る
-/
structure RecordBlock
    {p H : ℕ}
    (x : FiberPoint p H)
    (start len : ℕ) : Prop where
  length_pos : 0 < len
  end_le_terminal : start + len ≤ p
  minimal : MinimalBlock (blockWord x start len)
  start_roof : x.height start = criticalHeight start
  interior_above :
    ∀ j : ℕ,
      0 < j →
      j < len →
      chordRankInt x.word start < chordRankInt x.word (start + j)
  terminal_below :
    chordRankInt x.word (start + len) < chordRankInt x.word start
  next_roof_if_interior :
    start + len < p →
      x.height (start + len) = criticalHeight (start + len)

namespace RecordBlock

/-- cut shift による signed rank difference の fixed-fiber exact formula。 -/
theorem chordRankInt_add_sub
    {p H : ℕ}
    (x : FiberPoint p H)
    (a r : ℕ) :
    chordRankInt x.word (a + r) - chordRankInt x.word a =
      (H : ℤ) * (r : ℤ) -
        (p : ℤ) * (prefixTwoDepth (x.word.drop a) r : ℤ) := by
  have hDepth := FiberPoint.prefixTwoDepth_add_drop x.word a r
  have hDepthZ :
      (prefixTwoDepth x.word (a + r) : ℤ) =
        (prefixTwoDepth x.word a : ℤ) +
          (prefixTwoDepth (x.word.drop a) r : ℤ) := by
    exact_mod_cast hDepth
  unfold chordRankInt
  rw [x.twoSteps_eq, x.oddSteps_eq, hDepthZ]
  push_cast
  ring

/--
local minimal block が global chord の下で record excursion を作るための pure constructor。
-/
theorem ofMinimalAtRoof
    {p H : ℕ}
    (x : FiberPoint p H)
    {start len : ℕ}
    (hLenPos : 0 < len)
    (hEnd : start + len ≤ p)
    (M : MinimalBlock (blockWord x start len))
    (hStartRoof : x.height start = criticalHeight start)
    (hCriticalBelow :
      ∀ j : ℕ, 0 < j → j < len →
        p * criticalHeight j < H * j)
    (hDrop :
      H * len < p * (criticalHeight len + 1))
    (hNextRoof :
      start + len < p →
        x.height (start + len) = criticalHeight (start + len)) :
    RecordBlock x start len := by
  refine {
    length_pos := hLenPos
    end_le_terminal := hEnd
    minimal := M
    start_roof := hStartRoof
    interior_above := ?_
    terminal_below := ?_
    next_roof_if_interior := hNextRoof
  }
  · intro j hjPos hjLt
    have hjLe : j ≤ len := Nat.le_of_lt hjLt
    have hLocalOdd : oddSteps (blockWord x start len) = len :=
      oddSteps_blockWord x hEnd
    have hjBlock : j < oddSteps (blockWord x start len) := by
      rw [hLocalOdd]
      exact hjLt
    have hLocalLe :
        prefixTwoDepth (blockWord x start len) j ≤ criticalHeight j :=
      M.firstCrossing.prefixTwoDepth_le_criticalHeight hjPos hjBlock
    have hSlice := prefixTwoDepth_blockWord x start len j hjLe
    rw [hSlice] at hLocalLe
    have hShift := chordRankInt_add_sub x start j
    have hCritZ :
        (p : ℤ) * (criticalHeight j : ℤ) <
          (H : ℤ) * (j : ℤ) := by
      exact_mod_cast hCriticalBelow j hjPos hjLt
    have hLocalZ :
        (prefixTwoDepth (x.word.drop start) j : ℤ) ≤
          (criticalHeight j : ℤ) := by
      exact_mod_cast hLocalLe
    have hpNonneg : 0 ≤ (p : ℤ) := by positivity
    have hDiffPos :
        0 < (H : ℤ) * (j : ℤ) -
          (p : ℤ) * (prefixTwoDepth (x.word.drop start) j : ℤ) := by
      nlinarith
    linarith
  · have hShift := chordRankInt_add_sub x start len
    have hLocalDepth :
        prefixTwoDepth (x.word.drop start) len =
          twoSteps (blockWord x start len) := by
      rfl
    have hMin := M.minimalDepth
    have hLocalOdd : oddSteps (blockWord x start len) = len :=
      oddSteps_blockWord x hEnd
    rw [hLocalOdd] at hMin
    rw [hLocalDepth, hMin] at hShift
    have hDropZ :
        (H : ℤ) * (len : ℤ) <
          (p : ℤ) * ((criticalHeight len + 1 : ℕ) : ℤ) := by
      exact_mod_cast hDrop
    have hDiffNeg :
        chordRankInt x.word (start + len) - chordRankInt x.word start < 0 := by
      rw [hShift]
      exact sub_neg.mpr hDropZ
    exact sub_neg.mp hDiffNeg

/-- record block の local word は valid。 -/
theorem local_valid
    {p H : ℕ}
    {x : FiberPoint p H}
    {start len : ℕ} :
    Valid (blockWord x start len) :=
  blockWord_valid x start len

/-- record block local word の odd-step 数は `len`。 -/
theorem local_oddSteps
    {p H : ℕ}
    {x : FiberPoint p H}
    {start len : ℕ}
    (B : RecordBlock x start len) :
    oddSteps (blockWord x start len) = len :=
  oddSteps_blockWord x B.end_le_terminal

/-- record block local depth は `criticalHeight len + 1`。 -/
theorem local_twoSteps
    {p H : ℕ}
    {x : FiberPoint p H}
    {start len : ℕ}
    (B : RecordBlock x start len) :
    twoSteps (blockWord x start len) = criticalHeight len + 1 := by
  have h := B.minimal.minimalDepth
  rw [B.local_oddSteps] at h
  exact h

/-- interior record endpoint の additive critical carry は必ず 1。 -/
theorem criticalCarry_eq_one_of_interior
    {p H : ℕ}
    {x : FiberPoint p H}
    {start len : ℕ}
    (B : RecordBlock x start len)
    (hInterior : start + len < p) :
    criticalCarry start len = 1 := by
  have hHeight := height_add_eq_add_blockDepth x start len
  have hDepth := B.local_twoSteps
  have hNext := B.next_roof_if_interior hInterior
  rw [B.start_roof, hDepth, hNext] at hHeight
  have hCrit := criticalHeight_add_eq start len
  omega

/-- terminal record block では whole FirstCrossing から additive carry 0 が従う。 -/
theorem criticalCarry_eq_zero_of_terminal
    {p H : ℕ}
    {x : FiberPoint p H}
    {start len : ℕ}
    (B : RecordBlock x start len)
    (hTerminal : start + len = p)
    (hWhole : FirstCrossing x.word) :
    criticalCarry start len = 0 := by
  have hHeight := height_add_eq_add_blockDepth x start len
  have hDepth := B.local_twoSteps
  have hTerminalHeight : x.height (start + len) = H := by
    rw [hTerminal]
    exact x.height_terminal
  rw [B.start_roof, hDepth, hTerminalHeight] at hHeight
  have hCrit := criticalHeight_add_eq start len
  have hCarryCases := criticalCarry_eq_zero_or_one start len
  rcases hCarryCases with hZero | hOne
  · exact hZero
  · exfalso
    have hHEq : H = criticalHeight p := by
      rw [hTerminal] at hCrit
      rw [hOne] at hCrit
      omega
    have hpPos : 0 < p := by
      have hLenPos : 0 < x.word.length :=
        List.length_pos_iff.mpr hWhole.nonempty
      have hLen : x.word.length = p := by
        simpa [oddSteps] using x.oddSteps_eq
      omega
    have hBelow := criticalHeight_pow_lt_threePow hpPos
    have hAbove :=
      (contracting_iff_threePow_lt_twoPow).1 hWhole.terminalContracting
    rw [x.oddSteps_eq, x.twoSteps_eq, hHEq] at hAbove
    omega

end RecordBlock

end RecordFerrers
end Collatz2
