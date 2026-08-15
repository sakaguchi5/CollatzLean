import CollatzLean.Collatz2.Canonical.RotationRankTrap
import CollatzLean.Collatz2.Global.EndpointFloorNaturalCoordinates

/-!
# Collatz2 Canonical: current A の unconditional tail-rank trap

Stage 7b。

`RotationRankTrap` は endpoint FutureMinimum を持つ conditional packet 上の bridge だった。
ここでは current A `CanonicalEndpointFloorContractingReturn` だけから同じ rank mechanism を
取り直す。

current A は無条件に

  w = 1 :: tail

を持ち、FirstCrossing から `tail` は contracting。
したがって `tail` の最初の FirstCrossing prefix を `r` として選べる。

virtual one-step rotation

  rho = tail ++ [1]

は actual orbit return である必要はない。diagonal coefficients を whole word と共有するため、
rank shift

  d_rho(j) = d_w(j+1) - d_w(1)

だけで十分である。

その結果 current A 自身から lossless に

* crossing 前: `d_1 < d_(j+1)`
* crossing: `d_(r+1) <= d_1` または `p < stripRank(w,r)`

を得る。
FutureMinimum endpoint は使わない。
-/

namespace Collatz2
namespace OddOrbit
namespace CanonicalEndpointFloorContractingReturn

/-- singleton append は tail length まで prefix を変えない。 -/
private theorem take_append_singleton_of_le_length_tailRank
    {α : Type*}
    (w : List α)
    (a : α)
    {k : ℕ}
    (hk : k ≤ w.length) :
    (w ++ [a]).take k = w.take k := by
  induction w generalizing k with
  | nil =>
      have hk0 : k = 0 := by
        simp at hk
        omega
      subst k
      simp
  | cons x w ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hk' : k ≤ w.length := by
            simp at hk
            omega
          simp [ih hk']

/-- current A だけから得る tail rank trap packet。 -/
structure TailRankTrapData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) where
  tail : Word
  word_eq : D.word = 1 :: tail
  tail_nonempty : tail ≠ []
  tail_valid : Word.Valid tail
  tail_contracting : Word.Contracting tail

  crossingLength : ℕ
  crossingLength_pos : 0 < crossingLength
  crossingLength_le_tail : crossingLength ≤ tail.length
  firstCrossing : Word.FirstCrossing (tail.take crossingLength)

  before_record :
    ∀ j : ℕ,
      0 < j →
      j < crossingLength →
      Word.chordRankInt D.word 1 <
        Word.chordRankInt D.word (j + 1)

  crossing_rank_or_strip :
    Word.chordRankInt D.word (crossingLength + 1) ≤
        Word.chordRankInt D.word 1 ∨
      Word.oddSteps D.word <
        Word.stripRank D.word crossingLength

  crossing_lt_whole : crossingLength < Word.oddSteps D.word

namespace TailRankTrapData

/-- virtual rotation `tail ++ [1]`。 -/
def virtualRotation
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D) : Word :=
  R.tail ++ [1]

/-- virtual rotation は base word の one-step cyclic rotation。 -/
theorem virtualRotation_eq_rotateOne
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D) :
    R.virtualRotation = Word.rotateOne D.word := by
  rw [R.word_eq]
  rfl

/-- virtual rotation は whole と同じ odd-step 数。 -/
theorem virtualRotation_oddSteps_eq
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D) :
    Word.oddSteps R.virtualRotation = Word.oddSteps D.word := by
  rw [R.virtualRotation_eq_rotateOne]
  rw [R.word_eq]
  rw [Word.rotateOne_eq_cyclicRotate_one]
  exact Word.oddSteps_cyclicRotate (1 :: R.tail) 1

/-- virtual rotation は whole と同じ total two-depth。 -/
theorem virtualRotation_twoSteps_eq
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D) :
    Word.twoSteps R.virtualRotation = Word.twoSteps D.word := by
  rw [R.virtualRotation_eq_rotateOne]
  rw [R.word_eq]
  rw [Word.rotateOne_eq_cyclicRotate_one]
  exact Word.twoSteps_cyclicRotate (1 :: R.tail) 1

/-- virtual rotation も contracting。 -/
theorem virtualRotation_contracting
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D) :
    Word.Contracting R.virtualRotation := by
  apply (Word.contracting_iff_threePow_lt_twoPow).2
  have h :=
    (Word.contracting_iff_threePow_lt_twoPow).1 D.contracting
  rw [R.virtualRotation_oddSteps_eq, R.virtualRotation_twoSteps_eq]
  exact h

/-- tail の crossing prefix は virtual rotation の同じ prefix。 -/
theorem virtualRotation_take_crossing
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D) :
    R.virtualRotation.take R.crossingLength =
      R.tail.take R.crossingLength := by
  unfold virtualRotation
  exact
    take_append_singleton_of_le_length_tailRank
      R.tail 1 R.crossingLength_le_tail

/-- crossing は terminal または strict interior。 -/
theorem terminal_or_interior
    {O : OddOrbit}
    {D : CanonicalEndpointFloorContractingReturn O}
    (R : TailRankTrapData D) :
    R.crossingLength = R.tail.length ∨
      R.crossingLength < R.tail.length := by
  exact eq_or_lt_of_le R.crossingLength_le_tail

end TailRankTrapData

/--
7b: current A から unconditional tail-rank trap を構成する。
-/
noncomputable def toTailRankTrapData
    {O : OddOrbit}
    (D : CanonicalEndpointFloorContractingReturn O) :
    TailRankTrapData D := by
  classical
  let N := D.toNaturalCoordinates
  have hTailValid : Word.Valid N.tail := by
    intro e he
    apply D.word_valid e
    rw [N.word_eq]
    simp [he]
  have hLen : 1 < D.word.length := D.word_length_gt_one
  have hTailContracting : Word.Contracting N.tail := by
    have hneg := D.allSuffixesContracting 1 hLen
    have hdrop : Word.Contracting (D.word.drop 1) :=
      (Word.suffixDeterminant_neg_iff_contracting).1 hneg
    rw [N.word_eq] at hdrop
    simpa using hdrop
  have hExists :=
    Word.exists_firstCrossing_of_contracting
      hTailValid N.tail_nonempty hTailContracting
  let r : ℕ := Classical.choose hExists
  have hSpec := Classical.choose_spec hExists
  have hrLe : r ≤ N.tail.length := hSpec.1
  have hFirst : Word.FirstCrossing (N.tail.take r) := hSpec.2
  have hrPos : 0 < r := by
    have hTakeLen : (N.tail.take r).length = r :=
      List.length_take_of_le hrLe
    have hPos : 0 < (N.tail.take r).length :=
      List.length_pos_iff.mpr hFirst.nonempty
    rw [hTakeLen] at hPos
    exact hPos
  let rho : Word := N.tail ++ [1]
  have hRhoEqRotate : rho = Word.rotateOne D.word := by
    dsimp [rho]
    rw [N.word_eq]
    rfl
  have hRhoOdd : Word.oddSteps rho = Word.oddSteps D.word := by
    rw [hRhoEqRotate, N.word_eq, Word.rotateOne_eq_cyclicRotate_one]
    exact Word.oddSteps_cyclicRotate (1 :: N.tail) 1
  have hRhoTwo : Word.twoSteps rho = Word.twoSteps D.word := by
    rw [hRhoEqRotate, N.word_eq, Word.rotateOne_eq_cyclicRotate_one]
    exact Word.twoSteps_cyclicRotate (1 :: N.tail) 1
  have hRhoC : Word.Contracting rho := by
    apply (Word.contracting_iff_threePow_lt_twoPow).2
    have h :=
      (Word.contracting_iff_threePow_lt_twoPow).1 D.contracting
    rw [hRhoOdd, hRhoTwo]
    exact h
  have hBefore :
      ∀ j : ℕ,
        0 < j →
        j < r →
        Word.chordRankInt D.word 1 <
          Word.chordRankInt D.word (j + 1) := by
    intro j hjPos hjLt
    have hjLeTail : j ≤ N.tail.length := by
      exact Nat.le_trans (Nat.le_of_lt hjLt) hrLe
    have hTakeLen : (N.tail.take r).length = r :=
      List.length_take_of_le hrLe
    have hjLtTake : j < (N.tail.take r).length := by
      rw [hTakeLen]
      exact hjLt
    have hExpRaw := hFirst.properExpanding hjPos hjLtTake
    have hTakeTake :
        (N.tail.take r).take j = N.tail.take j := by
      simp [List.take_take, Nat.min_eq_left (Nat.le_of_lt hjLt)]
    rw [hTakeTake] at hExpRaw
    have hRhoTake : rho.take j = N.tail.take j := by
      dsimp [rho]
      exact
        take_append_singleton_of_le_length_tailRank
          N.tail 1 hjLeTail
    have hExp : Word.Expanding (rho.take j) := by
      rw [hRhoTake]
      exact hExpRaw
    have hjLtRho : j < rho.length := by
      dsimp [rho]
      simp
      omega
    have hRankRho : 0 < Word.chordRankInt rho j :=
      Word.chordRankInt_pos_of_expanding_contracting
        hjPos hjLtRho hExp hRhoC
    have hShift :
        Word.chordRankInt rho j =
          Word.chordRankInt D.word (j + 1) -
            Word.chordRankInt D.word 1 := by
      rw [hRhoEqRotate, N.word_eq]
      exact Word.chordRankInt_rotateOne_eq_sub hjLeTail
    linarith
  have hCrossDichotomy :
      Word.chordRankInt D.word (r + 1) ≤
          Word.chordRankInt D.word 1 ∨
        Word.oddSteps D.word < Word.stripRank D.word r := by
    have hrLeRho : r ≤ rho.length := by
      dsimp [rho]
      simp
      omega
    have hRhoTake : rho.take r = N.tail.take r := by
      dsimp [rho]
      exact
        take_append_singleton_of_le_length_tailRank
          N.tail 1 hrLe
    have hCrossC : Word.Contracting (rho.take r) := by
      rw [hRhoTake]
      exact hFirst.terminalContracting
    have hShift :
        Word.chordRankInt rho r =
          Word.chordRankInt D.word (r + 1) -
            Word.chordRankInt D.word 1 := by
      rw [hRhoEqRotate, N.word_eq]
      exact Word.chordRankInt_rotateOne_eq_sub hrLe
    by_cases hNonpos : Word.chordRankInt rho r ≤ 0
    · left
      linarith
    · right
      have hRankPos : 0 < Word.chordRankInt rho r := by omega
      have hpRho : 0 < Word.oddSteps rho := by
        rw [hRhoOdd]
        unfold Word.oddSteps
        exact List.length_pos_iff.mpr D.word_nonempty
      have hStripRho :=
        Word.stripRank_gt_oddSteps_of_contracting_take_of_rankInt_pos
          hpRho hrPos hrLeRho hCrossC hRankPos
      simpa [Word.stripRank, hRhoOdd, hRhoTwo] using hStripRho
  have hrLtWhole : r < Word.oddSteps D.word := by
    have hTailLen : N.tail.length + 1 = D.word.length :=
      N.tail_length_add_one
    unfold Word.oddSteps
    omega
  exact {
    tail := N.tail
    word_eq := N.word_eq
    tail_nonempty := N.tail_nonempty
    tail_valid := hTailValid
    tail_contracting := hTailContracting
    crossingLength := r
    crossingLength_pos := hrPos
    crossingLength_le_tail := hrLe
    firstCrossing := hFirst
    before_record := hBefore
    crossing_rank_or_strip := hCrossDichotomy
    crossing_lt_whole := hrLtWhole
  }

end CanonicalEndpointFloorContractingReturn
end OddOrbit
end Collatz2
