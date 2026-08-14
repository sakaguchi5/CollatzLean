import CollatzLean.Collatz2.Canonical.RotationCrossingTrap
import CollatzLean.Collatz2.Canonical.EndpointFloorRankSeparation
import CollatzLean.Collatz2.Geometry.RankStrip

/-!
# Collatz2 Canonical: rotation crossing trap の rank-record 形式

Stage 7。

これは conditional packet `MinimalAdjacentCanonicalReturn` / `RotationCrossingTrap` に対する
rank bridge であり、current A の endpoint FutureMinimum を無条件に主張しない。

`w = 1 :: v` と rotation `rho = v ++ [1]` に対し、rotation prefix rank は exact に

  d_rho(j) = d_w(j+1) - d_w(1)

となる。

従って rotation の first crossing より前では original rank は `d_1` より上にある。
crossing 時点では lossless に

* original rank が `d_1` 以下へ落ちる
* まだ rational chord の下側に残るため critical/rational strip が非自明

の二択になる。

後者は rank 単位で

  p < stripRank(r)

という明示 witness を持つ。
-/

namespace Collatz2
namespace Word

/-- singleton append は、その手前までの prefix を変えない。 -/
private theorem take_append_singleton_of_le_length_rank
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

/-- rotateOne prefix の two-depth は元 tail の同じ prefix depth。 -/
theorem prefixTwoDepth_rotateOne
    {e : ℕ}
    {v : Word}
    {k : ℕ}
    (hk : k ≤ v.length) :
    prefixTwoDepth (rotateOne (e :: v)) k =
      twoSteps (v.take k) := by
  unfold prefixTwoDepth
  rw [rotateOne_cons]
  rw [take_append_singleton_of_le_length_rank v e hk]

/-- 元 word の `k+1` prefix depth は head exponent と rotated prefix depth の和。 -/
theorem prefixTwoDepth_cons_succ_eq_head_add_rotate
    {e : ℕ}
    {v : Word}
    {k : ℕ}
    (hk : k ≤ v.length) :
    prefixTwoDepth (e :: v) (k + 1) =
      e + prefixTwoDepth (rotateOne (e :: v)) k := by
  rw [prefixTwoDepth_rotateOne hk]
  simp [prefixTwoDepth, twoSteps]

/-- 一文字 rotation の chord rank shift。 -/
theorem chordRankInt_rotateOne_eq_sub
    {e : ℕ}
    {v : Word}
    {k : ℕ}
    (hk : k ≤ v.length) :
    chordRankInt (rotateOne (e :: v)) k =
      chordRankInt (e :: v) (k + 1) -
        chordRankInt (e :: v) 1 := by
  have hOdd :
      oddSteps (rotateOne (e :: v)) = oddSteps (e :: v) := by
    rw [rotateOne_eq_cyclicRotate_one]
    exact oddSteps_cyclicRotate (e :: v) 1
  have hTwo :
      twoSteps (rotateOne (e :: v)) = twoSteps (e :: v) := by
    rw [rotateOne_eq_cyclicRotate_one]
    exact twoSteps_cyclicRotate (e :: v) 1
  have hDepthSucc :
      prefixTwoDepth (e :: v) (k + 1) =
        e + prefixTwoDepth (rotateOne (e :: v)) k :=
    prefixTwoDepth_cons_succ_eq_head_add_rotate
      (e := e) (v := v) (k := k) hk
  have hDepthOne :
      prefixTwoDepth (e :: v) 1 = e := by
    simp [prefixTwoDepth, twoSteps]
  unfold chordRankInt
  rw [hOdd, hTwo, hDepthSucc, hDepthOne]
  push_cast
  ring

end Word

namespace OddOrbit
namespace EndpointFloorReduction
namespace MinimalAdjacentCanonicalReturn

/-- conditional rotation は base word の genuine one-step cyclic rotation。 -/
theorem rotationWord_eq_rotateOne_base
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    M.rotationWord = Word.rotateOne M.base.word := by
  have hw : M.base.word = 1 :: M.tail := by
    simpa [tail] using M.zeroCore.natural.word_eq
  rw [hw]
  simp [rotationWord, Word.rotateOne]

/-- rotation rank と original rank の exact shift。 -/
theorem rotationRank_shift
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O)
    {k : ℕ}
    (hk : k ≤ M.tail.length) :
    Word.chordRankInt M.rotationWord k =
      Word.chordRankInt M.base.word (k + 1) -
        Word.chordRankInt M.base.word 1 := by
  have hw : M.base.word = 1 :: M.tail := by
    simpa [tail] using M.zeroCore.natural.word_eq
  calc
    Word.chordRankInt M.rotationWord k
        = Word.chordRankInt (Word.rotateOne M.base.word) k := by
            rw [M.rotationWord_eq_rotateOne_base]
    _ = Word.chordRankInt M.base.word (k + 1) -
          Word.chordRankInt M.base.word 1 := by
            rw [hw]
            exact Word.chordRankInt_rotateOne_eq_sub hk

/-- rotation word length。 -/
@[simp] theorem rotationWord_length
    {O : OddOrbit}
    (M : MinimalAdjacentCanonicalReturn O) :
    M.rotationWord.length = M.tail.length + 1 := by
  simp [rotationWord]

namespace RotationCrossingTrap

/--
rotation first crossing より前では original rank は first rank `d_1` より strict に上。
-/
theorem originalRank_above_first_before_crossing
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M)
    {j : ℕ}
    (hjPos : 0 < j)
    (hjLt : j < R.crossingLength) :
    Word.chordRankInt M.base.word 1 <
      Word.chordRankInt M.base.word (j + 1) := by
  have hrLeRot : R.crossingLength ≤ M.rotationWord.length := by
    rw [M.rotationWord_length]
    exact Nat.le_trans R.crossingLength_le_tail (Nat.le_succ _)
  have hCrossLen :
      (M.rotationWord.take R.crossingLength).length = R.crossingLength :=
    List.length_take_of_le hrLeRot
  have hjLtTake :
      j < (M.rotationWord.take R.crossingLength).length := by
    rw [hCrossLen]
    exact hjLt
  have hExpRaw :=
    R.rotationFirstCrossing.properExpanding hjPos hjLtTake
  have hTakeTake :
      (M.rotationWord.take R.crossingLength).take j =
        M.rotationWord.take j := by
    simp [List.take_take, Nat.min_eq_left (Nat.le_of_lt hjLt)]
  rw [hTakeTake] at hExpRaw
  have hExp : Word.Expanding (M.rotationWord.take j) := hExpRaw
  have hjLtRot : j < M.rotationWord.length := by omega
  have hRankRot :
      0 < Word.chordRankInt M.rotationWord j :=
    Word.chordRankInt_pos_of_expanding_contracting
      hjPos hjLtRot hExp M.rotationContracting
  have hShift :=
    M.rotationRank_shift
      (k := j)
      (Nat.le_trans (Nat.le_of_lt hjLt) R.crossingLength_le_tail)
  linarith

/--
rotation crossing 時点の lossless rank dichotomy。

* rank が `d_1` 以下へ落ちる
* crossing prefix は critical line を越えたが full rational chord の下に残り、
  `p < stripRank` を強制する
-/
theorem crossingRank_le_first_or_strip
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M) :
    Word.chordRankInt M.base.word (R.crossingLength + 1) ≤
        Word.chordRankInt M.base.word 1 ∨
      Word.oddSteps M.base.word <
        Word.stripRank M.base.word R.crossingLength := by
  let r := R.crossingLength
  have hrPos : 0 < r := by
    simpa [r] using R.crossingLength_pos
  have hrLeTail : r ≤ M.tail.length := by
    simpa [r] using R.crossingLength_le_tail
  have hrLeRot : r ≤ M.rotationWord.length := by
    rw [M.rotationWord_length]
    omega
  have hCrossC : Word.Contracting (M.rotationWord.take r) := by
    have h := R.rotationFirstCrossing.terminalContracting
    simpa [r] using h
  have hShift := M.rotationRank_shift (k := r) hrLeTail
  by_cases hNonpos : Word.chordRankInt M.rotationWord r ≤ 0
  · left
    dsimp [r] at hShift hNonpos ⊢
    linarith
  · right
    have hRankPos : 0 < Word.chordRankInt M.rotationWord r := by
      omega
    have hpRot : 0 < Word.oddSteps M.rotationWord := by
      simp only [Word.oddSteps, rotationWord_length, lt_add_iff_pos_left,
        Order.lt_add_one_iff, zero_le]
    have hStripRot :=
      Word.stripRank_gt_oddSteps_of_contracting_take_of_rankInt_pos
        hpRot hrPos hrLeRot hCrossC hRankPos
    have hOdd := M.rotation_oddSteps_eq
    have hTwo := M.rotation_twoSteps_eq
    simpa [Word.stripRank, hOdd, hTwo, r] using hStripRot

/--
既存の terminal/interior orbit branch と rank/strip branch を同じ packet に保持する。
-/
structure RankRecordTrapData
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M) : Prop where
  before_record :
    ∀ j : ℕ,
      0 < j →
      j < R.crossingLength →
      Word.chordRankInt M.base.word 1 <
        Word.chordRankInt M.base.word (j + 1)
  terminal_or_interior :
    R.crossingLength = M.tail.length ∨
      R.crossingLength < M.tail.length
  crossing_rank_or_strip :
    Word.chordRankInt M.base.word (R.crossingLength + 1) ≤
        Word.chordRankInt M.base.word 1 ∨
      Word.oddSteps M.base.word <
        Word.stripRank M.base.word R.crossingLength

/-- RotationCrossingTrap を rank-record packet へ lossless に翻訳する。 -/
theorem toRankRecordTrapData
    {O : OddOrbit}
    {M : MinimalAdjacentCanonicalReturn O}
    (R : RotationCrossingTrap M) :
    RankRecordTrapData R := {
  before_record := fun _j hjPos hjLt =>
    R.originalRank_above_first_before_crossing hjPos hjLt
  terminal_or_interior := R.terminal_or_interior
  crossing_rank_or_strip := R.crossingRank_le_first_or_strip
}

end RotationCrossingTrap
end MinimalAdjacentCanonicalReturn
end EndpointFloorReduction
end OddOrbit
end Collatz2
