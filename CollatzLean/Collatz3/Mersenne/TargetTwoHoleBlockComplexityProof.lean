import CollatzLean.Collatz3.Binary.BlockPeriod
import CollatzLean.Collatz3.Mersenne.BlockComplexity
import CollatzLean.Collatz3.Mersenne.GeometricSum
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: target-two の period-break 上界

`TargetTwoHoleGeometric` で得た base `2^n` の 3-block normal form を、
`Binary.BlockPeriod` の固定幅 block 語へ移す。

`r=1,2` では各 base-`2^n` digit は高々 4 bit の短い segment であり、
同一 digit が続く区間では period `n` の mismatch は 0。
不一致は高々二つの block 境界にしか現れず、その Hamming 距離の和は高々 5 になる。

wrapped branch はまず `2*3^k` の canonical word を作り、LSB の 0 を一つ外して
`3^k` へ戻す。`Binary.HasPeriodBreakAtMost.of_two_mul` により break 上界は保存される。

これで `BlockComplexity.lean` に残していた内部 target
`TargetTwoHolePeriodBreakAtMostFive` を無条件に閉じる。
-/

namespace Collatz3
namespace Mersenne

open Binary

/-- `2^r-1` の短い LSB-first segment。 -/
def targetTwoLowSegment (r : ℕ) : List Bool :=
  List.replicate r true

/-- `2^r` の短い LSB-first segment。 -/
def targetTwoPowerSegment (r : ℕ) : List Bool :=
  List.replicate r false ++ [true]

/-- `2^(r+1)-1` の短い LSB-first segment。 -/
def targetTwoReverseMiddleSegment (r : ℕ) : List Bool :=
  List.replicate (r + 1) true

/-- `2^(r+1)-2` の短い LSB-first segment。 -/
def targetTwoWrappedLowSegment (r : ℕ) : List Bool :=
  false :: List.replicate r true

/-- `2^(r+1)` の短い LSB-first segment。 -/
def targetTwoHighSegment (r : ℕ) : List Bool :=
  List.replicate (r + 1) false ++ [true]

private theorem value_lowSegment (r : ℕ) :
    valueLSB (targetTwoLowSegment r) = 2 ^ r - 1 := by
  have h := valueLSB_replicate_true_add_one r
  unfold targetTwoLowSegment
  omega

private theorem value_powerSegment (r : ℕ) :
    valueLSB (targetTwoPowerSegment r) = 2 ^ r := by
  simp [targetTwoPowerSegment, valueLSB_append]

private theorem value_reverseMiddleSegment (r : ℕ) :
    valueLSB (targetTwoReverseMiddleSegment r) = 2 ^ (r + 1) - 1 := by
  have h := valueLSB_replicate_true_add_one (r + 1)
  unfold targetTwoReverseMiddleSegment
  omega

private theorem value_wrappedLowSegment (r : ℕ) :
    valueLSB (targetTwoWrappedLowSegment r) = 2 ^ (r + 1) - 2 := by
  have h := valueLSB_replicate_true_add_one r
  unfold targetTwoWrappedLowSegment
  simp only [valueLSB_cons, bitValue_false, zero_add]
  rw [pow_succ]
  omega

private theorem value_highSegment (r : ℕ) :
    valueLSB (targetTwoHighSegment r) = 2 ^ (r + 1) := by
  simp [targetTwoHighSegment, valueLSB_append]

/-- 同一 fixed-width block の反復値は geometric sum になる。 -/
private theorem repeatBlock_value_geom
    {n : ℕ} {block : List Bool}
    (hLen : block.length = n) : ∀ count : ℕ,
    valueLSB (repeatBlock block count) =
      valueLSB block * targetGeomSum (2 ^ n) count
  | 0 => by simp [repeatBlock, targetGeomSum]
  | m + 1 => by
      rw [repeatBlock_succ, valueLSB_append, hLen,
        repeatBlock_value_geom hLen m, targetGeomSum_succ]
      ring

/-- 最後だけ短い canonical block にしても run 全体の geometric value は変わらない。 -/
private theorem canonicalRepeat_value_geom
    {n : ℕ} {block last : List Bool}
    (hLen : block.length = n)
    (hLastValue : valueLSB last = valueLSB block) : ∀ count : ℕ,
    valueLSB (canonicalRepeat block last count) =
      valueLSB block * targetGeomSum (2 ^ n) count
  | 0 => by simp [canonicalRepeat, canonicalBlockList, targetGeomSum]
  | m + 1 => by
      have hWord :
          canonicalRepeat block last (m + 1) =
            repeatBlock block m ++ last := by
        simp [canonicalRepeat, canonicalBlockList, concatBlocks_append,
          repeatBlock, concatBlocks]
      rw [hWord, valueLSB_append,
        repeatBlock_value_geom hLen m,
        repeatBlock_length, hLen, hLastValue]
      have hPow : 2 ^ (m * n) = (2 ^ n) ^ m := by
        rw [Nat.mul_comm, pow_mul]
      rw [hPow]
      rw [targetGeomSum_add (2 ^ n) m 1]
      simp [targetGeomSum]
      ring

/--
三つの constant digit run の canonical word の exact value。
zero-length middle/upper run も同じ式で扱える。
-/
private theorem threeRunCanonicalWord_value_geom
    {n : ℕ}
    {a aLast b bLast c cLast : List Bool}
    {qa qb qc : ℕ}
    (haLen : a.length = n)
    (hbLen : b.length = n)
    (hcLen : c.length = n)
    (haValue : valueLSB aLast = valueLSB a)
    (hbValue : valueLSB bLast = valueLSB b)
    (hcValue : valueLSB cLast = valueLSB c) :
    valueLSB (threeRunCanonicalWord a aLast b bLast c cLast qa qb qc) =
      valueLSB a * targetGeomSum (2 ^ n) qa +
      (2 ^ n) ^ qa * valueLSB b * targetGeomSum (2 ^ n) qb +
      (2 ^ n) ^ (qa + qb) * valueLSB c * targetGeomSum (2 ^ n) qc := by
  by_cases hqc : 0 < qc
  · unfold threeRunCanonicalWord threeRunCanonicalBlocks
    rw [ite_eq_left hqc, concatBlocks_append, concatBlocks_append]
    rw [List.append_assoc]
    change valueLSB
      (repeatBlock a qa ++
        (repeatBlock b qb ++ canonicalRepeat c cLast qc)) = _
    rw [valueLSB_append, repeatBlock_length, haLen,
      repeatBlock_value_geom haLen qa]
    have hPowA : 2 ^ (qa * n) = (2 ^ n) ^ qa := by
      rw [Nat.mul_comm, pow_mul]
    rw [hPowA, valueLSB_append, repeatBlock_length, hbLen,
      repeatBlock_value_geom hbLen qb,
      canonicalRepeat_value_geom hcLen hcValue qc]
    have hPowB : 2 ^ (qb * n) = (2 ^ n) ^ qb := by
      rw [Nat.mul_comm, pow_mul]
    rw [hPowB, pow_add]
    ring
  · have hqc0 : qc = 0 := Nat.eq_zero_of_not_pos hqc
    subst qc
    by_cases hqb : 0 < qb
    · unfold threeRunCanonicalWord threeRunCanonicalBlocks
      rw [ite_eq_right (by omega : ¬ 0 < 0), ite_eq_left hqb, concatBlocks_append]
      change valueLSB
        (repeatBlock a qa ++ canonicalRepeat b bLast qb) = _
      rw [valueLSB_append, repeatBlock_length, haLen,
        repeatBlock_value_geom haLen qa,
        canonicalRepeat_value_geom hbLen hbValue qb]
      have hPowA : 2 ^ (qa * n) = (2 ^ n) ^ qa := by
        rw [Nat.mul_comm, pow_mul]
      rw [hPowA]
      simp [targetGeomSum, mul_assoc]
    · have hqb0 : qb = 0 := Nat.eq_zero_of_not_pos hqb
      subst qb
      unfold threeRunCanonicalWord threeRunCanonicalBlocks
      rw [ite_eq_right (by omega : ¬ 0 < 0), ite_eq_right (by omega : ¬ 0 < 0)]
      change valueLSB (canonicalRepeat a aLast qa) = _
      rw [canonicalRepeat_value_geom haLen haValue qa]
      simp [targetGeomSum]

/-- 幅 4 以上の padding mismatch は、短い segment なら幅 4 で計算すればよい。 -/
private theorem mismatch_pad_eq_four
    {n : ℕ} {p q : List Bool}
    (hn : 4 ≤ n)
    (hp : p.length ≤ 4)
    (hq : q.length ≤ 4) :
    mismatchCount (padBlock n p) (padBlock n q) =
      mismatchCount (padBlock 4 p) (padBlock 4 q) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  simpa using
    (mismatchCount_padBlock_add_right
      (width := 4) (extra := d) hp hq)

/-- forward digit triple の二境界 mismatch は合計高々 5。 -/
private theorem forward_mismatch_bounds
    {n r : ℕ}
    (hn : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    let a := padBlock n (targetTwoLowSegment r)
    let b := padBlock n (targetTwoPowerSegment r)
    let c := padBlock n (targetTwoHighSegment r)
    mismatchCount a b + mismatchCount b c ≤ 5 ∧
      mismatchCount a c ≤ 5 ∧ mismatchCount a b ≤ 5 := by
  rcases hr with rfl | rfl
  · have hab := mismatch_pad_eq_four hn
      (p := targetTwoLowSegment 1) (q := targetTwoPowerSegment 1)
      (by norm_num [targetTwoLowSegment]) (by norm_num [targetTwoPowerSegment])
    have hbc := mismatch_pad_eq_four hn
      (p := targetTwoPowerSegment 1) (q := targetTwoHighSegment 1)
      (by norm_num [targetTwoPowerSegment]) (by norm_num [targetTwoHighSegment])
    have hac := mismatch_pad_eq_four hn
      (p := targetTwoLowSegment 1) (q := targetTwoHighSegment 1)
      (by norm_num [targetTwoLowSegment]) (by norm_num [targetTwoHighSegment])
    dsimp
    rw [hab, hbc, hac]
    norm_num [targetTwoLowSegment, targetTwoPowerSegment, targetTwoHighSegment,
      padBlock, List.replicate, mismatchCount]
  · have hab := mismatch_pad_eq_four hn
      (p := targetTwoLowSegment 2) (q := targetTwoPowerSegment 2)
      (by norm_num [targetTwoLowSegment]) (by norm_num [targetTwoPowerSegment])
    have hbc := mismatch_pad_eq_four hn
      (p := targetTwoPowerSegment 2) (q := targetTwoHighSegment 2)
      (by norm_num [targetTwoPowerSegment]) (by norm_num [targetTwoHighSegment])
    have hac := mismatch_pad_eq_four hn
      (p := targetTwoLowSegment 2) (q := targetTwoHighSegment 2)
      (by norm_num [targetTwoLowSegment]) (by norm_num [targetTwoHighSegment])
    dsimp
    rw [hab, hbc, hac]
    norm_num [targetTwoLowSegment, targetTwoPowerSegment, targetTwoHighSegment,
      padBlock, List.replicate, mismatchCount]

/-- reverse digit triple の二境界 mismatch は合計高々 5。 -/
private theorem reverse_mismatch_bounds
    {n r : ℕ}
    (hn : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    let a := padBlock n (targetTwoLowSegment r)
    let b := padBlock n (targetTwoReverseMiddleSegment r)
    let c := padBlock n (targetTwoHighSegment r)
    mismatchCount a b + mismatchCount b c ≤ 5 ∧
      mismatchCount a c ≤ 5 ∧ mismatchCount a b ≤ 5 := by
  rcases hr with rfl | rfl
  · have hab := mismatch_pad_eq_four hn
      (p := targetTwoLowSegment 1) (q := targetTwoReverseMiddleSegment 1)
      (by norm_num [targetTwoLowSegment]) (by norm_num [targetTwoReverseMiddleSegment])
    have hbc := mismatch_pad_eq_four hn
      (p := targetTwoReverseMiddleSegment 1) (q := targetTwoHighSegment 1)
      (by norm_num [targetTwoReverseMiddleSegment]) (by norm_num [targetTwoHighSegment])
    have hac := mismatch_pad_eq_four hn
      (p := targetTwoLowSegment 1) (q := targetTwoHighSegment 1)
      (by norm_num [targetTwoLowSegment]) (by norm_num [targetTwoHighSegment])
    dsimp
    rw [hab, hbc, hac]
    norm_num [targetTwoLowSegment, targetTwoReverseMiddleSegment, targetTwoHighSegment,
      padBlock, List.replicate, mismatchCount]
  · have hab := mismatch_pad_eq_four hn
      (p := targetTwoLowSegment 2) (q := targetTwoReverseMiddleSegment 2)
      (by norm_num [targetTwoLowSegment]) (by norm_num [targetTwoReverseMiddleSegment])
    have hbc := mismatch_pad_eq_four hn
      (p := targetTwoReverseMiddleSegment 2) (q := targetTwoHighSegment 2)
      (by norm_num [targetTwoReverseMiddleSegment]) (by norm_num [targetTwoHighSegment])
    have hac := mismatch_pad_eq_four hn
      (p := targetTwoLowSegment 2) (q := targetTwoHighSegment 2)
      (by norm_num [targetTwoLowSegment]) (by norm_num [targetTwoHighSegment])
    dsimp
    rw [hab, hbc, hac]
    norm_num [targetTwoLowSegment, targetTwoReverseMiddleSegment, targetTwoHighSegment,
      padBlock, List.replicate, mismatchCount]

/-- wrapped digit triple の二境界 mismatch は合計高々 5。 -/
private theorem wrapped_mismatch_bounds
    {n r : ℕ}
    (hn : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    let a := padBlock n (targetTwoWrappedLowSegment r)
    let b := padBlock n (targetTwoReverseMiddleSegment r)
    let c := padBlock n (targetTwoHighSegment r)
    mismatchCount a b + mismatchCount b c ≤ 5 ∧
      mismatchCount a c ≤ 5 ∧ mismatchCount a b ≤ 5 := by
  rcases hr with rfl | rfl
  · have hab := mismatch_pad_eq_four hn
      (p := targetTwoWrappedLowSegment 1) (q := targetTwoReverseMiddleSegment 1)
      (by norm_num [targetTwoWrappedLowSegment]) (by norm_num [targetTwoReverseMiddleSegment])
    have hbc := mismatch_pad_eq_four hn
      (p := targetTwoReverseMiddleSegment 1) (q := targetTwoHighSegment 1)
      (by norm_num [targetTwoReverseMiddleSegment]) (by norm_num [targetTwoHighSegment])
    have hac := mismatch_pad_eq_four hn
      (p := targetTwoWrappedLowSegment 1) (q := targetTwoHighSegment 1)
      (by norm_num [targetTwoWrappedLowSegment]) (by norm_num [targetTwoHighSegment])
    dsimp
    rw [hab, hbc, hac]
    norm_num [targetTwoWrappedLowSegment, targetTwoReverseMiddleSegment, targetTwoHighSegment,
      padBlock, List.replicate, mismatchCount]
  · have hab := mismatch_pad_eq_four hn
      (p := targetTwoWrappedLowSegment 2) (q := targetTwoReverseMiddleSegment 2)
      (by norm_num [targetTwoWrappedLowSegment]) (by norm_num [targetTwoReverseMiddleSegment])
    have hbc := mismatch_pad_eq_four hn
      (p := targetTwoReverseMiddleSegment 2) (q := targetTwoHighSegment 2)
      (by norm_num [targetTwoReverseMiddleSegment]) (by norm_num [targetTwoHighSegment])
    have hac := mismatch_pad_eq_four hn
      (p := targetTwoWrappedLowSegment 2) (q := targetTwoHighSegment 2)
      (by norm_num [targetTwoWrappedLowSegment]) (by norm_num [targetTwoHighSegment])
    dsimp
    rw [hab, hbc, hac]
    norm_num [targetTwoWrappedLowSegment, targetTwoReverseMiddleSegment, targetTwoHighSegment,
      padBlock, List.replicate, mismatchCount]

/--
三 digit run の exact value と小さい境界 mismatch があれば、canonical binary word は
period `n` の break を高々 5 個しか持たない。
-/
private theorem hasPeriodBreakAtMostFive_of_threeRun
    {x n qa qb qc : ℕ}
    {aLast bLast cLast : List Bool}
    (hn : 4 ≤ n)
    (hqa : 0 < qa)
    (haLen4 : aLast.length ≤ 4)
    (hbLen4 : bLast.length ≤ 4)
    (hcLen4 : cLast.length ≤ 4)
    (haEnd : ∃ u, aLast = u ++ [true])
    (hbEnd : ∃ u, bLast = u ++ [true])
    (hcEnd : ∃ u, cLast = u ++ [true])
    (hABBC :
      mismatchCount (padBlock n aLast) (padBlock n bLast) +
        mismatchCount (padBlock n bLast) (padBlock n cLast) ≤ 5)
    (hAC : mismatchCount (padBlock n aLast) (padBlock n cLast) ≤ 5)
    (hAB : mismatchCount (padBlock n aLast) (padBlock n bLast) ≤ 5)
    (hValue :
      x =
        valueLSB aLast * targetGeomSum (2 ^ n) qa +
        (2 ^ n) ^ qa * valueLSB bLast * targetGeomSum (2 ^ n) qb +
        (2 ^ n) ^ (qa + qb) * valueLSB cLast * targetGeomSum (2 ^ n) qc) :
    HasPeriodBreakAtMost x n 5 := by
  let a := padBlock n aLast
  let b := padBlock n bLast
  let c := padBlock n cLast
  let bits := threeRunCanonicalWord a aLast b bLast c cLast qa qb qc
  have haLenN : aLast.length ≤ n := le_trans haLen4 hn
  have hbLenN : bLast.length ≤ n := le_trans hbLen4 hn
  have hcLenN : cLast.length ≤ n := le_trans hcLen4 hn
  have haLen : a.length = n := padBlock_length haLenN
  have hbLen : b.length = n := padBlock_length hbLenN
  have hcLen : c.length = n := padBlock_length hcLenN
  have haValue : valueLSB aLast = valueLSB a := by
    symm
    exact padBlock_value
  have hbValue : valueLSB bLast = valueLSB b := by
    symm
    exact padBlock_value
  have hcValue : valueLSB cLast = valueLSB c := by
    symm
    exact padBlock_value
  have hWordValue : valueLSB bits = x := by
    have h := threeRunCanonicalWord_value_geom
      (n := n) (a := a) (aLast := aLast)
      (b := b) (bLast := bLast) (c := c) (cLast := cLast)
      (qa := qa) (qb := qb) (qc := qc)
      haLen hbLen hcLen haValue hbValue hcValue
    rw [← haValue, ← hbValue, ← hcValue] at h
    exact h.trans hValue.symm
  have hBitLength : HasBitLength x bits.length := by
    rw [← hWordValue]
    simpa [bits, a, b, c] using
      (threeRunCanonicalWord_hasBitLength
        (a := a) (aLast := aLast)
        (b := b) (bLast := bLast)
        (c := c) (cLast := cLast)
        (qa := qa) (qb := qb) (qc := qc)
        hqa haEnd hbEnd hcEnd)
  have haa : mismatchCount a aLast = 0 :=
    mismatchCount_padBlock_segment
  have hbb : mismatchCount b bLast = 0 :=
    mismatchCount_padBlock_segment
  have hcc : mismatchCount c cLast = 0 :=
    mismatchCount_padBlock_segment
  have hBreak : periodBreakCount n bits ≤ 5 := by
    apply threeRunCanonical_periodBreakCount_le
      hqa haLen hbLen hcLen haLenN hbLenN hcLenN haa hbb hcc
    · simpa [a, b, c] using hABBC
    · simpa [a, c] using hAC
    · simpa [a, b] using hAB
  exact ⟨bits, bits.length, ⟨rfl, hWordValue⟩, hBitLength, hBreak⟩

/-- split-forward geometric data は period `n` の break を高々5個しか持たない。 -/
theorem TargetTwoHoleSplitForwardGeometricData.hasPeriodBreakAtMostFive
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b)
    (hn : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    HasPeriodBreakAtMost (3 ^ k) n 5 := by
  let aLast := targetTwoLowSegment r
  let bLast := targetTwoPowerSegment r
  let cLast := targetTwoHighSegment r
  have hqbu : h.q + (h.u - h.q) = h.u :=
    Nat.add_sub_of_le h.q_le_u
  have huct : h.u + (h.t - h.u) = h.t :=
    Nat.add_sub_of_le h.u_le_t
  have hLenA : aLast.length ≤ 4 := by
    rcases hr with rfl | rfl <;> norm_num [aLast, targetTwoLowSegment]
  have hLenB : bLast.length ≤ 4 := by
    rcases hr with rfl | rfl <;> norm_num [bLast, targetTwoPowerSegment]
  have hLenC : cLast.length ≤ 4 := by
    rcases hr with rfl | rfl <;> norm_num [cLast, targetTwoHighSegment]
  have hEndA : ∃ u, aLast = u ++ [true] := by
    rcases hr with rfl | rfl
    · exact ⟨[], by simp [aLast, targetTwoLowSegment]⟩
    · exact ⟨[true], by simp [aLast, targetTwoLowSegment]⟩
  have hEndB : ∃ u, bLast = u ++ [true] :=
    ⟨List.replicate r false, rfl⟩
  have hEndC : ∃ u, cLast = u ++ [true] :=
    ⟨List.replicate (r + 1) false, rfl⟩
  rcases forward_mismatch_bounds hn hr with ⟨hABBC, hAC, hAB⟩
  apply hasPeriodBreakAtMostFive_of_threeRun
    (x := 3 ^ k) (n := n)
    (qa := h.q) (qb := h.u - h.q) (qc := h.t - h.u)
    hn h.q_pos hLenA hLenB hLenC hEndA hEndB hEndC hABBC hAC hAB
  rw [value_lowSegment, value_powerSegment, value_highSegment]
  have hNormal := h.baseBlock_normalForm
  simpa [hqbu, pow_add, mul_assoc, mul_left_comm, mul_comm] using hNormal

/-- split-reverse geometric data は period `n` の break を高々5個しか持たない。 -/
theorem TargetTwoHoleSplitReverseGeometricData.hasPeriodBreakAtMostFive
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b)
    (hn : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    HasPeriodBreakAtMost (3 ^ k) n 5 := by
  let aLast := targetTwoLowSegment r
  let bLast := targetTwoReverseMiddleSegment r
  let cLast := targetTwoHighSegment r
  have huq : h.u + (h.q - h.u) = h.q :=
    Nat.add_sub_of_le (Nat.le_of_lt h.u_lt_q)
  have hqt : h.q + (h.t - h.q) = h.t :=
    Nat.add_sub_of_le h.q_le_t
  have hLenA : aLast.length ≤ 4 := by
    rcases hr with rfl | rfl <;> norm_num [aLast, targetTwoLowSegment]
  have hLenB : bLast.length ≤ 4 := by
    rcases hr with rfl | rfl <;> norm_num [bLast, targetTwoReverseMiddleSegment]
  have hLenC : cLast.length ≤ 4 := by
    rcases hr with rfl | rfl <;> norm_num [cLast, targetTwoHighSegment]
  have hEndA : ∃ u, aLast = u ++ [true] := by
    rcases hr with rfl | rfl
    · exact ⟨[], by simp [aLast, targetTwoLowSegment]⟩
    · exact ⟨[true], by simp [aLast, targetTwoLowSegment]⟩
  have hEndB : ∃ u, bLast = u ++ [true] := by
    rcases hr with rfl | rfl
    · exact ⟨[true], by simp [bLast, targetTwoReverseMiddleSegment]⟩
    · exact ⟨[true, true], by simp [bLast, targetTwoReverseMiddleSegment]⟩
  have hEndC : ∃ u, cLast = u ++ [true] :=
    ⟨List.replicate (r + 1) false, rfl⟩
  rcases reverse_mismatch_bounds hn hr with ⟨hABBC, hAC, hAB⟩
  apply hasPeriodBreakAtMostFive_of_threeRun
    (x := 3 ^ k) (n := n)
    (qa := h.u) (qb := h.q - h.u) (qc := h.t - h.q)
    hn h.u_pos hLenA hLenB hLenC hEndA hEndB hEndC hABBC hAC hAB
  rw [value_lowSegment, value_reverseMiddleSegment, value_highSegment]
  have hNormal := h.baseBlock_normalForm
  simpa [huq, pow_add, mul_assoc, mul_left_comm, mul_comm] using hNormal

/-- wrapped geometric data は `2*3^k` の canonical block word を経由して break≤5 を与える。 -/
theorem TargetTwoHoleWrappedGeometricData.hasPeriodBreakAtMostFive
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b)
    (hn : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    HasPeriodBreakAtMost (3 ^ k) n 5 := by
  let aLast := targetTwoWrappedLowSegment r
  let bLast := targetTwoReverseMiddleSegment r
  let cLast := targetTwoHighSegment r
  have hqu : h.q + (h.u - h.q) = h.u :=
    Nat.add_sub_of_le (Nat.le_of_lt h.q_lt_u)
  have hut : h.u + (h.t - h.u) = h.t :=
    Nat.add_sub_of_le h.u_le_t
  have hLenA : aLast.length ≤ 4 := by
    rcases hr with rfl | rfl <;> norm_num [aLast, targetTwoWrappedLowSegment]
  have hLenB : bLast.length ≤ 4 := by
    rcases hr with rfl | rfl <;> norm_num [bLast, targetTwoReverseMiddleSegment]
  have hLenC : cLast.length ≤ 4 := by
    rcases hr with rfl | rfl <;> norm_num [cLast, targetTwoHighSegment]
  have hEndA : ∃ u, aLast = u ++ [true] := by
    rcases hr with rfl | rfl
    · exact ⟨[false], by simp [aLast, targetTwoWrappedLowSegment]⟩
    · exact ⟨[false, true], by simp [aLast, targetTwoWrappedLowSegment]⟩
  have hEndB : ∃ u, bLast = u ++ [true] := by
    rcases hr with rfl | rfl
    · exact ⟨[true], by simp [bLast, targetTwoReverseMiddleSegment]⟩
    · exact ⟨[true, true], by simp [bLast, targetTwoReverseMiddleSegment]⟩
  have hEndC : ∃ u, cLast = u ++ [true] :=
    ⟨List.replicate (r + 1) false, rfl⟩
  rcases wrapped_mismatch_bounds hn hr with ⟨hABBC, hAC, hAB⟩
  have hTwo : HasPeriodBreakAtMost (2 * 3 ^ k) n 5 := by
    apply hasPeriodBreakAtMostFive_of_threeRun
      (x := 2 * 3 ^ k) (n := n)
      (qa := h.q) (qb := h.u - h.q) (qc := h.t - h.u)
      hn h.q_pos hLenA hLenB hLenC hEndA hEndB hEndC hABBC hAC hAB
    rw [value_wrappedLowSegment, value_reverseMiddleSegment, value_highSegment]
    have hNormal := h.baseBlock_normalForm
    simpa [hqu, pow_add, mul_assoc, mul_left_comm, mul_comm] using hNormal
  exact HasPeriodBreakAtMost.of_two_mul
    (x := 3 ^ k) (period := n) (bound := 5)
    (by positivity) (by omega) hTwo

/--
`BlockComplexity.lean` に残していた target-two の内部 target を閉じる。
三 geometric phase のどれに入っても `Binary.HasPeriodBreakAtMost (3^k) n 5` が成立する。
-/
theorem targetTwo_periodBreakAtMostFive :
    TargetTwoHolePeriodBreakAtMostFive := by
  intro k n r L a b hn hr hGeom
  rcases hGeom with hWrapped | hRest
  · rcases hWrapped with ⟨h⟩
    exact h.hasPeriodBreakAtMostFive hn hr
  · rcases hRest with hForward | hReverse
    · rcases hForward with ⟨h⟩
      exact h.hasPeriodBreakAtMostFive hn hr
    · rcases hReverse with ⟨h⟩
      exact h.hasPeriodBreakAtMostFive hn hr

/-- Stephan 側の外部 corollaryだけを受け取れば、target-two `n≥4` の bounded-depth が得られる完成形。 -/
theorem targetTwo_depth_bounded_of_stephan_internal
    (hStephan : StephanValuationWidthPeriodBreakEscape) :
    ∃ K : ℕ,
      ∀ {k n r L a b : ℕ},
        2 ≤ k →
        4 ≤ n →
        ((r = 1 ∧ Even k) ∨ (r = 2 ∧ k % 2 = 1)) →
        TargetTwoHoleGeometricBranch k n r L a b →
        k < K :=
  targetTwo_depth_bounded_of_stephan hStephan targetTwo_periodBreakAtMostFive

end Mersenne
end Collatz3
