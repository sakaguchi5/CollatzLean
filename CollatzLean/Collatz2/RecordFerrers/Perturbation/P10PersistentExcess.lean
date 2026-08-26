import CollatzLean.Collatz2.RecordFerrers.Perturbation.P09OneBitDefectLaw

/-!
# Record–Ferrers 摂動理論 10: 局所欠陥から境界 excess への翻訳と持続

carry 0 が一度生じると、その場所の局所 boundary excess は正確に 1 になる。
P09 で分離した左欠陥・右欠陥を boundary excess の左右位置へ翻訳し、
隣接二 block 全体では excess が正確に 1 であることを示す。
さらに、その後の carry がすべて 1 なら、この excess 1 は後方へそのまま持続する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace Skeleton

/-- 指定開始位置以後の全 block carry が 1 であること。空列では自明。 -/
def AllCarryOneFrom (start : ℕ) : List ℕ → Prop
  | [] => True
  | r :: rs =>
      criticalCarry start r = 1 ∧ AllCarryOneFrom (start + r) rs

/-- 全 carry が 1 の後続列では zero carry は一つも現れない。 -/
theorem zeroCarryCountFrom_eq_zero_of_allCarryOne
    (start : ℕ)
    (rs : List ℕ)
    (h : AllCarryOneFrom start rs) :
    zeroCarryCountFrom start rs = 0 := by
  induction rs generalizing start with
  | nil => rfl
  | cons r rs ih =>
      change
        criticalCarry start r = 1 ∧
          AllCarryOneFrom (start + r) rs at h
      simp [zeroCarryCountFrom, h.1, ih (start + r) h.2]

/-- zero-carry 個数は list の連結に対して、開始位置をずらして加法的。 -/
theorem zeroCarryCountFrom_append
    (start : ℕ)
    (xs ys : List ℕ) :
    zeroCarryCountFrom start (xs ++ ys) =
      zeroCarryCountFrom start xs +
        zeroCarryCountFrom (start + xs.sum) ys := by
  induction xs generalizing start with
  | nil =>
      simp [zeroCarryCountFrom]
  | cons r rs ih =>
      simp only [List.cons_append, List.sum_cons, zeroCarryCountFrom]
      rw [ih (start + r)]
      simp [Nat.add_assoc]

/-- 全 carry が 1 の後続列を追加しても、すでにある boundary excess は変わらない。 -/
theorem boundaryExcessInt_append_eq_of_allCarryOne
    (start : ℕ)
    (leftCtx tail : List ℕ)
    (hTail : AllCarryOneFrom (start + leftCtx.sum) tail) :
    boundaryExcessInt start (leftCtx ++ tail) =
      boundaryExcessInt start leftCtx := by
  rw [boundaryExcessInt_eq_zeroCarryCountFrom,
      boundaryExcessInt_eq_zeroCarryCountFrom,
      zeroCarryCountFrom_append]
  rw [zeroCarryCountFrom_eq_zero_of_allCarryOne
    (start + leftCtx.sum) tail hTail]
  simp

/--
一個の欠陥によって excess が 1 になった後、
後続 carry がすべて 1 なら excess 1 は持続する。
-/
theorem persistent_excess_after_single_carry_failure
    (start : ℕ)
    (leftCtx tail : List ℕ)
    (hExcess : boundaryExcessInt start leftCtx = 1)
    (hTail : AllCarryOneFrom (start + leftCtx.sum) tail) :
    boundaryExcessInt start (leftCtx ++ tail) = 1 := by
  rw [boundaryExcessInt_append_eq_of_allCarryOne
    start leftCtx tail hTail]
  exact hExcess

/--
左 carry 欠陥は、左 block の局所 excess が 1、右 block の局所 excess が 0
であることと正確に同値。
-/
theorem leftCarryDefect_iff_localBoundaryExcess
    (a r s : ℕ) :
    LeftCarryDefect a r s ↔
      boundaryExcessInt a [r] = 1 ∧
        boundaryExcessInt (a + r) [s] = 0 := by
  unfold LeftCarryDefect
  rw [boundaryExcessInt_singleton_eq_one_iff,
      boundaryExcessInt_singleton_eq_zero_iff]

/--
右 carry 欠陥は、左 block の局所 excess が 0、右 block の局所 excess が 1
であることと正確に同値。
-/
theorem rightCarryDefect_iff_localBoundaryExcess
    (a r s : ℕ) :
    RightCarryDefect a r s ↔
      boundaryExcessInt a [r] = 0 ∧
        boundaryExcessInt (a + r) [s] = 1 := by
  unfold RightCarryDefect
  rw [boundaryExcessInt_singleton_eq_zero_iff,
      boundaryExcessInt_singleton_eq_one_iff]

/-- 左欠陥が一つある隣接二 block 全体の boundary excess は正確に 1。 -/
theorem boundaryExcessInt_pair_eq_one_of_leftCarryDefect
    (a r s : ℕ)
    (h : LeftCarryDefect a r s) :
    boundaryExcessInt a [r, s] = 1 := by
  rw [boundaryExcessInt_eq_zeroCarryCountFrom]
  unfold LeftCarryDefect at h
  simp [zeroCarryCountFrom, h.1, h.2]

/-- 右欠陥が一つある隣接二 block 全体の boundary excess は正確に 1。 -/
theorem boundaryExcessInt_pair_eq_one_of_rightCarryDefect
    (a r s : ℕ)
    (h : RightCarryDefect a r s) :
    boundaryExcessInt a [r, s] = 1 := by
  rw [boundaryExcessInt_eq_zeroCarryCountFrom]
  unfold RightCarryDefect at h
  simp [zeroCarryCountFrom, h.1, h.2]

/--
全長保存移送後に局所 carry が 0 になることは、
左右どちらか一方の局所 boundary excess だけが 1 になることと同値。
-/
theorem adjacentTransfer_localCarry_zero_iff_localBoundaryExcess
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s') :
    criticalCarry r' s' = 0 ↔
      (boundaryExcessInt a [r'] = 1 ∧
          boundaryExcessInt (a + r') [s'] = 0) ∨
        (boundaryExcessInt a [r'] = 0 ∧
          boundaryExcessInt (a + r') [s'] = 1) := by
  rw [adjacentTransfer_localCarry_zero_iff_left_or_right_defect hOld T]
  rw [leftCarryDefect_iff_localBoundaryExcess,
      rightCarryDefect_iff_localBoundaryExcess]

/--
全長保存移送後に局所 carry が 0 なら、
新しい隣接二 block 全体の boundary excess は正確に 1。
-/
theorem adjacentTransfer_boundaryExcessInt_pair_eq_one_of_localCarry_zero
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s')
    (hLocal : criticalCarry r' s' = 0) :
    boundaryExcessInt a [r', s'] = 1 := by
  have hDefect :=
    (adjacentTransfer_localCarry_zero_iff_left_or_right_defect hOld T).1 hLocal
  rcases hDefect with hLeft | hRight
  · exact boundaryExcessInt_pair_eq_one_of_leftCarryDefect a r' s' hLeft
  · exact boundaryExcessInt_pair_eq_one_of_rightCarryDefect a r' s' hRight

/--
全長保存移送が一個の局所欠陥を作り、その後の carry がすべて 1 なら、
その隣接二 block で生じた boundary excess 1 は後続列の最後まで持続する。
-/
theorem persistent_excess_after_adjacentTransfer_localCarry_zero
    {a r s r' s' : ℕ}
    (hOld : InteriorPairCarry a r s)
    (T : AdjacentLengthTransfer r s r' s')
    (hLocal : criticalCarry r' s' = 0)
    (tail : List ℕ)
    (hTail : AllCarryOneFrom ((a + r') + s') tail) :
    boundaryExcessInt a ([r', s'] ++ tail) = 1 := by
  have hPair : boundaryExcessInt a [r', s'] = 1 :=
    adjacentTransfer_boundaryExcessInt_pair_eq_one_of_localCarry_zero
      hOld T hLocal
  have hTail' : AllCarryOneFrom (a + [r', s'].sum) tail := by
    simpa [Nat.add_assoc] using hTail
  exact persistent_excess_after_single_carry_failure
    a [r', s'] tail hPair hTail'

end Skeleton

end RecordFerrers
end Collatz2
