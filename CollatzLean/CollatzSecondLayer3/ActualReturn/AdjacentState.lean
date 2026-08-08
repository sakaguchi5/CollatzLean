import CollatzLean.CollatzSecondLayer3.ActualReturn.FutureMinimumGeometry

/-!
# 隣接 future-minimum actual-return state

first crossing の存在を仮定せず、標準 future-minimum の隣接二区間そのものを
発散側の正本局所状態として扱う。

`j` 番目の標準 future-minimum から `j+1` 番目までを

* 長さ `r`
* 総2進指数 `H`
* affine 定数 `B`
* 値差 `Δ`

で記述する。非有界軌道では `Δ` は4の正倍数である。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 標準 future-minimum の隣接二区間の指数語。 -/
noncomputable def adjacentFutureMinimumWord
    (O : OddOrbit) (j : ℕ) : ExpWord :=
  O.segmentWord
    (O.futureMinIndex j)
    (consecutiveFutureMinimumIndexGap O j)

/--
標準 future-minimum の隣接 actual return。
first crossing・Special C3・negative shadow は公開状態に含めない。
-/
structure AdjacentFutureMinimumReturnData (O : OddOrbit) where
  unbounded : O.Unbounded
  index : ℕ

namespace AdjacentFutureMinimumReturnData

/-- 任意の標準 future-minimum 添字から隣接 return state を作る。 -/
def ofIndex
    (O : OddOrbit)
    (hU : O.Unbounded)
    (j : ℕ) : AdjacentFutureMinimumReturnData O :=
  { unbounded := hU
    index := j }

/-- current 標準 future-minimum の位置。 -/
noncomputable def startIndex
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  O.futureMinIndex R.index

/-- next 標準 future-minimum の位置。 -/
noncomputable def nextIndex
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  O.futureMinIndex (R.index + 1)

/-- 隣接 future-minimum 間の odd-step 長。 -/
noncomputable def length
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  consecutiveFutureMinimumIndexGap O R.index

/-- 隣接区間の actual exponent word。 -/
noncomputable def word
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) : ExpWord :=
  adjacentFutureMinimumWord O R.index

/-- current future-minimum 値。 -/
noncomputable def startValue
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  O.value R.startIndex

/-- next future-minimum 値。 -/
noncomputable def nextValue
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  O.value R.nextIndex

/-- 隣接 future-minimum の正値差 `Δ`。 -/
noncomputable def valueGap
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  consecutiveFutureMinimumValueGap O R.index

/-- 隣接区間の総2進指数 `H`。 -/
noncomputable def totalExponent
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  twoSteps R.word

/-- 隣接区間の affine 定数 `B`。 -/
noncomputable def affineConstant
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) : ℕ :=
  affineConst R.word

/-- next index は start index に隣接長を足した位置。 -/
theorem nextIndex_eq_startIndex_add_length
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    R.nextIndex = R.startIndex + R.length := by
  unfold nextIndex startIndex length consecutiveFutureMinimumIndexGap
  have h := O.futureMinIndex_lt_succ R.index
  omega

/-- 隣接 future-minimum 間の長さは正。 -/
theorem length_pos
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    0 < R.length := by
  unfold length consecutiveFutureMinimumIndexGap
  exact Nat.sub_pos_of_lt (O.futureMinIndex_lt_succ R.index)

/-- 隣接 word の長さは `r`。 -/
@[simp] theorem word_length
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    R.word.length = R.length := by
  simp [word, adjacentFutureMinimumWord, length]

/-- 隣接 word は非空。 -/
theorem word_nonempty
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    R.word ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  have hpos := R.length_pos
  simp at hlen
  omega

/-- 隣接 word は actual orbit 由来なので valid。 -/
theorem word_valid
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    Valid R.word := by
  change
    Valid
      (O.segmentWord
        (O.futureMinIndex R.index)
        (consecutiveFutureMinimumIndexGap O R.index))
  exact
    (O.runs_segment
      (O.futureMinIndex R.index)
      (consecutiveFutureMinimumIndexGap O R.index)).valid

/-- 隣接 word の odd step 数は `r`。 -/
theorem oddSteps_word
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    oddSteps R.word = R.length := by
  simp [oddSteps]

/-- 隣接 future-minimum 間は actual finite run。 -/
theorem realizes
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    Realizes R.word R.startValue R.nextValue := by
  change
    Realizes
      (O.segmentWord R.startIndex R.length)
      (O.value R.startIndex)
      (O.value R.nextIndex)
  rw [R.nextIndex_eq_startIndex_add_length]
  exact O.realizes_segment R.startIndex R.length

/-- 隣接 actual return の基本 affine 方程式。 -/
theorem scaled_return_equation
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    2 ^ R.totalExponent * R.nextValue =
      3 ^ R.length * R.startValue + R.affineConstant := by
  have h := R.realizes
  unfold Realizes at h
  rw [R.oddSteps_word] at h
  simpa [totalExponent, affineConstant] using h

/-- next value は start value に正差 `Δ` を足したもの。 -/
theorem nextValue_eq_startValue_add_valueGap
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    R.nextValue = R.startValue + R.valueGap := by
  unfold nextValue startValue valueGap nextIndex startIndex
  unfold consecutiveFutureMinimumValueGap
  have hlt := O.futureMinValue_lt_succ R.unbounded R.index
  omega

/-- 隣接 future-minimum 値差は正。 -/
theorem valueGap_pos
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    0 < R.valueGap := by
  simpa [valueGap] using
    consecutiveFutureMinimumValueGap_pos O R.unbounded R.index

/-- 隣接 future-minimum 値差は4以上。 -/
theorem four_le_valueGap
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    4 ≤ R.valueGap := by
  simpa [valueGap] using
    four_le_consecutiveFutureMinimumValueGap O R.unbounded R.index

/-- 隣接 future-minimum 値差は4の倍数。 -/
theorem valueGap_eq_four_mul
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    ∃ q : ℕ, R.valueGap = 4 * q := by
  simpa [valueGap] using
    four_dvd_consecutiveFutureMinimumValueGap O R.unbounded R.index

/-- current future-minimum の actual exponent は exact に1。 -/
theorem startExponent_eq_one
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    O.exponent R.startIndex = 1 := by
  simpa [startIndex] using
    futureMinimum_exponent_eq_one_of_unbounded
      O R.unbounded (O.futureMinimumAt_futureMinIndex R.index)

/-- next future-minimum の actual exponent も exact に1。 -/
theorem nextExponent_eq_one
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    O.exponent R.nextIndex = 1 := by
  simpa [nextIndex] using
    futureMinimum_exponent_eq_one_of_unbounded
      O R.unbounded (O.futureMinimumAt_futureMinIndex (R.index + 1))

/-- 隣接 word は pure expanding または pure contracting のどちらか。 -/
theorem expanding_or_contracting
    {O : OddOrbit} (R : AdjacentFutureMinimumReturnData O) :
    Expanding R.word ∨ Contracting R.word :=
  expanding_or_contracting_of_valid_nonempty
    R.word_valid R.word_nonempty

/--
隣接長が2以上なら、最初の1 stepを除いた suffix 全体は next future-minimum へ
真に下がるため contracting。
-/
theorem tail_contracting
    {O : OddOrbit}
    (R : AdjacentFutureMinimumReturnData O)
    (hlen : 1 < R.length) :
    Contracting
      (O.segmentWord (R.startIndex + 1) (R.length - 1)) := by
  have hleft : R.startIndex < R.startIndex + 1 := by omega
  have hnext := R.nextIndex_eq_startIndex_add_length
  have hright : R.startIndex + 1 < R.nextIndex := by
    omega
  have hsuffix :=
    suffix_to_nextFutureMinimum_contracting
      O R.unbounded R.index (R.startIndex + 1)
      (by simp only [startIndex, lt_add_iff_pos_right, Order.lt_one_iff])
      (by simpa [nextIndex] using hright)
  have hsuffix' :
      Contracting
        (O.segmentWord
          (R.startIndex + 1)
          (R.nextIndex - (R.startIndex + 1))) := by
    simpa [nextIndex] using hsuffix
  have hq :
      R.nextIndex - (R.startIndex + 1) = R.length - 1 := by
    omega
  rw [hq] at hsuffix'
  exact hsuffix'

end AdjacentFutureMinimumReturnData
end CollatzSecondLayer3
