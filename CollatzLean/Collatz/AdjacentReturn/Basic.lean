import CollatzLean.Collatz.OddOrbit.StandardFutureMinimum
import CollatzLean.Collatz.Word.Geometry

/-!
# 隣接future-minimum return

標準列を選ぶ操作と、選択済み隣接区間の有限解析を分離する。
`State`自身の全projectionはcomputableである。
標準tail-minimum列の隣接性もState/Towerに明示保存する。
-/

namespace Collatz
namespace AdjacentReturn

/-- 選択済み標準future-minimum列上の一つの隣接return。 -/
structure State (O : OddOrbit) where
  unbounded : O.Unbounded
  minima : O.FutureMinima
  standard : minima.IsStandard
  index : ℕ

namespace State

/-- current future-minimum位置。 -/
def startIndex {O : OddOrbit} (R : State O) : ℕ := R.minima.index R.index

/-- next future-minimum位置。 -/
def nextIndex {O : OddOrbit} (R : State O) : ℕ := R.minima.index (R.index + 1)

/-- 隣接位置差。 -/
def length {O : OddOrbit} (R : State O) : ℕ := R.nextIndex - R.startIndex

/-- 隣接actual exponent word。 -/
def word {O : OddOrbit} (R : State O) : Collatz.Word :=
  O.segment R.startIndex R.length

/-- current値。 -/
def startValue {O : OddOrbit} (R : State O) : ℕ := O.value R.startIndex

/-- next値。 -/
def nextValue {O : OddOrbit} (R : State O) : ℕ := O.value R.nextIndex

/-- 隣接値差。 -/
def valueGap {O : OddOrbit} (R : State O) : ℕ := R.nextValue - R.startValue

/-- 総2除算数。 -/
def totalExponent {O : OddOrbit} (R : State O) : ℕ := R.word.twoSteps

/-- affine定数。 -/
def affineConstant {O : OddOrbit} (R : State O) : ℕ := R.word.affineConst

/-- next indexのexact位置。 -/
theorem nextIndex_eq_startIndex_add_length
    {O : OddOrbit} (R : State O) :
    R.nextIndex = R.startIndex + R.length := by
  have h :
      R.minima.index R.index ≤ R.minima.index (R.index + 1) := by
    exact (R.minima.index_strict
      (show R.index < R.index.succ by omega)).le
  change R.minima.index (R.index + 1) =
    R.minima.index R.index +
      (R.minima.index (R.index + 1) - R.minima.index R.index)
  simpa [Nat.add_comm] using (Nat.sub_add_cancel h).symm

/-- 隣接長は正。 -/
theorem length_pos {O : OddOrbit} (R : State O) : 0 < R.length := by
  unfold length
  exact Nat.sub_pos_of_lt (R.minima.index_strict (Nat.lt_succ_self R.index))

@[simp] theorem word_length {O : OddOrbit} (R : State O) :
    R.word.length = R.length := by simp [word]

/-- 隣接wordは非空。 -/
theorem word_nonempty {O : OddOrbit} (R : State O) : R.word ≠ [] := by
  intro h
  have hzero : R.length = 0 := by
    simpa using congrArg List.length h
  exact (length_pos R).ne' hzero

/-- 隣接wordはactual run由来なのでvalid。 -/
theorem word_valid {O : OddOrbit} (R : State O) : R.word.Valid := by
  exact (O.runsSegment R.startIndex R.length).valid

/-- 隣接returnのactual realization。 -/
theorem realizes {O : OddOrbit} (R : State O) :
    R.word.Realizes R.startValue R.nextValue := by
  unfold word startValue nextValue
  rw [R.nextIndex_eq_startIndex_add_length]
  exact O.realizesSegment R.startIndex R.length

/-- 隣接future-minimum値は真に増える。 -/
theorem startValue_lt_nextValue {O : OddOrbit} (R : State O) :
    R.startValue < R.nextValue := by
  exact R.minima.value_strict (Nat.lt_succ_self R.index)

/-- 値差は正。 -/
theorem valueGap_pos {O : OddOrbit} (R : State O) : 0 < R.valueGap := by
  unfold valueGap
  exact Nat.sub_pos_of_lt R.startValue_lt_nextValue

theorem nextValue_eq_startValue_add_valueGap {O : OddOrbit} (R : State O) :
    R.nextValue = R.startValue + R.valueGap := by
  unfold valueGap
  rw [Nat.add_comm]
  exact (Nat.sub_add_cancel R.startValue_lt_nextValue.le).symm

/-- 隣接wordはexpandingまたはcontracting。 -/
theorem expanding_or_contracting {O : OddOrbit} (R : State O) :
    R.word.Expanding ∨ R.word.Contracting :=
  Word.expanding_or_contracting_of_valid_nonempty R.word_valid R.word_nonempty

/-- expanding枝。 -/
def IsExpanding {O : OddOrbit} (R : State O) : Prop := R.word.Expanding

/-- contracting枝。 -/
def IsContracting {O : OddOrbit} (R : State O) : Prop := R.word.Contracting

/-- expanding determinant gap。 -/
def expandingGap {O : OddOrbit} (R : State O) : ℕ :=
  3 ^ R.length - 2 ^ R.totalExponent

/-- contracting determinant gap。 -/
def contractingGap {O : OddOrbit} (R : State O) : ℕ :=
  2 ^ R.totalExponent - 3 ^ R.length

/-- odd step数は隣接長。 -/
theorem oddSteps_word {O : OddOrbit} (R : State O) : R.word.oddSteps = R.length := by
  simp [Word.oddSteps]

/-- 隣接returnの基本アフィン方程式。 -/
theorem scaledEquation {O : OddOrbit} (R : State O) :
    2 ^ R.totalExponent * R.nextValue =
      3 ^ R.length * R.startValue + R.affineConstant := by
  have h := R.realizes
  unfold Word.Realizes at h
  rw [R.oddSteps_word] at h
  simpa [totalExponent, affineConstant] using h

/-- expanding枝のexact局所整数方程式。 -/
theorem expandingIdentity
    {O : OddOrbit} (R : State O) (hE : R.IsExpanding) :
    2 ^ R.totalExponent * R.valueGap =
      R.expandingGap * R.startValue + R.affineConstant := by
  have hE' : 2 ^ R.totalExponent < 3 ^ R.length := by
    simpa [IsExpanding, Word.Expanding, totalExponent, R.oddSteps_word] using hE
  have hGap : 2 ^ R.totalExponent + R.expandingGap = 3 ^ R.length := by
    unfold expandingGap
    omega
  have hEq := R.scaledEquation
  rw [R.nextValue_eq_startValue_add_valueGap] at hEq
  nlinarith [hGap]

/-- contracting枝のexact局所整数方程式。 -/
theorem contractingIdentity
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    R.affineConstant =
      R.contractingGap * R.startValue +
        2 ^ R.totalExponent * R.valueGap := by
  have hC' : 3 ^ R.length < 2 ^ R.totalExponent := by
    simpa [IsContracting, Word.Contracting, totalExponent, R.oddSteps_word] using hC
  have hGap : 3 ^ R.length + R.contractingGap = 2 ^ R.totalExponent := by
    unfold contractingGap
    omega
  have hEq := R.scaledEquation
  rw [R.nextValue_eq_startValue_add_valueGap] at hEq
  nlinarith [hGap]

/-- contracting adjacent word内にはfinite first crossingが存在する。 -/
theorem existsFirstCrossing
    {O : OddOrbit} (R : State O) (hC : R.IsContracting) :
    ∃ p : ℕ, p ≤ R.length ∧ Word.FirstCrossing (R.word.take p) := by
  have h := Word.exists_firstCrossing_of_contracting
    R.word_valid R.word_nonempty (by
      simpa [IsContracting] using hC)
  simpa [R.word_length] using h

end State

/-- expanding枝のcofinal tower。 -/
structure ExpandingTower (O : OddOrbit) where
  unbounded : O.Unbounded
  minima : O.FutureMinima
  standard : minima.IsStandard
  select : ℕ → ℕ
  select_strict : StrictMono select
  expanding : ∀ n, (State.mk unbounded minima standard (select n)).IsExpanding

namespace ExpandingTower

/-- tower第n項。 -/
def tower_at {O : OddOrbit} (T : ExpandingTower O) (n : ℕ) : State O :=
  ⟨T.unbounded, T.minima, T.standard, T.select n⟩

/-- 第n項はexpanding。 -/
theorem at_expanding {O : OddOrbit} (T : ExpandingTower O) (n : ℕ) :
    (T.tower_at n).IsExpanding := T.expanding n

/-- strict selectorは添字自身以上。 -/
theorem select_ge {O : OddOrbit} (T : ExpandingTower O) (n : ℕ) :
    n ≤ T.select n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hlt := T.select_strict (Nat.lt_succ_self n)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)

end ExpandingTower

/-- contracting枝のcofinal tower。 -/
structure ContractingTower (O : OddOrbit) where
  unbounded : O.Unbounded
  minima : O.FutureMinima
  standard : minima.IsStandard
  select : ℕ → ℕ
  select_strict : StrictMono select
  contracting : ∀ n, (State.mk unbounded minima standard (select n)).IsContracting

namespace ContractingTower

/-- tower第n項。 -/
def tower_at {O : OddOrbit} (T : ContractingTower O) (n : ℕ) : State O :=
  ⟨T.unbounded, T.minima, T.standard, T.select n⟩

/-- 第n項はcontracting。 -/
theorem at_contracting {O : OddOrbit} (T : ContractingTower O) (n : ℕ) :
    (T.tower_at n).IsContracting := T.contracting n

/-- strict selectorは添字自身以上。 -/
theorem select_ge {O : OddOrbit} (T : ContractingTower O) (n : ℕ) :
    n ≤ T.select n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have hlt := T.select_strict (Nat.lt_succ_self n)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hlt)

end ContractingTower

end AdjacentReturn
end Collatz
