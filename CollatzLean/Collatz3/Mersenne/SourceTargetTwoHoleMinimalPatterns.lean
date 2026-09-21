import CollatzLean.Collatz3.Mersenne.SmallHoleExact
import CollatzLean.Collatz3.Arithmetic.TwoThreeUnit
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.LinearCombination

/-!
# Collatz3 Mersenne: source/target two-hole six-unit 語彙

source-two と target-two の exact equation を、それぞれ六項の signed `{2,3}`-unit
`sum = 1` として読むための最小語彙を置く。

この層は index、term、full pattern、minimal certificate だけを定義し、
certificate の存在や non-full 排除は後段に分離する。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

/-! ## source-two -/

/-- source-two の六項 index。 -/
inductive SourceTwoUnitIndex
  | negThree
  | sourceTop
  | sourceHoleA
  | sourceHoleB
  | targetTop
  | targetBase
  deriving DecidableEq

instance : Fintype SourceTwoUnitIndex where
  elems :=
    { .negThree, .sourceTop, .sourceHoleA,
      .sourceHoleB, .targetTop, .targetBase }
  complete := by
    intro x
    cases x <;> simp

/-- source-two の `sum = 1` に現れる六項。 -/
def sourceTwoUnitTerm
    (k n r L a b : ℕ) :
    SourceTwoUnitIndex → SignedTwoThreeUnit
  | .negThree   => SignedTwoThreeUnit.negThree k
  | .sourceTop  => SignedTwoThreeUnit.pos n k
  | .sourceHoleA => SignedTwoThreeUnit.neg a k
  | .sourceHoleB => SignedTwoThreeUnit.neg b k
  | .targetTop  => SignedTwoThreeUnit.neg (r + L) 0
  | .targetBase => SignedTwoThreeUnit.pos r 0

/-- source-two index はちょうど6個。 -/
theorem sourceTwoUnitIndex_card :
    Fintype.card SourceTwoUnitIndex = 6 := by
  decide

private theorem sourceTwoUnitIndex_univ :
    (Finset.univ : Finset SourceTwoUnitIndex) =
      { .negThree, .sourceTop, .sourceHoleA,
        .sourceHoleB, .targetTop, .targetBase } := by
  ext i
  cases i <;> simp

/-- source-two exact equation は六項 `{2,3}`-unit equation `sum = 1` を与える。 -/
theorem SourceTwoHoleEquation.sixUnit_sum_eq_one
    {k n r L a b : ℕ}
    (hEq : SourceTwoHoleEquation k n r L a b) :
    Finset.sum (Finset.univ : Finset SourceTwoUnitIndex)
        (fun i => (sourceTwoUnitTerm k n r L a b i).value) = 1 := by
  rw [sourceTwoUnitIndex_univ]
  simp only [sourceTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_negThree, SignedTwoThreeUnit.value_pos,
    SignedTwoThreeUnit.value_neg, pow_zero, mul_one, Finset.sum_singleton]
  unfold SourceTwoHoleEquation at hEq
  rw [pow_add]
  linear_combination hEq

/-- source-two の genuinely full six-term pattern。 -/
def SourceTwoFullPattern
    (selected : Finset SourceTwoUnitIndex) : Prop :=
  selected = Finset.univ

/-- source-two minimal nondegenerate certificate。 -/
structure SourceTwoMinimalPatternCertificate
    (k n r L a b : ℕ)
    (selected : Finset SourceTwoUnitIndex) : Prop where
  nondegenerate :
    NondegenerateSumOne
      (fun i => (sourceTwoUnitTerm k n r L a b i).value)
      selected
  anchor_mem : SourceTwoUnitIndex.negThree ∈ selected

/-! ## target-two -/

/-- target-two の六項 index。 -/
inductive TargetTwoUnitIndex
  | negThree
  | sourceTop
  | targetTop
  | targetBase
  | targetHoleA
  | targetHoleB
  deriving DecidableEq

instance : Fintype TargetTwoUnitIndex where
  elems :=
    { .negThree, .sourceTop, .targetTop,
      .targetBase, .targetHoleA, .targetHoleB }
  complete := by
    intro x
    cases x <;> simp

/-- target-two の `sum = 1` に現れる六項。 -/
def targetTwoUnitTerm
    (k n r L a b : ℕ) :
    TargetTwoUnitIndex → SignedTwoThreeUnit
  | .negThree   => SignedTwoThreeUnit.negThree k
  | .sourceTop  => SignedTwoThreeUnit.pos n k
  | .targetTop  => SignedTwoThreeUnit.neg (r + L) 0
  | .targetBase => SignedTwoThreeUnit.pos r 0
  | .targetHoleA => SignedTwoThreeUnit.pos (r + a) 0
  | .targetHoleB => SignedTwoThreeUnit.pos (r + b) 0

/-- target-two index はちょうど6個。 -/
theorem targetTwoUnitIndex_card :
    Fintype.card TargetTwoUnitIndex = 6 := by
  decide

private theorem targetTwoUnitIndex_univ :
    (Finset.univ : Finset TargetTwoUnitIndex) =
      { .negThree, .sourceTop, .targetTop,
        .targetBase, .targetHoleA, .targetHoleB } := by
  ext i
  cases i <;> simp

/-- target-two exact equation は六項 `{2,3}`-unit equation `sum = 1` を与える。 -/
theorem TargetTwoHoleEquation.sixUnit_sum_eq_one
    {k n r L a b : ℕ}
    (hEq : TargetTwoHoleEquation k n r L a b) :
    Finset.sum (Finset.univ : Finset TargetTwoUnitIndex)
        (fun i => (targetTwoUnitTerm k n r L a b i).value) = 1 := by
  rw [targetTwoUnitIndex_univ]
  simp only [targetTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_negThree, SignedTwoThreeUnit.value_pos,
    SignedTwoThreeUnit.value_neg, pow_zero, mul_one, Finset.sum_singleton]
  unfold TargetTwoHoleEquation at hEq
  rw [pow_add, pow_add, pow_add]
  linear_combination hEq

/-- target-two の genuinely full six-term pattern。 -/
def TargetTwoFullPattern
    (selected : Finset TargetTwoUnitIndex) : Prop :=
  selected = Finset.univ

/-- target-two minimal nondegenerate certificate。 -/
structure TargetTwoMinimalPatternCertificate
    (k n r L a b : ℕ)
    (selected : Finset TargetTwoUnitIndex) : Prop where
  nondegenerate :
    NondegenerateSumOne
      (fun i => (targetTwoUnitTerm k n r L a b i).value)
      selected
  anchor_mem : TargetTwoUnitIndex.negThree ∈ selected

end Mersenne
end Collatz3
