import CollatzLean.Collatz3.Mersenne.SmallHoleExact
import CollatzLean.Collatz3.Arithmetic.TwoThreeUnit
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: split-two minimal S-unit patterns

split-two equation

`3^k(2^n-1-2^a) = 2^r(2^L-1-2^b)+1`

を展開すると、右辺 1 に正規化した六つの signed `{2,3}`-unit

* `-3^k`
* `+2^n 3^k`
* `-2^a 3^k`
* `-2^(r+L)`
* `+2^r`
* `+2^(r+b)`

が得られる。

このファイルでは deep S-unit theorem を仮定しない。
六項の index と、既知 lower-hole pattern / full six-term / proper residual の
有限分類だけを内部語彙として固定する。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

/-- split-two の `sum = 1` 側に現れる六項。 -/
inductive SplitTwoUnitIndex
  | negThree
  | sourceTop
  | sourceHole
  | targetTop
  | targetBase
  | targetHole
  deriving DecidableEq

instance : Fintype SplitTwoUnitIndex where
  elems :=
    { .negThree,
      .sourceTop,
      .sourceHole,
      .targetTop,
      .targetBase,
      .targetHole }
  complete := by
    intro x
    cases x <;> simp

/-- 六 index を実際の signed `{2,3}`-unit に読む。 -/
def splitTwoUnitTerm
    (k n r L a b : ℕ) :
    SplitTwoUnitIndex → SignedTwoThreeUnit
  | .negThree   => SignedTwoThreeUnit.negThree k
  | .sourceTop  => SignedTwoThreeUnit.pos n k
  | .sourceHole => SignedTwoThreeUnit.neg a k
  | .targetTop  => SignedTwoThreeUnit.neg (r + L) 0
  | .targetBase => SignedTwoThreeUnit.pos r 0
  | .targetHole => SignedTwoThreeUnit.pos (r + b) 0

/-- index はちょうど6個。 -/
theorem splitTwoUnitIndex_card :
    Fintype.card SplitTwoUnitIndex = 6 := by
  decide

private theorem splitTwoUnitIndex_univ :
    (Finset.univ : Finset SplitTwoUnitIndex) =
      { .negThree, .sourceTop, .sourceHole,
        .targetTop, .targetBase, .targetHole } := by
  ext i
  cases i <;> simp

/-- split-two exact equation は六項 `{2,3}`-unit equation `sum = 1` を与える。 -/
theorem SplitTwoHoleEquation.sixUnit_sum_eq_one
    {k n r L a b : ℕ}
    (hEq : SplitTwoHoleEquation k n r L a b) :
    Finset.sum (Finset.univ : Finset SplitTwoUnitIndex)
        (fun i => (splitTwoUnitTerm k n r L a b i).value) = 1 := by
  rw [splitTwoUnitIndex_univ]
  simp only [splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq, Finset.mem_singleton,
    or_self, not_false_eq_true,
    Finset.sum_insert, SignedTwoThreeUnit.value_negThree, SignedTwoThreeUnit.value_pos,
    SignedTwoThreeUnit.value_neg,pow_zero, mul_one, Finset.sum_singleton]
  unfold SplitTwoHoleEquation at hEq
  rw [pow_add, pow_add]
  linear_combination hEq

/-- no-hole に対応する4項 pattern。 -/
def splitTwoNoHolePattern : Finset SplitTwoUnitIndex :=
  { .negThree, .sourceTop, .targetTop, .targetBase }

/-- source-one に対応する5項 pattern。 -/
def splitTwoSourceOnePattern : Finset SplitTwoUnitIndex :=
  { .negThree, .sourceTop, .sourceHole, .targetTop, .targetBase }

/-- target-one に対応する5項 pattern。 -/
def splitTwoTargetOnePattern : Finset SplitTwoUnitIndex :=
  { .negThree, .sourceTop, .targetTop, .targetBase, .targetHole }

/-- 既に閉じた lower-hole equation に一致する exact pattern。 -/
def SplitTwoKnownLowerPattern
    (selected : Finset SplitTwoUnitIndex) : Prop :=
  selected = splitTwoNoHolePattern ∨
    selected = splitTwoSourceOnePattern ∨
      selected = splitTwoTargetOnePattern

/-- 六項すべてを保持する genuinely new full split pattern。 -/
def SplitTwoFullPattern
    (selected : Finset SplitTwoUnitIndex) : Prop :=
  selected = Finset.univ

/-- full six-term でない proper residual。六項 universe なので自動的に card≤5。 -/
def SplitTwoProperResidualPattern
    (selected : Finset SplitTwoUnitIndex) : Prop :=
  selected.card ≤ 5 ∧
    ¬ SplitTwoKnownLowerPattern selected

/--
ESS/Baker 側へ渡す minimal pattern certificate の薄い型。
存在証明は exact sparse equation 側の minimal-vanishing machinery と接続して後段で行う。
-/
structure SplitTwoMinimalPatternCertificate
    (k n r L a b : ℕ)
    (selected : Finset SplitTwoUnitIndex) : Prop where
  nondegenerate :
    NondegenerateSumOne
      (fun i => (splitTwoUnitTerm k n r L a b i).value)
      selected
  anchor_mem : SplitTwoUnitIndex.negThree ∈ selected

/-- 任意の six-index subset は full か card≤5。 -/
theorem splitTwoPattern_full_or_card_le_five
    (selected : Finset SplitTwoUnitIndex) :
    SplitTwoFullPattern selected ∨ selected.card ≤ 5 := by
  by_cases hFull : selected = Finset.univ
  · exact Or.inl hFull
  · right
    have hProper : selected ⊂ (Finset.univ : Finset SplitTwoUnitIndex) := by
      exact Finset.ssubset_iff_subset_ne.mpr ⟨by simp, hFull⟩
    have hCardLt := Finset.card_lt_card hProper
    have hUnivCard :
        (Finset.univ : Finset SplitTwoUnitIndex).card = 6 := by
      simp [splitTwoUnitIndex_card]
    rw [hUnivCard] at hCardLt
    omega

/--
pattern classification の最終形。

* known lower-hole pattern
* genuinely new full six-term pattern
* unknown だが card≤5 の proper residual

の三択に必ず入る。
-/
theorem splitTwoPattern_classification
    (selected : Finset SplitTwoUnitIndex) :
    SplitTwoKnownLowerPattern selected ∨
      SplitTwoFullPattern selected ∨
        SplitTwoProperResidualPattern selected := by
  by_cases hKnown : SplitTwoKnownLowerPattern selected
  · exact Or.inl hKnown
  · rcases splitTwoPattern_full_or_card_le_five selected with hFull | hSmall
    · exact Or.inr (Or.inl hFull)
    · exact Or.inr (Or.inr ⟨hSmall, hKnown⟩)

/-- no-hole pattern の nondegenerate certificate は実際の no-hole equation を与える。 -/
theorem SplitTwoMinimalPatternCertificate.to_noHole
    {k n r L a b : ℕ}
    {selected : Finset SplitTwoUnitIndex}
    (h : SplitTwoMinimalPatternCertificate k n r L a b selected)
    (hs : selected = splitTwoNoHolePattern) :
    NoHoleEquation k n r L := by
  have hSum := h.nondegenerate.sum_eq_one
  rw [hs] at hSum
  simp only [splitTwoNoHolePattern, splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self,
    not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
     SignedTwoThreeUnit.value_pos,
    SignedTwoThreeUnit.value_neg, pow_zero, mul_one, Finset.sum_singleton] at hSum
  unfold NoHoleEquation
  rw [pow_add] at hSum
  linear_combination hSum

/-- source-one pattern は source-one equation へ戻る。 -/
theorem SplitTwoMinimalPatternCertificate.to_sourceOne
    {k n r L a b : ℕ}
    {selected : Finset SplitTwoUnitIndex}
    (h : SplitTwoMinimalPatternCertificate k n r L a b selected)
    (hs : selected = splitTwoSourceOnePattern) :
    SourceOneHoleEquation k n r L a := by
  have hSum := h.nondegenerate.sum_eq_one
  rw [hs] at hSum
  simp only [splitTwoSourceOnePattern, splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
   Finset.mem_singleton,
    or_self, not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
    SignedTwoThreeUnit.value_pos,
    SignedTwoThreeUnit.value_neg, pow_zero, mul_one, Finset.sum_singleton] at hSum
  unfold SourceOneHoleEquation
  rw [pow_add] at hSum
  linear_combination hSum

/-- target-one pattern は target-one equation へ戻る。 -/
theorem SplitTwoMinimalPatternCertificate.to_targetOne
    {k n r L a b : ℕ}
    {selected : Finset SplitTwoUnitIndex}
    (h : SplitTwoMinimalPatternCertificate k n r L a b selected)
    (hs : selected = splitTwoTargetOnePattern) :
    TargetOneHoleEquation k n r L b := by
  have hSum := h.nondegenerate.sum_eq_one
  rw [hs] at hSum
  simp only [splitTwoTargetOnePattern, splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton,
    or_self, not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
     SignedTwoThreeUnit.value_pos,
    SignedTwoThreeUnit.value_neg, pow_zero, mul_one, Finset.sum_singleton] at hSum
  unfold TargetOneHoleEquation
  rw [pow_add] at hSum
  linear_combination hSum

end Mersenne
end Collatz3
