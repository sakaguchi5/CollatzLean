import CollatzLean.Collatz3.Mersenne.SplitTwoHoleMinimalPatterns
import CollatzLean.Collatz3.Arithmetic.AnchoredVanishing
import Mathlib.Data.Finset.Sum

/-!
# Collatz3 Mersenne: split-two minimal certificate の存在

`SplitTwoHoleMinimalPatterns` では、split-two を六項の signed `{2,3}`-unit
`sum = 1` として固定し、certificate が得られた後の有限分類を証明した。

このファイルでは残っていた存在矢印を閉じる。

六項 `sum = 1` に定数 `-1` を一項だけ加えて zero-sum にし、`-3^k` を anchor として
既存の `AnchorMinimalVanishing` を適用する。source length、source hole、exit depth が正なら、
`-3^k` 以外の六項のうち `-1` を除く全項は偶数なので、anchor を含む消滅部分和には
必ず `-1` も含まれる。そこで左側の `Unit` 成分を除けば、split-two 六項上の
nondegenerate `sum = 1` certificate が得られる。

したがって well-formed split-two equation は、既存の

* known lower-hole pattern,
* full six-term pattern,
* proper residual (`card ≤ 5`)

の三分岐へ直接送れる。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

/-- `-1` を一つ加えた split-two zero-sum 用 index。 -/
abbrev SplitTwoAugmentedIndex := Unit ⊕ SplitTwoUnitIndex

/-- 左成分は定数 `-1`、右成分は既存の split-two 六項を表す。 -/
def splitTwoAugmentedTerm
    (k n r L a b : ℕ) :
    SplitTwoAugmentedIndex → SignedTwoThreeUnit
  | .inl _ => SignedTwoThreeUnit.negOne
  | .inr i => splitTwoUnitTerm k n r L a b i

/-- augmented zero-sum における定数 `-1` の index。 -/
def splitTwoAugmentedOne : SplitTwoAugmentedIndex := Sum.inl ()

/-- augmented zero-sum における `-3^k` anchor の index。 -/
def splitTwoAugmentedThree : SplitTwoAugmentedIndex :=
  Sum.inr SplitTwoUnitIndex.negThree

@[simp] theorem splitTwoAugmentedTerm_one
    (k n r L a b : ℕ) :
    splitTwoAugmentedTerm k n r L a b splitTwoAugmentedOne =
      SignedTwoThreeUnit.negOne := rfl

@[simp] theorem splitTwoAugmentedTerm_three
    (k n r L a b : ℕ) :
    splitTwoAugmentedTerm k n r L a b splitTwoAugmentedThree =
      SignedTwoThreeUnit.negThree k := rfl

@[simp] theorem splitTwoAugmentedOne_ne_three :
    splitTwoAugmentedOne ≠ splitTwoAugmentedThree := by
  simp [splitTwoAugmentedOne, splitTwoAugmentedThree]

/-- split-two の六項 `sum=1` に `-1` を足すと exact zero-sum になる。 -/
theorem SplitTwoHoleEquation.augmented_sum_zero
    {k n r L a b : ℕ}
    (hEq : SplitTwoHoleEquation k n r L a b) :
    Vanishes
      (fun i => (splitTwoAugmentedTerm k n r L a b i).value)
      (Finset.univ : Finset SplitTwoAugmentedIndex) := by
  have hSix := hEq.sixUnit_sum_eq_one
  unfold Vanishes
  rw [Fintype.sum_sum_type]
  simp only [splitTwoAugmentedTerm, SignedTwoThreeUnit.value_negOne]
  rw [hSix]
  norm_num

/--
parity anchor。

`n>0`, `a>0`, `r>0` のとき、`-3^k` を含む augmented zero-sum は
定数 `-1` も必ず含む。`-1` が無ければ `-3^k` 以外は全て even なので、
odd な `-3^k` が even sum に等しいことになり矛盾する。
-/
theorem splitTwo_augmented_vanishing_contains_one
    {k n r L a b : ℕ}
    (hn : 0 < n)
    (ha : 0 < a)
    (hr : 0 < r)
    {s : Finset SplitTwoAugmentedIndex}
    (hThree : splitTwoAugmentedThree ∈ s)
    (hZero :
      Vanishes
        (fun i => (splitTwoAugmentedTerm k n r L a b i).value)
        s) :
    splitTwoAugmentedOne ∈ s := by
  classical
  let term := splitTwoAugmentedTerm k n r L a b
  let three : SplitTwoAugmentedIndex := splitTwoAugmentedThree
  let one : SplitTwoAugmentedIndex := splitTwoAugmentedOne
  by_contra hOne
  have hEvenEach :
      ∀ i ∈ s.erase three,
        IntEven ((term i).value) := by
    intro i hi
    have hiData := Finset.mem_erase.mp hi
    have hiNeThree : i ≠ three := hiData.1
    have hiS : i ∈ s := hiData.2
    rcases i with u | i
    · have hu : u = () := Subsingleton.elim _ _
      subst u
      have hiEq : (Sum.inl () : SplitTwoAugmentedIndex) = one := rfl
      rw [hiEq] at hiS
      exact False.elim (hOne hiS)
    · cases i with
      | negThree =>
          have hiEq :
              (Sum.inr SplitTwoUnitIndex.negThree : SplitTwoAugmentedIndex) = three := rfl
          exact False.elim (hiNeThree hiEq)
      | sourceTop =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          simpa [term, splitTwoAugmentedTerm, splitTwoUnitTerm,
            SignedTwoThreeUnit.pos] using hn
      | sourceHole =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          simpa [term, splitTwoAugmentedTerm, splitTwoUnitTerm,
            SignedTwoThreeUnit.neg] using ha
      | targetTop =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          change 0 < r + L
          omega
      | targetBase =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          simpa [term, splitTwoAugmentedTerm, splitTwoUnitTerm,
            SignedTwoThreeUnit.pos] using hr
      | targetHole =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          change 0 < r + b
          omega
  have hEvenSum :
      IntEven
        (Finset.sum (s.erase three)
          (fun i => (term i).value)) :=
    IntEven.finset_sum _ _ hEvenEach
  rcases hEvenSum with ⟨q, hq⟩
  have hDecomp :
      Finset.sum (s.erase three)
          (fun i => (term i).value) +
        (term three).value = 0 := by
    rw [Finset.sum_erase_add s (fun i => (term i).value) hThree]
    exact hZero
  apply SignedTwoThreeUnit.negThree_not_even k
  refine ⟨-q, ?_⟩
  have hThreeValue : term three = SignedTwoThreeUnit.negThree k := by
    rfl
  rw [hq, hThreeValue] at hDecomp
  omega

/--
anchor-minimal augmented zero-sum から、右側の split-two 六項だけを取り出すと
nondegenerate `sum=1` になる。
-/
theorem splitTwo_certificate_of_anchorMinimal
    {k n r L a b : ℕ}
    {s : Finset SplitTwoAugmentedIndex}
    (hMin :
      AnchorMinimalVanishing
        (fun i => (splitTwoAugmentedTerm k n r L a b i).value)
        splitTwoAugmentedThree s)
    (hOne : splitTwoAugmentedOne ∈ s) :
    SplitTwoMinimalPatternCertificate
      k n r L a b s.toRight := by
  classical
  let term := splitTwoAugmentedTerm k n r L a b
  have hOne' : (Sum.inl () : SplitTwoAugmentedIndex) ∈ s := by
    simpa [splitTwoAugmentedOne] using hOne
  have hLeft : s.toLeft = ({()} : Finset Unit) := by
    ext u
    have hu : u = () := Subsingleton.elim _ _
    subst u
    constructor
    · intro _
      simp
    · intro _
      exact Finset.mem_toLeft.mpr hOne'
  constructor
  · constructor
    · have hDecomp :=
        Finset.sum_sum_eq_sum_toLeft_add_sum_toRight s
          (fun i => (term i).value)
      have hZero : Finset.sum s (fun i => (term i).value) = 0 := hMin.sum_eq_zero
      rw [hZero, hLeft] at hDecomp
      simp [term, splitTwoAugmentedTerm] at hDecomp
      omega
    · intro u huNonempty huSub hZeroU
      let u' : Finset SplitTwoAugmentedIndex :=
        u.map (.inr : SplitTwoUnitIndex ↪ SplitTwoAugmentedIndex)
      have hu'Sub : u' ⊆ s := by
        intro z hz
        rcases Finset.mem_map.mp hz with ⟨i, hi, rfl⟩
        have hiRight : i ∈ s.toRight := huSub hi
        change (Sum.inr i : SplitTwoAugmentedIndex) ∈ s
        exact Finset.mem_toRight.mp hiRight
      have hu'Nonempty : u'.Nonempty := by
        rcases huNonempty with ⟨i, hi⟩
        exact ⟨Sum.inr i, Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩
      have hu'Ne : u' ≠ s := by
        intro hEq
        have hOneU' : splitTwoAugmentedOne ∈ u' := by
          rw [hEq]
          exact hOne
        simp [u', splitTwoAugmentedOne] at hOneU'
      have hZeroU' :
          Vanishes (fun i => (term i).value) u' := by
        unfold Vanishes
        simpa [u', term, splitTwoAugmentedTerm] using hZeroU
      exact hMin.no_nonempty_proper_vanishing
        hu'Sub hu'Nonempty hu'Ne hZeroU'
  · have hThreeAug :
        (Sum.inr SplitTwoUnitIndex.negThree : SplitTwoAugmentedIndex) ∈ s := by
      simpa [splitTwoAugmentedThree] using hMin.anchor_mem
    have hThreeRight :
        SplitTwoUnitIndex.negThree ∈ s.toRight := by
      exact Finset.mem_toRight.mpr hThreeAug
    exact hThreeRight

/--
well-formed split-two の正値条件のうち、certificate 構成に本当に必要な
`n>0`, `a>0`, `r>0` だけを仮定した存在定理。
-/
theorem SplitTwoHoleEquation.exists_minimalPatternCertificate
    {k n r L a b : ℕ}
    (hEq : SplitTwoHoleEquation k n r L a b)
    (hn : 0 < n)
    (ha : 0 < a)
    (hr : 0 < r) :
    ∃ selected : Finset SplitTwoUnitIndex,
      SplitTwoMinimalPatternCertificate k n r L a b selected := by
  classical
  let term := splitTwoAugmentedTerm k n r L a b
  let three : SplitTwoAugmentedIndex := splitTwoAugmentedThree
  have hZero :
      Vanishes
        (fun i => (term i).value)
        (Finset.univ : Finset SplitTwoAugmentedIndex) := by
    simpa [term] using hEq.augmented_sum_zero
  rcases exists_anchorMinimalVanishing
      (v := fun i => (term i).value)
      three
      (s₀ := (Finset.univ : Finset SplitTwoAugmentedIndex))
      (by simp [three, splitTwoAugmentedThree])
      hZero with
    ⟨s, hsUniv, hMin⟩
  have hOne : splitTwoAugmentedOne ∈ s := by
    apply splitTwo_augmented_vanishing_contains_one
      (k := k) (n := n) (r := r) (L := L) (a := a) (b := b)
      hn ha hr hMin.anchor_mem
    exact hMin.sum_eq_zero
  exact ⟨s.toRight, splitTwo_certificate_of_anchorMinimal hMin hOne⟩

/--
通常の split-two normal form が持つ `0<a<n`, `r>0` から certificate を得る便利形。
-/
theorem SplitTwoHoleEquation.exists_minimalPatternCertificate_of_wellFormed
    {k n r L a b : ℕ}
    (hEq : SplitTwoHoleEquation k n r L a b)
    (ha0 : 0 < a)
    (han : a < n)
    (hr : 0 < r) :
    ∃ selected : Finset SplitTwoUnitIndex,
      SplitTwoMinimalPatternCertificate k n r L a b selected := by
  exact hEq.exists_minimalPatternCertificate (by omega) ha0 hr

/--
split-two equation から、certificate と三分岐 classification を同時に回収する。
これで `equation → certificate → pattern classification` の missing arrow は閉じる。
-/
theorem SplitTwoHoleEquation.exists_classifiedMinimalPattern
    {k n r L a b : ℕ}
    (hEq : SplitTwoHoleEquation k n r L a b)
    (hn : 0 < n)
    (ha : 0 < a)
    (hr : 0 < r) :
    ∃ selected : Finset SplitTwoUnitIndex,
      SplitTwoMinimalPatternCertificate k n r L a b selected ∧
      (SplitTwoKnownLowerPattern selected ∨
        SplitTwoFullPattern selected ∨
          SplitTwoProperResidualPattern selected) := by
  rcases hEq.exists_minimalPatternCertificate hn ha hr with ⟨selected, hCert⟩
  exact ⟨selected, hCert, splitTwoPattern_classification selected⟩

/-- known lower-hole branch なら、実際の no-hole/source-one/target-one equation のいずれかへ戻る。 -/
theorem SplitTwoMinimalPatternCertificate.knownLower_reduces
    {k n r L a b : ℕ}
    {selected : Finset SplitTwoUnitIndex}
    (h : SplitTwoMinimalPatternCertificate k n r L a b selected)
    (hKnown : SplitTwoKnownLowerPattern selected) :
    NoHoleEquation k n r L ∨
      SourceOneHoleEquation k n r L a ∨
        TargetOneHoleEquation k n r L b := by
  rcases hKnown with hNo | hRest
  · exact Or.inl (h.to_noHole hNo)
  · rcases hRest with hSource | hTarget
    · exact Or.inr (Or.inl (h.to_sourceOne hSource))
    · exact Or.inr (Or.inr (h.to_targetOne hTarget))

end Mersenne
end Collatz3
