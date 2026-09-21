import CollatzLean.Collatz3.Mersenne.SourceTargetTwoHoleMinimalPatterns
import CollatzLean.Collatz3.Arithmetic.AnchoredVanishing
import Mathlib.Data.Finset.Sum

/-!
# Collatz3 Mersenne: source/target two-hole minimal certificate の存在

source-two / target-two の六項 `sum=1` に定数 `-1` を加え、`-3^k` を anchor とする
極小 zero-sum を取る。parity によりその極小和は必ず `-1` を含むため、
`-1` を外すと六項 index 上の nondegenerate `sum=1` certificate が得られる。

定義は前段に置き、このファイルでは存在矢印だけを閉じる。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

/-! ## source-two certificate -/

abbrev SourceTwoAugmentedIndex := Unit ⊕ SourceTwoUnitIndex

def sourceTwoAugmentedTerm
    (k n r L a b : ℕ) :
    SourceTwoAugmentedIndex → SignedTwoThreeUnit
  | .inl _ => SignedTwoThreeUnit.negOne
  | .inr i => sourceTwoUnitTerm k n r L a b i

def sourceTwoAugmentedOne : SourceTwoAugmentedIndex := Sum.inl ()

def sourceTwoAugmentedThree : SourceTwoAugmentedIndex :=
  Sum.inr SourceTwoUnitIndex.negThree

@[simp] theorem sourceTwoAugmentedTerm_one
    (k n r L a b : ℕ) :
    sourceTwoAugmentedTerm k n r L a b sourceTwoAugmentedOne =
      SignedTwoThreeUnit.negOne := rfl

@[simp] theorem sourceTwoAugmentedTerm_three
    (k n r L a b : ℕ) :
    sourceTwoAugmentedTerm k n r L a b sourceTwoAugmentedThree =
      SignedTwoThreeUnit.negThree k := rfl

/-- source-two の六項 `sum=1` に `-1` を加えると zero-sum。 -/
theorem SourceTwoHoleEquation.augmented_sum_zero
    {k n r L a b : ℕ}
    (hEq : SourceTwoHoleEquation k n r L a b) :
    Vanishes
      (fun i => (sourceTwoAugmentedTerm k n r L a b i).value)
      (Finset.univ : Finset SourceTwoAugmentedIndex) := by
  have hSix := hEq.sixUnit_sum_eq_one
  unfold Vanishes
  rw [Fintype.sum_sum_type]
  simp only [sourceTwoAugmentedTerm, SignedTwoThreeUnit.value_negOne]
  rw [hSix]
  norm_num

/-- source-two augmented zero-sum で `-3^k` を含めば、parity により `-1` も含む。 -/
theorem sourceTwo_augmented_vanishing_contains_one
    {k n r L a b : ℕ}
    (hn : 0 < n)
    (ha : 0 < a)
    (hb : 0 < b)
    (hr : 0 < r)
    {s : Finset SourceTwoAugmentedIndex}
    (hThree : sourceTwoAugmentedThree ∈ s)
    (hZero :
      Vanishes
        (fun i => (sourceTwoAugmentedTerm k n r L a b i).value)
        s) :
    sourceTwoAugmentedOne ∈ s := by
  classical
  let term := sourceTwoAugmentedTerm k n r L a b
  let three : SourceTwoAugmentedIndex := sourceTwoAugmentedThree
  let one : SourceTwoAugmentedIndex := sourceTwoAugmentedOne
  by_contra hOne
  have hEvenEach :
      ∀ i ∈ s.erase three, IntEven ((term i).value) := by
    intro i hi
    have hiData := Finset.mem_erase.mp hi
    have hiNeThree : i ≠ three := hiData.1
    have hiS : i ∈ s := hiData.2
    rcases i with u | i
    · have hu : u = () := Subsingleton.elim _ _
      subst u
      have hiEq : (Sum.inl () : SourceTwoAugmentedIndex) = one := rfl
      rw [hiEq] at hiS
      exact False.elim (hOne hiS)
    · cases i with
      | negThree =>
          have hiEq :
              (Sum.inr SourceTwoUnitIndex.negThree : SourceTwoAugmentedIndex) = three := rfl
          exact False.elim (hiNeThree hiEq)
      | sourceTop =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          simpa [term, sourceTwoAugmentedTerm, sourceTwoUnitTerm,
            SignedTwoThreeUnit.pos] using hn
      | sourceHoleA =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          simpa [term, sourceTwoAugmentedTerm, sourceTwoUnitTerm,
            SignedTwoThreeUnit.neg] using ha
      | sourceHoleB =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          simpa [term, sourceTwoAugmentedTerm, sourceTwoUnitTerm,
            SignedTwoThreeUnit.neg] using hb
      | targetTop =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          change 0 < r + L
          omega
      | targetBase =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          simpa [term, sourceTwoAugmentedTerm, sourceTwoUnitTerm,
            SignedTwoThreeUnit.pos] using hr
  have hEvenSum :
      IntEven (Finset.sum (s.erase three) (fun i => (term i).value)) :=
    IntEven.finset_sum _ _ hEvenEach
  rcases hEvenSum with ⟨q, hq⟩
  have hDecomp :
      Finset.sum (s.erase three) (fun i => (term i).value) +
        (term three).value = 0 := by
    rw [Finset.sum_erase_add s (fun i => (term i).value) hThree]
    exact hZero
  apply SignedTwoThreeUnit.negThree_not_even k
  refine ⟨-q, ?_⟩
  have hThreeValue : term three = SignedTwoThreeUnit.negThree k := by rfl
  rw [hq, hThreeValue] at hDecomp
  omega

/-- anchor-minimal source-two zero-sum から六項 certificate を取り出す。 -/
theorem sourceTwo_certificate_of_anchorMinimal
    {k n r L a b : ℕ}
    {s : Finset SourceTwoAugmentedIndex}
    (hMin :
      AnchorMinimalVanishing
        (fun i => (sourceTwoAugmentedTerm k n r L a b i).value)
        sourceTwoAugmentedThree s)
    (hOne : sourceTwoAugmentedOne ∈ s) :
    SourceTwoMinimalPatternCertificate k n r L a b s.toRight := by
  classical
  let term := sourceTwoAugmentedTerm k n r L a b
  have hOne' : (Sum.inl () : SourceTwoAugmentedIndex) ∈ s := by
    simpa [sourceTwoAugmentedOne] using hOne
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
      simp [term, sourceTwoAugmentedTerm] at hDecomp
      omega
    · intro u huNonempty huSub hZeroU
      let u' : Finset SourceTwoAugmentedIndex :=
        u.map (.inr : SourceTwoUnitIndex ↪ SourceTwoAugmentedIndex)
      have hu'Sub : u' ⊆ s := by
        intro z hz
        rcases Finset.mem_map.mp hz with ⟨i, hi, rfl⟩
        have hiRight : i ∈ s.toRight := huSub hi
        change (Sum.inr i : SourceTwoAugmentedIndex) ∈ s
        exact Finset.mem_toRight.mp hiRight
      have hu'Nonempty : u'.Nonempty := by
        rcases huNonempty with ⟨i, hi⟩
        exact ⟨Sum.inr i, Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩
      have hu'Ne : u' ≠ s := by
        intro hEq
        have hOneU' : sourceTwoAugmentedOne ∈ u' := by
          rw [hEq]
          exact hOne
        simp [u', sourceTwoAugmentedOne] at hOneU'
      have hZeroU' : Vanishes (fun i => (term i).value) u' := by
        unfold Vanishes
        simpa [u', term, sourceTwoAugmentedTerm] using hZeroU
      exact hMin.no_nonempty_proper_vanishing hu'Sub hu'Nonempty hu'Ne hZeroU'
  · have hThreeAug :
        (Sum.inr SourceTwoUnitIndex.negThree : SourceTwoAugmentedIndex) ∈ s := by
      simpa [sourceTwoAugmentedThree] using hMin.anchor_mem
    exact Finset.mem_toRight.mpr hThreeAug

/-- well-formed source-two equation は minimal certificate を持つ。 -/
theorem SourceTwoHoleEquation.exists_minimalPatternCertificate
    {k n r L a b : ℕ}
    (hEq : SourceTwoHoleEquation k n r L a b)
    (hn : 0 < n)
    (ha : 0 < a)
    (hb : 0 < b)
    (hr : 0 < r) :
    ∃ selected : Finset SourceTwoUnitIndex,
      SourceTwoMinimalPatternCertificate k n r L a b selected := by
  classical
  let term := sourceTwoAugmentedTerm k n r L a b
  let three : SourceTwoAugmentedIndex := sourceTwoAugmentedThree
  have hZero :
      Vanishes (fun i => (term i).value)
        (Finset.univ : Finset SourceTwoAugmentedIndex) := by
    simpa [term] using hEq.augmented_sum_zero
  rcases exists_anchorMinimalVanishing
      (v := fun i => (term i).value)
      three
      (s₀ := (Finset.univ : Finset SourceTwoAugmentedIndex))
      (by simp [three, sourceTwoAugmentedThree])
      hZero with
    ⟨s, _hsUniv, hMin⟩
  have hOne : sourceTwoAugmentedOne ∈ s := by
    apply sourceTwo_augmented_vanishing_contains_one
      (k := k) (n := n) (r := r) (L := L) (a := a) (b := b)
      hn ha hb hr hMin.anchor_mem
    exact hMin.sum_eq_zero
  exact ⟨s.toRight, sourceTwo_certificate_of_anchorMinimal hMin hOne⟩

/-! ## target-two certificate -/

abbrev TargetTwoAugmentedIndex := Unit ⊕ TargetTwoUnitIndex

def targetTwoAugmentedTerm
    (k n r L a b : ℕ) :
    TargetTwoAugmentedIndex → SignedTwoThreeUnit
  | .inl _ => SignedTwoThreeUnit.negOne
  | .inr i => targetTwoUnitTerm k n r L a b i

def targetTwoAugmentedOne : TargetTwoAugmentedIndex := Sum.inl ()

def targetTwoAugmentedThree : TargetTwoAugmentedIndex :=
  Sum.inr TargetTwoUnitIndex.negThree

@[simp] theorem targetTwoAugmentedTerm_one
    (k n r L a b : ℕ) :
    targetTwoAugmentedTerm k n r L a b targetTwoAugmentedOne =
      SignedTwoThreeUnit.negOne := rfl

@[simp] theorem targetTwoAugmentedTerm_three
    (k n r L a b : ℕ) :
    targetTwoAugmentedTerm k n r L a b targetTwoAugmentedThree =
      SignedTwoThreeUnit.negThree k := rfl

/-- target-two の六項 `sum=1` に `-1` を加えると zero-sum。 -/
theorem TargetTwoHoleEquation.augmented_sum_zero
    {k n r L a b : ℕ}
    (hEq : TargetTwoHoleEquation k n r L a b) :
    Vanishes
      (fun i => (targetTwoAugmentedTerm k n r L a b i).value)
      (Finset.univ : Finset TargetTwoAugmentedIndex) := by
  have hSix := hEq.sixUnit_sum_eq_one
  unfold Vanishes
  rw [Fintype.sum_sum_type]
  simp only [targetTwoAugmentedTerm, SignedTwoThreeUnit.value_negOne]
  rw [hSix]
  norm_num

/-- target-two augmented zero-sum で `-3^k` を含めば `-1` も含む。 -/
theorem targetTwo_augmented_vanishing_contains_one
    {k n r L a b : ℕ}
    (hn : 0 < n)
    (hr : 0 < r)
    {s : Finset TargetTwoAugmentedIndex}
    (hThree : targetTwoAugmentedThree ∈ s)
    (hZero :
      Vanishes
        (fun i => (targetTwoAugmentedTerm k n r L a b i).value)
        s) :
    targetTwoAugmentedOne ∈ s := by
  classical
  let term := targetTwoAugmentedTerm k n r L a b
  let three : TargetTwoAugmentedIndex := targetTwoAugmentedThree
  let one : TargetTwoAugmentedIndex := targetTwoAugmentedOne
  by_contra hOne
  have hEvenEach :
      ∀ i ∈ s.erase three, IntEven ((term i).value) := by
    intro i hi
    have hiData := Finset.mem_erase.mp hi
    have hiNeThree : i ≠ three := hiData.1
    have hiS : i ∈ s := hiData.2
    rcases i with u | i
    · have hu : u = () := Subsingleton.elim _ _
      subst u
      have hiEq : (Sum.inl () : TargetTwoAugmentedIndex) = one := rfl
      rw [hiEq] at hiS
      exact False.elim (hOne hiS)
    · cases i with
      | negThree =>
          have hiEq :
              (Sum.inr TargetTwoUnitIndex.negThree : TargetTwoAugmentedIndex) = three := rfl
          exact False.elim (hiNeThree hiEq)
      | sourceTop =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          simpa [term, targetTwoAugmentedTerm, targetTwoUnitTerm,
            SignedTwoThreeUnit.pos] using hn
      | targetTop =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          change 0 < r + L
          omega
      | targetBase =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          simpa [term, targetTwoAugmentedTerm, targetTwoUnitTerm,
            SignedTwoThreeUnit.pos] using hr
      | targetHoleA =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          change 0 < r + a
          omega
      | targetHoleB =>
          apply SignedTwoThreeUnit.value_even_of_twoExp_pos
          change 0 < r + b
          omega
  have hEvenSum :
      IntEven (Finset.sum (s.erase three) (fun i => (term i).value)) :=
    IntEven.finset_sum _ _ hEvenEach
  rcases hEvenSum with ⟨q, hq⟩
  have hDecomp :
      Finset.sum (s.erase three) (fun i => (term i).value) +
        (term three).value = 0 := by
    rw [Finset.sum_erase_add s (fun i => (term i).value) hThree]
    exact hZero
  apply SignedTwoThreeUnit.negThree_not_even k
  refine ⟨-q, ?_⟩
  have hThreeValue : term three = SignedTwoThreeUnit.negThree k := by rfl
  rw [hq, hThreeValue] at hDecomp
  omega

/-- anchor-minimal target-two zero-sum から六項 certificate を取り出す。 -/
theorem targetTwo_certificate_of_anchorMinimal
    {k n r L a b : ℕ}
    {s : Finset TargetTwoAugmentedIndex}
    (hMin :
      AnchorMinimalVanishing
        (fun i => (targetTwoAugmentedTerm k n r L a b i).value)
        targetTwoAugmentedThree s)
    (hOne : targetTwoAugmentedOne ∈ s) :
    TargetTwoMinimalPatternCertificate k n r L a b s.toRight := by
  classical
  let term := targetTwoAugmentedTerm k n r L a b
  have hOne' : (Sum.inl () : TargetTwoAugmentedIndex) ∈ s := by
    simpa [targetTwoAugmentedOne] using hOne
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
      simp [term, targetTwoAugmentedTerm] at hDecomp
      omega
    · intro u huNonempty huSub hZeroU
      let u' : Finset TargetTwoAugmentedIndex :=
        u.map (.inr : TargetTwoUnitIndex ↪ TargetTwoAugmentedIndex)
      have hu'Sub : u' ⊆ s := by
        intro z hz
        rcases Finset.mem_map.mp hz with ⟨i, hi, rfl⟩
        have hiRight : i ∈ s.toRight := huSub hi
        change (Sum.inr i : TargetTwoAugmentedIndex) ∈ s
        exact Finset.mem_toRight.mp hiRight
      have hu'Nonempty : u'.Nonempty := by
        rcases huNonempty with ⟨i, hi⟩
        exact ⟨Sum.inr i, Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩
      have hu'Ne : u' ≠ s := by
        intro hEq
        have hOneU' : targetTwoAugmentedOne ∈ u' := by
          rw [hEq]
          exact hOne
        simp [u', targetTwoAugmentedOne] at hOneU'
      have hZeroU' : Vanishes (fun i => (term i).value) u' := by
        unfold Vanishes
        simpa [u', term, targetTwoAugmentedTerm] using hZeroU
      exact hMin.no_nonempty_proper_vanishing hu'Sub hu'Nonempty hu'Ne hZeroU'
  · have hThreeAug :
        (Sum.inr TargetTwoUnitIndex.negThree : TargetTwoAugmentedIndex) ∈ s := by
      simpa [targetTwoAugmentedThree] using hMin.anchor_mem
    exact Finset.mem_toRight.mpr hThreeAug

/-- well-formed target-two equation は minimal certificate を持つ。 -/
theorem TargetTwoHoleEquation.exists_minimalPatternCertificate
    {k n r L a b : ℕ}
    (hEq : TargetTwoHoleEquation k n r L a b)
    (hn : 0 < n)
    (hr : 0 < r) :
    ∃ selected : Finset TargetTwoUnitIndex,
      TargetTwoMinimalPatternCertificate k n r L a b selected := by
  classical
  let term := targetTwoAugmentedTerm k n r L a b
  let three : TargetTwoAugmentedIndex := targetTwoAugmentedThree
  have hZero :
      Vanishes (fun i => (term i).value)
        (Finset.univ : Finset TargetTwoAugmentedIndex) := by
    simpa [term] using hEq.augmented_sum_zero
  rcases exists_anchorMinimalVanishing
      (v := fun i => (term i).value)
      three
      (s₀ := (Finset.univ : Finset TargetTwoAugmentedIndex))
      (by simp [three, targetTwoAugmentedThree])
      hZero with
    ⟨s, _hsUniv, hMin⟩
  have hOne : targetTwoAugmentedOne ∈ s := by
    apply targetTwo_augmented_vanishing_contains_one
      (k := k) (n := n) (r := r) (L := L) (a := a) (b := b)
      hn hr hMin.anchor_mem
    exact hMin.sum_eq_zero
  exact ⟨s.toRight, targetTwo_certificate_of_anchorMinimal hMin hOne⟩

end Mersenne
end Collatz3
