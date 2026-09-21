import CollatzLean.Collatz3.Mersenne.SourceTargetTwoHoleMinimalCertificate
import CollatzLean.Collatz3.Mersenne.TwoHoleUnitArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: source/target two-hole non-full certificate の内部排除

source-two と target-two の minimal certificate が full six-term でないとき、
選ばれなかった補集合は exact zero-sum になる。

* source-two は符号・大小関係で11型へ縮約し、唯一残る型から `k=1`。
* target-two は負項が `targetTop` 一つだけなので8型へ縮約し、すべて `k=1` または矛盾。

従って両配置とも `k≥3` では full six-term certificate だけが残る。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic
open TwoHoleUnitArithmetic

/-! ## 共通 Finset helper -/

private theorem selected_eq_univ_sdiff_of_univ_sdiff_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {selected omitted : Finset ι}
    (h : (Finset.univ : Finset ι) \ selected = omitted) :
    selected = (Finset.univ : Finset ι) \ omitted := by
  ext i
  have hi :
      (i ∈ (Finset.univ : Finset ι) \ selected) ↔ i ∈ omitted := by
    rw [h]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi ⊢
  constructor
  · intro hSel hOmit
    exact (hi.mpr hOmit) hSel
  · intro hOmit
    by_contra hSel
    exact hOmit (hi.mp hSel)

/-! ## source-two -/

private theorem sourceTwo_complement_sum_zero
    {k n r L a b : ℕ}
    {selected : Finset SourceTwoUnitIndex}
    (hEq : SourceTwoHoleEquation k n r L a b)
    (hCert : SourceTwoMinimalPatternCertificate k n r L a b selected) :
    Finset.sum ((Finset.univ : Finset SourceTwoUnitIndex) \ selected)
        (fun i => (sourceTwoUnitTerm k n r L a b i).value) = 0 := by
  have hAll := hEq.sixUnit_sum_eq_one
  have hSelected := hCert.nondegenerate.sum_eq_one
  have hSub : selected ⊆ (Finset.univ : Finset SourceTwoUnitIndex) := by
    intro i hi
    simp
  rw [← Finset.sum_sdiff hSub] at hAll
  rw [hSelected] at hAll
  omega

private theorem sourceTwo_complement_nonempty
    {selected : Finset SourceTwoUnitIndex}
    (hNotFull : selected ≠ (Finset.univ : Finset SourceTwoUnitIndex)) :
    ((Finset.univ : Finset SourceTwoUnitIndex) \ selected).Nonempty := by
  by_contra hNot
  have hEmpty :
      (Finset.univ : Finset SourceTwoUnitIndex) \ selected = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hNot
  apply hNotFull
  ext i
  constructor
  · intro _
    simp
  · intro _
    by_contra hi
    have hiDiff : i ∈ (Finset.univ : Finset SourceTwoUnitIndex) \ selected := by
      simp [hi]
    rw [hEmpty] at hiDiff
    simp at hiDiff

/-- `2^a+2^b < 2^n` for `a<b<n`。 -/
private theorem sourceTwo_holes_lt_top
    {a b n : ℕ}
    (hab : a < b)
    (hbn : b < n) :
    (2 : ℤ) ^ a + (2 : ℤ) ^ b < (2 : ℤ) ^ n := by
  have hAlt : 2 ^ a < 2 ^ b :=
    Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) hab
  have hAB : 2 ^ a + 2 ^ b < 2 ^ (b + 1) := by
    rw [pow_succ]
    omega
  have hBN : b + 1 ≤ n := by omega
  have hTop : 2 ^ (b + 1) ≤ 2 ^ n :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hBN
  have hNat : 2 ^ a + 2 ^ b < 2 ^ n := lt_of_lt_of_le hAB hTop
  exact_mod_cast hNat

private theorem sourceTwo_sourceTop_without_targetTop_cases :
    ∀ u : Finset SourceTwoUnitIndex,
      SourceTwoUnitIndex.negThree ∉ u →
      SourceTwoUnitIndex.sourceTop ∈ u →
      SourceTwoUnitIndex.targetTop ∉ u →
      u = { .sourceTop } ∨
      u = { .sourceTop, .sourceHoleA } ∨
      u = { .sourceTop, .sourceHoleB } ∨
      u = { .sourceTop, .targetBase } ∨
      u = { .sourceTop, .sourceHoleA, .sourceHoleB } ∨
      u = { .sourceTop, .sourceHoleA, .targetBase } ∨
      u = { .sourceTop, .sourceHoleB, .targetBase } ∨
      u = { .sourceTop, .sourceHoleA, .sourceHoleB, .targetBase } := by
  native_decide

private theorem sourceTwo_targetTop_without_sourceTop_cases :
    ∀ u : Finset SourceTwoUnitIndex,
      SourceTwoUnitIndex.negThree ∉ u →
      SourceTwoUnitIndex.sourceTop ∉ u →
      SourceTwoUnitIndex.targetTop ∈ u →
      u = { .targetTop } ∨
      u = { .sourceHoleA, .targetTop } ∨
      u = { .sourceHoleB, .targetTop } ∨
      u = { .targetTop, .targetBase } ∨
      u = { .sourceHoleA, .sourceHoleB, .targetTop } ∨
      u = { .sourceHoleA, .targetTop, .targetBase } ∨
      u = { .sourceHoleB, .targetTop, .targetBase } ∨
      u = { .sourceHoleA, .sourceHoleB, .targetTop, .targetBase } := by
  native_decide

/-- source top が補集合に入る zero-sum なら target top も入る。 -/
private theorem sourceTwo_sourceTop_imp_targetTop
    {k n r L a b : ℕ}
    {u : Finset SourceTwoUnitIndex}
    (hab : a < b)
    (hbn : b < n)
    (hN : SourceTwoUnitIndex.negThree ∉ u)
    (hA : SourceTwoUnitIndex.sourceTop ∈ u)
    (hZero :
      Finset.sum u (fun i => (sourceTwoUnitTerm k n r L a b i).value) = 0) :
    SourceTwoUnitIndex.targetTop ∈ u := by
  by_contra hE
  have hHoles := sourceTwo_holes_lt_top (a := a) (b := b) (n := n) hab hbn
  have hCases := sourceTwo_sourceTop_without_targetTop_cases u hN hA hE
  rcases hCases with h | h | h | h | h | h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [sourceTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hApos : 0 < (2 : ℤ) ^ n * (3 : ℤ) ^ k := by positivity
    have hDpos : 0 < (2 : ℤ) ^ a * (3 : ℤ) ^ k := by positivity
    have hFpos : 0 < (2 : ℤ) ^ b * (3 : ℤ) ^ k := by positivity
    have hBpos : 0 < (2 : ℤ) ^ r := by positivity
    have hScaled0 :=
      mul_lt_mul_of_pos_right hHoles (show 0 < (3 : ℤ) ^ k by positivity)
    have hScaled :
        (2 : ℤ) ^ a * (3 : ℤ) ^ k + (2 : ℤ) ^ b * (3 : ℤ) ^ k <
          (2 : ℤ) ^ n * (3 : ℤ) ^ k := by
      simpa [add_mul] using hScaled0
    linarith

/-- target top が補集合に入る zero-sum なら source top も入る。 -/
private theorem sourceTwo_targetTop_imp_sourceTop
    {k n r L a b : ℕ}
    {u : Finset SourceTwoUnitIndex}
    (hL : 0 < L)
    (hN : SourceTwoUnitIndex.negThree ∉ u)
    (hE : SourceTwoUnitIndex.targetTop ∈ u)
    (hZero :
      Finset.sum u (fun i => (sourceTwoUnitTerm k n r L a b i).value) = 0) :
    SourceTwoUnitIndex.sourceTop ∈ u := by
  by_contra hA
  have hTopNat : 2 ^ r < 2 ^ (r + L) :=
    Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) (by omega : r < r + L)
  have hTop : (2 : ℤ) ^ r < (2 : ℤ) ^ (r + L) := by
    exact_mod_cast hTopNat
  have hCases := sourceTwo_targetTop_without_sourceTop_cases u hN hA hE
  rcases hCases with h | h | h | h | h | h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [sourceTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hDpos : 0 < (2 : ℤ) ^ a * (3 : ℤ) ^ k := by positivity
    have hFpos : 0 < (2 : ℤ) ^ b * (3 : ℤ) ^ k := by positivity
    have hBpos : 0 < (2 : ℤ) ^ r := by positivity
    linarith

private theorem sourceTwo_noNegative_cases :
    ∀ u : Finset SourceTwoUnitIndex,
      SourceTwoUnitIndex.negThree ∉ u →
      SourceTwoUnitIndex.sourceHoleA ∉ u →
      SourceTwoUnitIndex.sourceHoleB ∉ u →
      SourceTwoUnitIndex.targetTop ∉ u →
      u.Nonempty →
      u = { .sourceTop } ∨
      u = { .targetBase } ∨
      u = { .sourceTop, .targetBase } := by
  native_decide

private theorem sourceTwo_noPositive_cases :
    ∀ u : Finset SourceTwoUnitIndex,
      SourceTwoUnitIndex.negThree ∉ u →
      SourceTwoUnitIndex.sourceTop ∉ u →
      SourceTwoUnitIndex.targetBase ∉ u →
      u.Nonempty →
      u = { .sourceHoleA } ∨
      u = { .sourceHoleB } ∨
      u = { .targetTop } ∨
      u = { .sourceHoleA, .sourceHoleB } ∨
      u = { .sourceHoleA, .targetTop } ∨
      u = { .sourceHoleB, .targetTop } ∨
      u = { .sourceHoleA, .sourceHoleB, .targetTop } := by
  native_decide

private theorem sourceTwo_complement_has_negative
    {k n r L a b : ℕ}
    {u : Finset SourceTwoUnitIndex}
    (hN : SourceTwoUnitIndex.negThree ∉ u)
    (hu : u.Nonempty)
    (hZero :
      Finset.sum u (fun i => (sourceTwoUnitTerm k n r L a b i).value) = 0) :
    SourceTwoUnitIndex.sourceHoleA ∈ u ∨
      SourceTwoUnitIndex.sourceHoleB ∈ u ∨
        SourceTwoUnitIndex.targetTop ∈ u := by
  by_contra hNot
  push Not at hNot
  rcases sourceTwo_noNegative_cases u hN hNot.1 hNot.2.1 hNot.2.2 hu with h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [sourceTwoUnitTerm,  reduceCtorEq,
    Finset.mem_singleton, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hA : 0 < (2 : ℤ) ^ n * (3 : ℤ) ^ k := by positivity
    have hB : 0 < (2 : ℤ) ^ r := by positivity
    linarith

private theorem sourceTwo_complement_has_positive
    {k n r L a b : ℕ}
    {u : Finset SourceTwoUnitIndex}
    (hN : SourceTwoUnitIndex.negThree ∉ u)
    (hu : u.Nonempty)
    (hZero :
      Finset.sum u (fun i => (sourceTwoUnitTerm k n r L a b i).value) = 0) :
    SourceTwoUnitIndex.sourceTop ∈ u ∨ SourceTwoUnitIndex.targetBase ∈ u := by
  by_contra hNot
  push Not at hNot
  rcases sourceTwo_noPositive_cases u hN hNot.1 hNot.2 hu with h | h | h | h | h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [sourceTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_neg, pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hD : 0 < (2 : ℤ) ^ a * (3 : ℤ) ^ k := by positivity
    have hF : 0 < (2 : ℤ) ^ b * (3 : ℤ) ^ k := by positivity
    have hE : 0 < (2 : ℤ) ^ (r + L) := by positivity
    linarith

/-- `sourceTop ↔ targetTop` 後に残る source-two complement は11型。 -/
private theorem sourceTwo_complement_eleven_cases :
    ∀ u : Finset SourceTwoUnitIndex,
      SourceTwoUnitIndex.negThree ∉ u →
      u.Nonempty →
      (SourceTwoUnitIndex.sourceHoleA ∈ u ∨
        SourceTwoUnitIndex.sourceHoleB ∈ u ∨ SourceTwoUnitIndex.targetTop ∈ u) →
      (SourceTwoUnitIndex.sourceTop ∈ u ∨ SourceTwoUnitIndex.targetBase ∈ u) →
      (SourceTwoUnitIndex.sourceTop ∈ u → SourceTwoUnitIndex.targetTop ∈ u) →
      (SourceTwoUnitIndex.targetTop ∈ u → SourceTwoUnitIndex.sourceTop ∈ u) →
      u = { .sourceTop, .targetTop } ∨
      u = { .sourceTop, .targetTop, .targetBase } ∨
      u = { .sourceTop, .sourceHoleA, .targetTop } ∨
      u = { .sourceTop, .sourceHoleB, .targetTop } ∨
      u = { .sourceTop, .sourceHoleA, .sourceHoleB, .targetTop } ∨
      u = { .sourceTop, .sourceHoleA, .targetTop, .targetBase } ∨
      u = { .sourceTop, .sourceHoleB, .targetTop, .targetBase } ∨
      u = { .sourceTop, .sourceHoleA, .sourceHoleB, .targetTop, .targetBase } ∨
      u = { .sourceHoleA, .targetBase } ∨
      u = { .sourceHoleB, .targetBase } ∨
      u = { .sourceHoleA, .sourceHoleB, .targetBase } := by
  native_decide

private theorem sourceTwo_mod3_impossible_AE_family
    {k n r L a b : ℕ}
    {u : Finset SourceTwoUnitIndex}
    (hk : 0 < k)
    (hU :
      u = { .sourceTop, .targetTop } ∨
      u = { .sourceTop, .sourceHoleA, .targetTop } ∨
      u = { .sourceTop, .sourceHoleB, .targetTop } ∨
      u = { .sourceTop, .sourceHoleA, .sourceHoleB, .targetTop })
    (hZero :
      Finset.sum u (fun i => (sourceTwoUnitTerm k n r L a b i).value) = 0) :
    False := by
  rcases hU with h | h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [sourceTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hMod := congrArg (fun z : ℤ => (z : ZMod 3)) hZero
    push_cast at hMod
    rw [threePow_zmod3_eq_zero_of_pos hk] at hMod
    have hPowZero : (2 : ZMod 3) ^ (r + L) = 0 := by
      simpa using hMod
    exact twoPow_ne_zero_zmod3 (r + L) hPowZero

private theorem sourceTwo_mod3_impossible_holes_base
    {k n r L a b : ℕ}
    {u : Finset SourceTwoUnitIndex}
    (hk : 0 < k)
    (hU :
      u = { .sourceHoleA, .targetBase } ∨
      u = { .sourceHoleB, .targetBase } ∨
      u = { .sourceHoleA, .sourceHoleB, .targetBase })
    (hZero :
      Finset.sum u (fun i => (sourceTwoUnitTerm k n r L a b i).value) = 0) :
    False := by
  rcases hU with h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [sourceTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hMod := congrArg (fun z : ℤ => (z : ZMod 3)) hZero
    push_cast at hMod
    rw [threePow_zmod3_eq_zero_of_pos hk] at hMod
    have hPowZero : (2 : ZMod 3) ^ r = 0 := by
      simpa using hMod
    exact twoPow_ne_zero_zmod3 r hPowZero

private theorem sourceTwo_AEB_depth_one
    {k n r L a b : ℕ}
    {u : Finset SourceTwoUnitIndex}
    (hk : 0 < k)
    (hL : 0 < L)
    (hU : u = { .sourceTop, .targetTop, .targetBase })
    (hZero :
      Finset.sum u (fun i => (sourceTwoUnitTerm k n r L a b i).value) = 0) :
    k = 1 := by
  rw [hU] at hZero
  simp only [sourceTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  have hInt :
      (2 : ℤ) ^ n * (3 : ℤ) ^ k + (2 : ℤ) ^ r =
        (2 : ℤ) ^ (r + L) := by
    linarith
  have hNat : 2 ^ n * 3 ^ k + 2 ^ r = 2 ^ (r + L) := by
    exact_mod_cast hInt
  exact sourceTop_plus_twoPow_depth_one hk hL hNat

private theorem sourceTwo_selected_negative_impossible
    {k n r L a b : ℕ}
    {selected u : Finset SourceTwoUnitIndex}
    (hCert : SourceTwoMinimalPatternCertificate k n r L a b selected)
    (hu : u = (Finset.univ : Finset SourceTwoUnitIndex) \ selected)
    (hU :
      u = { .sourceTop, .sourceHoleA, .targetTop, .targetBase } ∨
      u = { .sourceTop, .sourceHoleB, .targetTop, .targetBase } ∨
      u = { .sourceTop, .sourceHoleA, .sourceHoleB, .targetTop, .targetBase }) :
    False := by
  rcases hU with h | h | h
  · have hComp :
        (Finset.univ : Finset SourceTwoUnitIndex) \ selected =
          { .sourceTop, .sourceHoleA, .targetTop, .targetBase } := by
      rw [← hu]; exact h
    have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
    have hSelected : selected = { .negThree, .sourceHoleB } := by
      rw [hSel0]
      native_decide
    have hSum := hCert.nondegenerate.sum_eq_one
    rw [hSelected] at hSum
    simp only [sourceTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
      not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
      SignedTwoThreeUnit.value_neg, Finset.sum_singleton] at hSum
    have hK : 0 < (3 : ℤ) ^ k := by positivity
    have hF : 0 < (2 : ℤ) ^ b * (3 : ℤ) ^ k := by positivity
    linarith
  · have hComp :
        (Finset.univ : Finset SourceTwoUnitIndex) \ selected =
          { .sourceTop, .sourceHoleB, .targetTop, .targetBase } := by
      rw [← hu]; exact h
    have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
    have hSelected : selected = { .negThree, .sourceHoleA } := by
      rw [hSel0]
      native_decide
    have hSum := hCert.nondegenerate.sum_eq_one
    rw [hSelected] at hSum
    simp only [sourceTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
      not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
      SignedTwoThreeUnit.value_neg, Finset.sum_singleton] at hSum
    have hK : 0 < (3 : ℤ) ^ k := by positivity
    have hD : 0 < (2 : ℤ) ^ a * (3 : ℤ) ^ k := by positivity
    linarith
  · have hComp :
        (Finset.univ : Finset SourceTwoUnitIndex) \ selected =
          { .sourceTop, .sourceHoleA, .sourceHoleB, .targetTop, .targetBase } := by
      rw [← hu]; exact h
    have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
    have hSelected : selected = { .negThree } := by
      rw [hSel0]
      native_decide
    have hSum := hCert.nondegenerate.sum_eq_one
    rw [hSelected] at hSum
    simp only [sourceTwoUnitTerm, Finset.sum_singleton,
      SignedTwoThreeUnit.value_negThree] at hSum
    have hK : 0 < (3 : ℤ) ^ k := by positivity
    linarith

/-- source-two non-full minimal certificate は `k=1` を強制する。 -/
theorem SourceTwoMinimalPatternCertificate.nonfull_depth_one
    {k n r L a b : ℕ}
    {selected : Finset SourceTwoUnitIndex}
    (hk : 0 < k)
    (hab : a < b)
    (hbn : b < n)
    (hL : 0 < L)
    (hEq : SourceTwoHoleEquation k n r L a b)
    (hCert : SourceTwoMinimalPatternCertificate k n r L a b selected)
    (hNotFull : selected ≠ (Finset.univ : Finset SourceTwoUnitIndex)) :
    k = 1 := by
  let u : Finset SourceTwoUnitIndex :=
    (Finset.univ : Finset SourceTwoUnitIndex) \ selected
  have huEq : u = (Finset.univ : Finset SourceTwoUnitIndex) \ selected := rfl
  have huNonempty : u.Nonempty := by
    dsimp [u]
    exact sourceTwo_complement_nonempty hNotFull
  have hN : SourceTwoUnitIndex.negThree ∉ u := by
    simp [u, hCert.anchor_mem]
  have hZero :
      Finset.sum u (fun i => (sourceTwoUnitTerm k n r L a b i).value) = 0 := by
    dsimp [u]
    exact sourceTwo_complement_sum_zero hEq hCert
  have hAE := sourceTwo_sourceTop_imp_targetTop
    (k := k) (n := n) (r := r) (L := L) (a := a) (b := b) (u := u)
    hab hbn hN
  have hEA := sourceTwo_targetTop_imp_sourceTop
    (k := k) (n := n) (r := r) (L := L) (a := a) (b := b) (u := u)
    hL hN
  have hNeg := sourceTwo_complement_has_negative hN huNonempty hZero
  have hPos := sourceTwo_complement_has_positive hN huNonempty hZero
  have hCases := sourceTwo_complement_eleven_cases u hN huNonempty hNeg hPos
    (fun h => hAE h hZero) (fun h => hEA h hZero)
  rcases hCases with
      hAE0 | hAEB | hAED | hAEF | hAEDF |
      hAEBD | hAEBF | hAEBDF | hDB | hFB | hDFB
  · exact False.elim (sourceTwo_mod3_impossible_AE_family hk (Or.inl hAE0) hZero)
  · exact sourceTwo_AEB_depth_one hk hL hAEB hZero
  · exact False.elim (sourceTwo_mod3_impossible_AE_family hk (Or.inr (Or.inl hAED)) hZero)
  · exact False.elim (sourceTwo_mod3_impossible_AE_family hk (Or.inr (Or.inr (Or.inl hAEF))) hZero)
  · exact False.elim (sourceTwo_mod3_impossible_AE_family hk (Or.inr (Or.inr (Or.inr hAEDF))) hZero)
  · exact False.elim (sourceTwo_selected_negative_impossible hCert huEq (Or.inl hAEBD))
  · exact False.elim (sourceTwo_selected_negative_impossible hCert huEq (Or.inr (Or.inl hAEBF)))
  · exact False.elim (sourceTwo_selected_negative_impossible hCert huEq (Or.inr (Or.inr hAEBDF)))
  · exact False.elim (sourceTwo_mod3_impossible_holes_base hk (Or.inl hDB) hZero)
  · exact False.elim (sourceTwo_mod3_impossible_holes_base hk (Or.inr (Or.inl hFB)) hZero)
  · exact False.elim (sourceTwo_mod3_impossible_holes_base hk (Or.inr (Or.inr hDFB)) hZero)

/-- `k≥3` の well-formed source-two は full six-term minimal certificate を持つ。 -/
theorem SourceTwoHoleEquation.largeDepth_exists_fullMinimalPattern
    {k n r L a b : ℕ}
    (hk3 : 3 ≤ k)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbn : b < n)
    (hr : 0 < r)
    (hL : 0 < L)
    (hEq : SourceTwoHoleEquation k n r L a b) :
    ∃ selected : Finset SourceTwoUnitIndex,
      SourceTwoMinimalPatternCertificate k n r L a b selected ∧
        SourceTwoFullPattern selected := by
  rcases hEq.exists_minimalPatternCertificate (by omega) ha0 (by omega) hr with
    ⟨selected, hCert⟩
  refine ⟨selected, hCert, ?_⟩
  unfold SourceTwoFullPattern
  by_contra hNotFull
  have hkOne := hCert.nonfull_depth_one (by omega) hab hbn hL hEq hNotFull
  omega

/-! ## target-two -/

private theorem targetTwo_complement_sum_zero
    {k n r L a b : ℕ}
    {selected : Finset TargetTwoUnitIndex}
    (hEq : TargetTwoHoleEquation k n r L a b)
    (hCert : TargetTwoMinimalPatternCertificate k n r L a b selected) :
    Finset.sum ((Finset.univ : Finset TargetTwoUnitIndex) \ selected)
        (fun i => (targetTwoUnitTerm k n r L a b i).value) = 0 := by
  have hAll := hEq.sixUnit_sum_eq_one
  have hSelected := hCert.nondegenerate.sum_eq_one
  have hSub : selected ⊆ (Finset.univ : Finset TargetTwoUnitIndex) := by
    intro i hi
    simp
  rw [← Finset.sum_sdiff hSub] at hAll
  rw [hSelected] at hAll
  omega

private theorem targetTwo_complement_nonempty
    {selected : Finset TargetTwoUnitIndex}
    (hNotFull : selected ≠ (Finset.univ : Finset TargetTwoUnitIndex)) :
    ((Finset.univ : Finset TargetTwoUnitIndex) \ selected).Nonempty := by
  by_contra hNot
  have hEmpty :
      (Finset.univ : Finset TargetTwoUnitIndex) \ selected = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hNot
  apply hNotFull
  ext i
  constructor
  · intro _
    simp
  · intro _
    by_contra hi
    have hiDiff : i ∈ (Finset.univ : Finset TargetTwoUnitIndex) \ selected := by
      simp [hi]
    rw [hEmpty] at hiDiff
    simp at hiDiff

/-- target 側の三小項の和は top より小さい。 -/
private theorem targetTwo_small_sum_lt_top
    {r L a b : ℕ}
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L) :
    (2 : ℤ) ^ r + (2 : ℤ) ^ (r + a) + (2 : ℤ) ^ (r + b) <
      (2 : ℤ) ^ (r + L) := by
  have hAB : 1 + 2 ^ a < 2 ^ b := by
    have ha1b : a + 1 ≤ b := by omega
    have hPow : 2 ^ (a + 1) ≤ 2 ^ b :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) ha1b
    have hSmall : 1 + 2 ^ a < 2 ^ (a + 1) := by
      rw [pow_succ]
      have hPos : 1 < 2 ^ a :=
        one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) (Nat.ne_of_gt ha0)
      omega
    exact lt_of_lt_of_le hSmall hPow
  have hSum : 1 + 2 ^ a + 2 ^ b < 2 ^ (b + 1) := by
    rw [pow_succ]
    omega
  have hb1L : b + 1 ≤ L := by omega
  have hTop : 2 ^ (b + 1) ≤ 2 ^ L :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hb1L
  have hInner : 1 + 2 ^ a + 2 ^ b < 2 ^ L := lt_of_lt_of_le hSum hTop
  have hMul :
      2 ^ r * (1 + 2 ^ a + 2 ^ b) < 2 ^ r * 2 ^ L :=
    Nat.mul_lt_mul_of_pos_left hInner (by positivity)
  have hNat : 2 ^ r + 2 ^ (r + a) + 2 ^ (r + b) < 2 ^ (r + L) := by
    rw [pow_add, pow_add, pow_add]
    simpa [mul_add, mul_assoc] using hMul
  exact_mod_cast hNat

private theorem targetTwo_without_targetTop_cases :
    ∀ u : Finset TargetTwoUnitIndex,
      TargetTwoUnitIndex.negThree ∉ u →
      TargetTwoUnitIndex.targetTop ∉ u →
      u.Nonempty →
      u = { .sourceTop } ∨
      u = { .targetBase } ∨
      u = { .targetHoleA } ∨
      u = { .targetHoleB } ∨
      u = { .sourceTop, .targetBase } ∨
      u = { .sourceTop, .targetHoleA } ∨
      u = { .sourceTop, .targetHoleB } ∨
      u = { .targetBase, .targetHoleA } ∨
      u = { .targetBase, .targetHoleB } ∨
      u = { .targetHoleA, .targetHoleB } ∨
      u = { .sourceTop, .targetBase, .targetHoleA } ∨
      u = { .sourceTop, .targetBase, .targetHoleB } ∨
      u = { .sourceTop, .targetHoleA, .targetHoleB } ∨
      u = { .targetBase, .targetHoleA, .targetHoleB } ∨
      u = { .sourceTop, .targetBase, .targetHoleA, .targetHoleB } := by
  native_decide

private theorem targetTwo_targetTop_without_sourceTop_cases :
    ∀ u : Finset TargetTwoUnitIndex,
      TargetTwoUnitIndex.negThree ∉ u →
      TargetTwoUnitIndex.sourceTop ∉ u →
      TargetTwoUnitIndex.targetTop ∈ u →
      u = { .targetTop } ∨
      u = { .targetTop, .targetBase } ∨
      u = { .targetTop, .targetHoleA } ∨
      u = { .targetTop, .targetHoleB } ∨
      u = { .targetTop, .targetBase, .targetHoleA } ∨
      u = { .targetTop, .targetBase, .targetHoleB } ∨
      u = { .targetTop, .targetHoleA, .targetHoleB } ∨
      u = { .targetTop, .targetBase, .targetHoleA, .targetHoleB } := by
  native_decide

/-- target-two zero-sum complement には唯一の負項 `targetTop` が必ず入る。 -/
private theorem targetTwo_complement_has_targetTop
    {k n r L a b : ℕ}
    {u : Finset TargetTwoUnitIndex}
    (hN : TargetTwoUnitIndex.negThree ∉ u)
    (hu : u.Nonempty)
    (hZero :
      Finset.sum u (fun i => (targetTwoUnitTerm k n r L a b i).value) = 0) :
    TargetTwoUnitIndex.targetTop ∈ u := by
  by_contra hE
  have hCases := targetTwo_without_targetTop_cases u hN hE hu
  rcases hCases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [targetTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hA : 0 < (2 : ℤ) ^ n * (3 : ℤ) ^ k := by positivity
    have hB : 0 < (2 : ℤ) ^ r := by positivity
    have hC : 0 < (2 : ℤ) ^ (r + a) := by positivity
    have hD : 0 < (2 : ℤ) ^ (r + b) := by positivity
    linarith

/-- target top が補集合にある zero-sum では source top も必ず入る。 -/
private theorem targetTwo_targetTop_imp_sourceTop
    {k n r L a b : ℕ}
    {u : Finset TargetTwoUnitIndex}
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hN : TargetTwoUnitIndex.negThree ∉ u)
    (hE : TargetTwoUnitIndex.targetTop ∈ u)
    (hZero :
      Finset.sum u (fun i => (targetTwoUnitTerm k n r L a b i).value) = 0) :
    TargetTwoUnitIndex.sourceTop ∈ u := by
  by_contra hA
  have hTop := targetTwo_small_sum_lt_top (r := r) ha0 hab hbL
  have hCases := targetTwo_targetTop_without_sourceTop_cases u hN hA hE
  rcases hCases with h | h | h | h | h | h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [targetTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hB : 0 < (2 : ℤ) ^ r := by positivity
    have hC : 0 < (2 : ℤ) ^ (r + a) := by positivity
    have hD : 0 < (2 : ℤ) ^ (r + b) := by positivity
    linarith

/-- target-two complement は8型だけ。 -/
private theorem targetTwo_complement_eight_cases :
    ∀ u : Finset TargetTwoUnitIndex,
      TargetTwoUnitIndex.negThree ∉ u →
      TargetTwoUnitIndex.targetTop ∈ u →
      TargetTwoUnitIndex.sourceTop ∈ u →
      u = { .sourceTop, .targetTop } ∨
      u = { .sourceTop, .targetTop, .targetBase } ∨
      u = { .sourceTop, .targetTop, .targetHoleA } ∨
      u = { .sourceTop, .targetTop, .targetHoleB } ∨
      u = { .sourceTop, .targetTop, .targetBase, .targetHoleA } ∨
      u = { .sourceTop, .targetTop, .targetBase, .targetHoleB } ∨
      u = { .sourceTop, .targetTop, .targetHoleA, .targetHoleB } ∨
      u = { .sourceTop, .targetTop, .targetBase, .targetHoleA, .targetHoleB } := by
  native_decide

private theorem targetTwo_AE_impossible
    {k n r L a b : ℕ}
    {u : Finset TargetTwoUnitIndex}
    (hk : 0 < k)
    (hU : u = { .sourceTop, .targetTop })
    (hZero :
      Finset.sum u (fun i => (targetTwoUnitTerm k n r L a b i).value) = 0) :
    False := by
  rw [hU] at hZero
  simp only [targetTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_pos,
    SignedTwoThreeUnit.value_neg, pow_zero, mul_one, Finset.sum_singleton] at hZero
  have hMod := congrArg (fun z : ℤ => (z : ZMod 3)) hZero
  push_cast at hMod
  rw [threePow_zmod3_eq_zero_of_pos hk] at hMod
  have hPowZero : (2 : ZMod 3) ^ (r + L) = 0 := by
    simpa using hMod
  exact twoPow_ne_zero_zmod3 (r + L) hPowZero

private theorem targetTwo_AE_single_depth_one
    {k n r L a b : ℕ}
    {u : Finset TargetTwoUnitIndex}
    (hk : 0 < k)
    (hU :
      u = { .sourceTop, .targetTop, .targetBase } ∨
      u = { .sourceTop, .targetTop, .targetHoleA } ∨
      u = { .sourceTop, .targetTop, .targetHoleB })
    (hab : a < b)
    (hbL : b < L)
    (hZero :
      Finset.sum u (fun i => (targetTwoUnitTerm k n r L a b i).value) = 0) :
    k = 1 := by
  rcases hU with hB | hC | hD
  · rw [hB] at hZero
    simp only [targetTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
      Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
      SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
      pow_zero, mul_one, Finset.sum_singleton] at hZero
    have hInt :
        (2 : ℤ) ^ n * (3 : ℤ) ^ k + (2 : ℤ) ^ r =
          (2 : ℤ) ^ (r + L) := by linarith
    have hNat : 2 ^ n * 3 ^ k + 2 ^ r = 2 ^ (r + L) := by exact_mod_cast hInt
    exact sourceTop_plus_twoPow_depth_one hk (by omega : 0 < L) hNat
  · rw [hC] at hZero
    simp only [targetTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
      Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
      SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
      pow_zero, mul_one, Finset.sum_singleton] at hZero
    have hInt :
        (2 : ℤ) ^ n * (3 : ℤ) ^ k + (2 : ℤ) ^ (r + a) =
          (2 : ℤ) ^ (r + L) := by linarith
    have hNat : 2 ^ n * 3 ^ k + 2 ^ (r + a) = 2 ^ (r + L) := by exact_mod_cast hInt
    have hExp : r + L = (r + a) + (L - a) := by omega
    rw [hExp] at hNat
    exact sourceTop_plus_twoPow_depth_one hk (by omega : 0 < L - a) hNat
  · rw [hD] at hZero
    simp only [targetTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
      Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
      SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
      pow_zero, mul_one, Finset.sum_singleton] at hZero
    have hInt :
        (2 : ℤ) ^ n * (3 : ℤ) ^ k + (2 : ℤ) ^ (r + b) =
          (2 : ℤ) ^ (r + L) := by linarith
    have hNat : 2 ^ n * 3 ^ k + 2 ^ (r + b) = 2 ^ (r + L) := by exact_mod_cast hInt
    have hExp : r + L = (r + b) + (L - b) := by omega
    rw [hExp] at hNat
    exact sourceTop_plus_twoPow_depth_one hk (by omega : 0 < L - b) hNat

private theorem targetTwo_selected_pair_depth_one
    {k n r L a b : ℕ}
    {selected u : Finset TargetTwoUnitIndex}
    (hk : 0 < k)
    (hCert : TargetTwoMinimalPatternCertificate k n r L a b selected)
    (hu : u = (Finset.univ : Finset TargetTwoUnitIndex) \ selected)
    (hU :
      u = { .sourceTop, .targetTop, .targetBase, .targetHoleA } ∨
      u = { .sourceTop, .targetTop, .targetBase, .targetHoleB } ∨
      u = { .sourceTop, .targetTop, .targetHoleA, .targetHoleB }) :
    k = 1 := by
  rcases hU with h | h | h
  · have hComp :
        (Finset.univ : Finset TargetTwoUnitIndex) \ selected =
          { .sourceTop, .targetTop, .targetBase, .targetHoleA } := by
      rw [← hu]; exact h
    have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
    have hSelected : selected = { .negThree, .targetHoleB } := by
      rw [hSel0]
      native_decide
    have hSum := hCert.nondegenerate.sum_eq_one
    rw [hSelected] at hSum
    simp only [targetTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
      not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
      SignedTwoThreeUnit.value_pos, pow_zero, mul_one, Finset.sum_singleton] at hSum
    have hInt : (3 : ℤ) ^ k + 1 = (2 : ℤ) ^ (r + b) := by linarith
    have hNat : 3 ^ k + 1 = 2 ^ (r + b) := by exact_mod_cast hInt
    exact threePow_add_one_eq_twoPow_depth_one hk hNat
  · have hComp :
        (Finset.univ : Finset TargetTwoUnitIndex) \ selected =
          { .sourceTop, .targetTop, .targetBase, .targetHoleB } := by
      rw [← hu]; exact h
    have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
    have hSelected : selected = { .negThree, .targetHoleA } := by
      rw [hSel0]
      native_decide
    have hSum := hCert.nondegenerate.sum_eq_one
    rw [hSelected] at hSum
    simp only [targetTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
      not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
      SignedTwoThreeUnit.value_pos, pow_zero, mul_one, Finset.sum_singleton] at hSum
    have hInt : (3 : ℤ) ^ k + 1 = (2 : ℤ) ^ (r + a) := by linarith
    have hNat : 3 ^ k + 1 = 2 ^ (r + a) := by exact_mod_cast hInt
    exact threePow_add_one_eq_twoPow_depth_one hk hNat
  · have hComp :
        (Finset.univ : Finset TargetTwoUnitIndex) \ selected =
          { .sourceTop, .targetTop, .targetHoleA, .targetHoleB } := by
      rw [← hu]; exact h
    have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
    have hSelected : selected = { .negThree, .targetBase } := by
      rw [hSel0]
      native_decide
    have hSum := hCert.nondegenerate.sum_eq_one
    rw [hSelected] at hSum
    simp only [targetTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
      not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
      SignedTwoThreeUnit.value_pos, pow_zero, mul_one, Finset.sum_singleton] at hSum
    have hInt : (3 : ℤ) ^ k + 1 = (2 : ℤ) ^ r := by linarith
    have hNat : 3 ^ k + 1 = 2 ^ r := by exact_mod_cast hInt
    exact threePow_add_one_eq_twoPow_depth_one hk hNat

private theorem targetTwo_selected_anchor_impossible
    {k n r L a b : ℕ}
    {selected u : Finset TargetTwoUnitIndex}
    (hCert : TargetTwoMinimalPatternCertificate k n r L a b selected)
    (hu : u = (Finset.univ : Finset TargetTwoUnitIndex) \ selected)
    (hU :
      u = { .sourceTop, .targetTop, .targetBase, .targetHoleA, .targetHoleB }) :
    False := by
  have hComp :
      (Finset.univ : Finset TargetTwoUnitIndex) \ selected =
        { .sourceTop, .targetTop, .targetBase, .targetHoleA, .targetHoleB } := by
    rw [← hu]
    exact hU
  have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
  have hSelected : selected = { .negThree } := by
    rw [hSel0]
    native_decide
  have hSum := hCert.nondegenerate.sum_eq_one
  rw [hSelected] at hSum
  simp only [targetTwoUnitTerm, Finset.sum_singleton,
    SignedTwoThreeUnit.value_negThree] at hSum
  have hK : 0 < (3 : ℤ) ^ k := by positivity
  linarith

/-- target-two non-full minimal certificate は `k=1` を強制する。 -/
theorem TargetTwoMinimalPatternCertificate.nonfull_depth_one
    {k n r L a b : ℕ}
    {selected : Finset TargetTwoUnitIndex}
    (hk : 0 < k)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hEq : TargetTwoHoleEquation k n r L a b)
    (hCert : TargetTwoMinimalPatternCertificate k n r L a b selected)
    (hNotFull : selected ≠ (Finset.univ : Finset TargetTwoUnitIndex)) :
    k = 1 := by
  let u : Finset TargetTwoUnitIndex :=
    (Finset.univ : Finset TargetTwoUnitIndex) \ selected
  have huEq : u = (Finset.univ : Finset TargetTwoUnitIndex) \ selected := rfl
  have huNonempty : u.Nonempty := by
    dsimp [u]
    exact targetTwo_complement_nonempty hNotFull
  have hN : TargetTwoUnitIndex.negThree ∉ u := by
    simp [u, hCert.anchor_mem]
  have hZero :
      Finset.sum u (fun i => (targetTwoUnitTerm k n r L a b i).value) = 0 := by
    dsimp [u]
    exact targetTwo_complement_sum_zero hEq hCert
  have hE := targetTwo_complement_has_targetTop hN huNonempty hZero
  have hA := targetTwo_targetTop_imp_sourceTop
    (k := k) (n := n) (r := r) (L := L) (a := a) (b := b) (u := u)
    ha0 hab hbL hN hE hZero
  have hCases := targetTwo_complement_eight_cases u hN hE hA
  rcases hCases with hAE | hAEB | hAEC | hAED | hAEBC | hAEBD | hAECD | hAEBCD
  · exact False.elim (targetTwo_AE_impossible hk hAE hZero)
  · exact targetTwo_AE_single_depth_one hk (Or.inl hAEB) hab hbL hZero
  · exact targetTwo_AE_single_depth_one hk (Or.inr (Or.inl hAEC)) hab hbL hZero
  · exact targetTwo_AE_single_depth_one hk (Or.inr (Or.inr hAED)) hab hbL hZero
  · exact targetTwo_selected_pair_depth_one hk hCert huEq (Or.inl hAEBC)
  · exact targetTwo_selected_pair_depth_one hk hCert huEq (Or.inr (Or.inl hAEBD))
  · exact targetTwo_selected_pair_depth_one hk hCert huEq (Or.inr (Or.inr hAECD))
  · exact False.elim (targetTwo_selected_anchor_impossible hCert huEq hAEBCD)

/-- `k≥3` の well-formed target-two は full six-term minimal certificate を持つ。 -/
theorem TargetTwoHoleEquation.largeDepth_exists_fullMinimalPattern
    {k n r L a b : ℕ}
    (hk3 : 3 ≤ k)
    (hn : 0 < n)
    (hr : 0 < r)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbL : b < L)
    (hEq : TargetTwoHoleEquation k n r L a b) :
    ∃ selected : Finset TargetTwoUnitIndex,
      TargetTwoMinimalPatternCertificate k n r L a b selected ∧
        TargetTwoFullPattern selected := by
  rcases hEq.exists_minimalPatternCertificate hn hr with ⟨selected, hCert⟩
  refine ⟨selected, hCert, ?_⟩
  unfold TargetTwoFullPattern
  by_contra hNotFull
  have hkOne := hCert.nonfull_depth_one (by omega) ha0 hab hbL hEq hNotFull
  omega

end Mersenne
end Collatz3
