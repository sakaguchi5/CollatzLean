import CollatzLean.Collatz3.Mersenne.Basic
import CollatzLean.Collatz3.Binary.SparseComplement
import CollatzLean.Collatz3.Mersenne.OneZeroSUnitReduction
import CollatzLean.Collatz3.Arithmetic.TwoThreeUnit
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: bounded block defect の `{2,3}`-S-unit reduction

一般の `BlockData`

`x + 1 = 2^k * u`
`2^r * y + 1 = 3^k * u`

に対し、係数 `u` と出口 `y` の binary zero defect がともに有界なら、
両側の sparse complement を一つの符号付き `{2,3}`-unit zero-sum にまとめられる。

one-zero 専用の `u = 2^n - 1` は仮定しない。
source 側の missing bit は `-2^a * 3^k`、target 側の missing bit は
`+2^(r+b)` として現れる。

このファイルで無条件に行うことは次の四点。

1. source / target の sparse missing bit を `{2,3}`-unit 列へ展開する。
2. `BlockData` と二つの sparse-complement equation を exact zero-sum にする。
3. `-3^k` を含む極小消滅部分和を取る。
4. parity により、その極小部分和が必ず constant `-1` も含むことを示す。

深い ESS / Subspace theorem はここへ入れない。
-/

namespace Collatz3
namespace Mersenne
namespace BlockSparseSUnit

open Arithmetic
open Arithmetic.SignedTwoThreeUnit

/--
source coefficient `u` の missing bit を負の mixed `{2,3}`-unit に展開する。

offset `a` から始めた bit `1` は `-2^a * 3^k` に対応する。
-/
def sourceMissingTerms (k offset : ℕ) : List Bool → List SignedTwoThreeUnit
  | [] => []
  | b :: bs =>
      (if b then [neg offset k] else []) ++
        sourceMissingTerms k (offset + 1) bs

/-- source missing term の個数は元 word の one-count。 -/
theorem sourceMissingTerms_length
    (k offset : ℕ)
    (bits : List Bool) :
    (sourceMissingTerms k offset bits).length = Binary.oneCount bits := by
  induction bits generalizing offset with
  | nil =>
      simp [sourceMissingTerms, Binary.oneCount]
  | cons b bs ih =>
      cases b <;>
        simp [sourceMissingTerms, Binary.oneCount, ih, Nat.add_comm]

/--
source missing term の整数和は
`-2^offset * 3^k * value(bits)` に exact に一致する。
-/
theorem sourceMissingTerms_value_sum
    (k offset : ℕ)
    (bits : List Bool) :
    ((sourceMissingTerms k offset bits).map SignedTwoThreeUnit.value).sum =
      -((2 : ℤ) ^ offset * (3 : ℤ) ^ k *
        (Binary.valueLSB bits : ℤ)) := by
  induction bits generalizing offset with
  | nil =>
      simp [sourceMissingTerms, Binary.valueLSB]
  | cons b bs ih =>
      cases b <;>
        simp [sourceMissingTerms, Binary.valueLSB, ih, pow_succ] <;>
        ring

/-- offset が正なら source missing term の 2-adic exponent もすべて正。 -/
theorem sourceMissingTerms_twoExp_pos
    {k offset : ℕ} {bits : List Bool} {t : SignedTwoThreeUnit}
    (hOffset : 0 < offset)
    (ht : t ∈ sourceMissingTerms k offset bits) :
    0 < t.twoExp := by
  induction bits generalizing offset with
  | nil =>
      simp [sourceMissingTerms] at ht
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [sourceMissingTerms, Bool.false_eq_true, ↓reduceIte,
            List.nil_append] at ht
          exact ih (by omega) ht
      | true =>
          simp only [sourceMissingTerms, ↓reduceIte, List.cons_append,
            List.nil_append, List.mem_cons] at ht
          rcases ht with hHead | hTail
          · subst t
            simpa [neg] using hOffset
          · exact ih (by omega) hTail

/--
`BlockData` の coefficient `u` に対する sparse complement は、bit 0 を missing にできない。

理由は、bit 0 が missing なら `u` が偶数になり、`r>0` の endpoint equation
`2^r*y+1 = 3^k*u` の左辺が奇数・右辺が偶数になって矛盾するため。
-/
theorem sourceBits_eq_false_cons
    {k r u x y sourceLength : ℕ}
    {sourceBits : List Bool}
    (hBlock : BlockData k r u x y)
    (hLen : sourceBits.length = sourceLength)
    (hEq :
      u + Binary.valueLSB sourceBits + 1 = 2 ^ sourceLength) :
    ∃ tail : List Bool, sourceBits = false :: tail := by
  have huPos : 0 < u := by
    by_contra hu
    have hu0 : u = 0 := Nat.eq_zero_of_not_pos hu
    have hStart := hBlock.startEquation
    rw [hu0] at hStart
    simp at hStart
  have hLengthPos : 0 < sourceLength := by
    by_contra hLength
    have hLength0 : sourceLength = 0 := Nat.eq_zero_of_not_pos hLength
    rw [hLength0] at hEq
    norm_num at hEq
    omega
  cases sourceBits with
  | nil =>
      simp at hLen
      omega
  | cons b tail =>
      cases b with
      | false =>
          exact ⟨tail, rfl⟩
      | true =>
          exfalso
          obtain ⟨q, hLengthEq⟩ :=
            Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hLengthPos)
          have hEq' := hEq
          rw [hLengthEq] at hEq'
          simp only [Binary.valueLSB_cons, Binary.bitValue_true] at hEq'
          rw [pow_succ] at hEq'
          have huEven : ∃ z : ℕ, u = 2 * z := by
            refine ⟨2 ^ q - Binary.valueLSB tail - 1, ?_⟩
            omega
          rcases huEven with ⟨z, huz⟩
          have hEnd := hBlock.endEquation
          rw [huz] at hEnd
          obtain ⟨s, hrEq⟩ :=
            Nat.exists_eq_succ_of_ne_zero
              (Nat.ne_of_gt hBlock.exitDepth_pos)
          rw [hrEq] at hEnd
          have hParity :
              2 * (2 ^ s * y) + 1 =
                2 * (3 ^ k * z) := by
            calc
              2 * (2 ^ s * y) + 1
                  = 2 ^ (s + 1) * y + 1 := by
                      rw [pow_succ]
                      ring
              _ = 3 ^ k * (2 * z) := hEnd
              _ = 2 * (3 ^ k * z) := by ring
          omega

/--
二つの odd anchor `-1`, `-3^k` を除いた even-side の unit 列。

source の sparse correction、target の sparse correction、両端の power-of-two 項を
一つの list にまとめる。
-/
def evenTerms
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :
    List SignedTwoThreeUnit :=
  pos sourceLength k ::
    (sourceMissingTerms k 0 (false :: sourceTail) ++
      SparseSUnit.missingTerms r targetBits ++
      [pos r 0, neg (targetLength + r) 0])

/-- even-side の項数は source/target の sparse one-count と定数 3 の和。 -/
theorem evenTerms_length
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :
    (evenTerms k sourceLength r targetLength sourceTail targetBits).length =
      Binary.oneCount sourceTail + Binary.oneCount targetBits + 3 := by
  simp [evenTerms, sourceMissingTerms_length,
    SparseSUnit.missingTerms_length, Binary.oneCount]
  omega

/-- even-side の整数和。 -/
theorem evenTerms_value_sum
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :
    ((evenTerms k sourceLength r targetLength sourceTail targetBits).map
      SignedTwoThreeUnit.value).sum =
      (2 : ℤ) ^ sourceLength * (3 : ℤ) ^ k -
        (3 : ℤ) ^ k *
          (Binary.valueLSB (false :: sourceTail) : ℤ) +
        (2 : ℤ) ^ r * (Binary.valueLSB targetBits : ℤ) +
        (2 : ℤ) ^ r -
        (2 : ℤ) ^ (targetLength + r) := by
  simp [evenTerms, sourceMissingTerms_value_sum,
    SparseSUnit.missingTerms_value_sum, Binary.valueLSB]
  ring

/--
source word が `false :: sourceTail` で、`sourceLength>0`, `r>0` なら、
even-side の全 unit は実際に 2-adic exponent が正。
-/
theorem evenTerms_twoExp_pos
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    {t : SignedTwoThreeUnit}
    (hSourceLength : 0 < sourceLength)
    (hr : 0 < r)
    (ht :
      t ∈ evenTerms k sourceLength r targetLength sourceTail targetBits) :
    0 < t.twoExp := by
  simp only [evenTerms, List.mem_cons, List.mem_append] at ht
  rcases ht with hLead | hRest
  · subst t
    simpa [pos] using hSourceLength
  · rcases hRest with hSparse | hEnds
    · rcases hSparse with hSource | hTarget
      · simp only [
          sourceMissingTerms,
          Bool.false_eq_true,
          ↓reduceIte,
          List.nil_append
        ] at hSource
        exact
          sourceMissingTerms_twoExp_pos
            (k := k)
            (offset := 1)
            (bits := sourceTail)
            (by omega)
            hSource
      · exact
          SparseSUnit.missingTerms_twoExp_pos hr hTarget
    · rcases hEnds with hShift | hTop
      · subst t
        simpa [pos] using hr
      · rcases hTop with hTop | hNil
        · subst t
          have hTopPos : 0 < targetLength + r := by
            omega
          simpa [neg] using hTopPos
        · simp at hNil



/-- 二つの odd anchor と even-side を型レベルで分離した有限 index。 -/
abbrev BlockSparseIndex
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :=
  Sum (Fin 2)
    (Fin (evenTerms k sourceLength r targetLength sourceTail targetBits).length)

/-- index が指す符号付き `{2,3}`-unit。 -/
def indexedTerm
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :
    BlockSparseIndex k sourceLength r targetLength sourceTail targetBits →
      SignedTwoThreeUnit
  | Sum.inl i =>
      if i.1 = 0 then negOne else negThree k
  | Sum.inr i =>
      (evenTerms k sourceLength r targetLength sourceTail targetBits).get i

/-- constant `-1` の index。 -/
def oneIndex
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :
    BlockSparseIndex k sourceLength r targetLength sourceTail targetBits :=
  Sum.inl ⟨0, by decide⟩

/-- `-3^k` の index。 -/
def threeIndex
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :
    BlockSparseIndex k sourceLength r targetLength sourceTail targetBits :=
  Sum.inl ⟨1, by decide⟩

@[simp] theorem indexedTerm_oneIndex
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :
    indexedTerm k sourceLength r targetLength sourceTail targetBits
      (oneIndex k sourceLength r targetLength sourceTail targetBits) = negOne := by
  simp [indexedTerm, oneIndex]

@[simp] theorem indexedTerm_threeIndex
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :
    indexedTerm k sourceLength r targetLength sourceTail targetBits
      (threeIndex k sourceLength r targetLength sourceTail targetBits) = negThree k := by
  simp [indexedTerm, threeIndex]

@[simp] theorem oneIndex_ne_threeIndex
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :
    oneIndex k sourceLength r targetLength sourceTail targetBits ≠
      threeIndex k sourceLength r targetLength sourceTail targetBits := by
  simp [oneIndex, threeIndex]

/-- `Finset.univ` で list 全体を走査した和は通常の `List.sum`。 -/
private theorem finset_univ_sum_get_map_eq_sum
    {α : Type*}
    (f : α → ℤ)
    (xs : List α) :
    Finset.sum
        (Finset.univ : Finset (Fin xs.length))
        (fun i => f (xs.get i)) =
      (xs.map f).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      change
        Finset.sum
            (Finset.univ : Finset (Fin (xs.length + 1)))
            (fun i => f ((x :: xs).get i)) =
          f x + (xs.map f).sum
      calc
        Finset.sum
            (Finset.univ : Finset (Fin (xs.length + 1)))
            (fun i => f ((x :: xs).get i))
            =
          f x +
            Finset.sum
              (Finset.univ : Finset (Fin xs.length))
              (fun i => f (xs.get i)) := by
          simpa using
            (Fin.sum_univ_succ
              (fun i : Fin (xs.length + 1) =>
                f ((x :: xs).get i)))
        _ = f x + (xs.map f).sum := by rw [ih]

/--
`BlockData` と source/target の sparse-complement equation を
整数環上の一つの exact zero-sum にまとめる。
-/
theorem blockEquation_int
    {k r u x y sourceLength targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hBlock : BlockData k r u x y)
    (hSourceEq :
      u + Binary.valueLSB (false :: sourceTail) + 1 = 2 ^ sourceLength)
    (hTargetEq :
      y + Binary.valueLSB targetBits + 1 = 2 ^ targetLength) :
    (-1 : ℤ) - (3 : ℤ) ^ k +
        (2 : ℤ) ^ sourceLength * (3 : ℤ) ^ k -
        (3 : ℤ) ^ k *
          (Binary.valueLSB (false :: sourceTail) : ℤ) +
        (2 : ℤ) ^ r * (Binary.valueLSB targetBits : ℤ) +
        (2 : ℤ) ^ r -
        (2 : ℤ) ^ (targetLength + r) = 0 := by
  have hSourceCast := congrArg (fun z : ℕ => (z : ℤ)) hSourceEq
  have hTargetCast := congrArg (fun z : ℕ => (z : ℤ)) hTargetEq
  have hEndCast := congrArg (fun z : ℕ => (z : ℤ)) hBlock.endEquation
  push_cast at hSourceCast hTargetCast hEndCast
  calc
    (-1 : ℤ) - (3 : ℤ) ^ k +
          (2 : ℤ) ^ sourceLength * (3 : ℤ) ^ k -
          (3 : ℤ) ^ k *
            (Binary.valueLSB (false :: sourceTail) : ℤ) +
          (2 : ℤ) ^ r * (Binary.valueLSB targetBits : ℤ) +
          (2 : ℤ) ^ r -
          (2 : ℤ) ^ (targetLength + r)
        =
        (-1 : ℤ) - (3 : ℤ) ^ k +
          (((u : ℤ) +
              (Binary.valueLSB (false :: sourceTail) : ℤ) + 1) *
            (3 : ℤ) ^ k) -
          (3 : ℤ) ^ k *
            (Binary.valueLSB (false :: sourceTail) : ℤ) +
          (2 : ℤ) ^ r * (Binary.valueLSB targetBits : ℤ) +
          (2 : ℤ) ^ r -
          (2 : ℤ) ^ (targetLength + r) := by
            rw [hSourceCast]
    _ =
        (-1 : ℤ) + (3 : ℤ) ^ k * (u : ℤ) +
          (2 : ℤ) ^ r * (Binary.valueLSB targetBits : ℤ) +
          (2 : ℤ) ^ r -
          (2 : ℤ) ^ (targetLength + r) := by ring
    _ =
        (2 : ℤ) ^ r * (y : ℤ) +
          (2 : ℤ) ^ r * (Binary.valueLSB targetBits : ℤ) +
          (2 : ℤ) ^ r -
          (2 : ℤ) ^ (targetLength + r) := by
            rw [← hEndCast]
            ring
    _ =
        (2 : ℤ) ^ r *
            ((y : ℤ) + (Binary.valueLSB targetBits : ℤ) + 1) -
          (2 : ℤ) ^ (targetLength + r) := by ring
    _ =
        (2 : ℤ) ^ r * (2 : ℤ) ^ targetLength -
          (2 : ℤ) ^ (targetLength + r) := by
            rw [hTargetCast]
    _ = 0 := by
      rw [pow_add]
      ring

/-- 全 block-sparse index の個数は source/target one-count と 5 の和。 -/
theorem blockSparseIndex_card
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) :
    Fintype.card
        (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits) =
      Binary.oneCount sourceTail + Binary.oneCount targetBits + 5 := by
  simp [BlockSparseIndex, evenTerms_length]
  omega

/-- block sparse equation は全 index 上の exact zero-sum を与える。 -/
theorem indexedTerm_univ_sum_zero
    {k r u x y sourceLength targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hBlock : BlockData k r u x y)
    (hSourceEq :
      u + Binary.valueLSB (false :: sourceTail) + 1 = 2 ^ sourceLength)
    (hTargetEq :
      y + Binary.valueLSB targetBits + 1 = 2 ^ targetLength) :
    Finset.sum
        (Finset.univ : Finset
          (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits))
        (fun i =>
          (indexedTerm k sourceLength r targetLength sourceTail targetBits i).value) = 0 := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  simp [indexedTerm, evenTerms_value_sum]
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    (blockEquation_int hBlock hSourceEq hTargetEq)

/--
parity anchor。

`sourceLength>0, r>0` の block-sparse zero-sum で `-3^k` を含む部分和は、
同じ部分和の中に必ず constant `-1` も含む。
-/
theorem vanishing_contains_one
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hSourceLength : 0 < sourceLength)
    (hr : 0 < r)
    {s : Finset
      (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits)}
    (hThree :
      threeIndex k sourceLength r targetLength sourceTail targetBits ∈ s)
    (hZero :
      Finset.sum s
        (fun i =>
          (indexedTerm k sourceLength r targetLength sourceTail targetBits i).value) = 0) :
    oneIndex k sourceLength r targetLength sourceTail targetBits ∈ s := by
  classical
  let three := threeIndex k sourceLength r targetLength sourceTail targetBits
  let one := oneIndex k sourceLength r targetLength sourceTail targetBits
  let term := indexedTerm k sourceLength r targetLength sourceTail targetBits
  by_contra hOne
  have hEvenEach :
      ∀ i ∈ s.erase three,
        IntEven ((term i).value) := by
    intro i hi
    have hiData := Finset.mem_erase.mp hi
    have hiNeThree : i ≠ three := hiData.1
    have hiS : i ∈ s := hiData.2
    rcases i with i | i
    · have hCases : i.1 = 0 ∨ i.1 = 1 := by omega
      rcases hCases with hZeroIdx | hOneIdx
      · have hiFin : i = (⟨0, by decide⟩ : Fin 2) := by
          apply Fin.ext
          exact hZeroIdx
        have hiEq :
            (Sum.inl i :
              BlockSparseIndex k sourceLength r targetLength sourceTail targetBits) =
              one := by
          simpa [one, oneIndex] using
            congrArg
              (fun j : Fin 2 =>
                (Sum.inl j :
                  BlockSparseIndex k sourceLength r targetLength sourceTail targetBits))
              hiFin
        rw [hiEq] at hiS
        exact False.elim (hOne hiS)
      · have hiFin : i = (⟨1, by decide⟩ : Fin 2) := by
          apply Fin.ext
          exact hOneIdx
        have hiEq :
            (Sum.inl i :
              BlockSparseIndex k sourceLength r targetLength sourceTail targetBits) =
              three := by
          simpa [three, threeIndex] using
            congrArg
              (fun j : Fin 2 =>
                (Sum.inl j :
                  BlockSparseIndex k sourceLength r targetLength sourceTail targetBits))
              hiFin
        exact False.elim (hiNeThree hiEq)
    · apply SignedTwoThreeUnit.value_even_of_twoExp_pos
      apply evenTerms_twoExp_pos hSourceLength hr
      exact List.get_mem _ _
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
    rw [Finset.sum_erase_add
      s
      (fun i => (term i).value)
      hThree]
    exact hZero
  apply SignedTwoThreeUnit.negThree_not_even k
  refine ⟨-q, ?_⟩
  have hThreeValue : term three = negThree k := by
    simp [term, three]
  rw [hq, hThreeValue] at hDecomp
  omega

/--
一般 `BlockData` と source/target の sparse complement から、
nondegenerate `{2,3}`-unit certificate を得る。

source / target の missing bit 数だけが certificate の項数に影響し、
zero の具体的な位置は問わない。
-/
theorem exists_nondegenerateCertificate
    {k r u x y sourceLength targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hBlock : BlockData k r u x y)
    (hSourceLen : (false :: sourceTail).length = sourceLength)
    (hSourceEq :
      u + Binary.valueLSB (false :: sourceTail) + 1 = 2 ^ sourceLength)
    (hTargetEq :
      y + Binary.valueLSB targetBits + 1 = 2 ^ targetLength) :
    ∃ selected : Finset
        (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits),
      selected.card ≤
        Binary.oneCount sourceTail + Binary.oneCount targetBits + 5 ∧
      NondegenerateSumOne
        (fun i =>
          (indexedTerm k sourceLength r targetLength sourceTail targetBits i).value)
        selected ∧
      threeIndex k sourceLength r targetLength sourceTail targetBits ∈ selected := by
  classical
  let term := indexedTerm k sourceLength r targetLength sourceTail targetBits
  let three := threeIndex k sourceLength r targetLength sourceTail targetBits
  let one := oneIndex k sourceLength r targetLength sourceTail targetBits
  have hSourceLength : 0 < sourceLength := by
    have hNonempty : 0 < (false :: sourceTail).length := by simp
    omega
  have hUnivZero :
      Vanishes
        (fun i => (term i).value)
        (Finset.univ : Finset
          (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits)) := by
    unfold Vanishes
    simpa [term] using
      indexedTerm_univ_sum_zero hBlock hSourceEq hTargetEq
  rcases exists_anchorMinimalVanishing
      (v := fun i => (term i).value)
      three
      (s₀ := (Finset.univ : Finset
        (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits)))
      (by simp)
      hUnivZero with
    ⟨s, hsUniv, hMinimal⟩
  have hOne : one ∈ s := by
    apply vanishing_contains_one hSourceLength hBlock.exitDepth_pos
      hMinimal.anchor_mem
    exact hMinimal.sum_eq_zero
  let selected := s.erase one
  have hNondegenerate :
      NondegenerateSumOne
        (fun i => (term i).value)
        selected := by
    apply hMinimal.erase_neg_one hOne
    simp [term, one]
  have hThreeSelected : three ∈ selected := by
    apply Finset.mem_erase.mpr
    constructor
    · simpa [one, three] using
        (oneIndex_ne_threeIndex k sourceLength r targetLength
          sourceTail targetBits).symm
    · exact hMinimal.anchor_mem
  refine ⟨selected, ?_, hNondegenerate, hThreeSelected⟩
  calc
    selected.card ≤
        (Finset.univ : Finset
          (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits)).card :=
      Finset.card_le_card (Finset.subset_univ selected)
    _ = Binary.oneCount sourceTail + Binary.oneCount targetBits + 5 := by
      simpa only [Finset.card_univ] using
        blockSparseIndex_card k sourceLength r targetLength sourceTail targetBits

end BlockSparseSUnit
end Mersenne
end Collatz3
