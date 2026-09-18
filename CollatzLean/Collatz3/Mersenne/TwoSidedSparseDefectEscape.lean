import CollatzLean.Collatz3.Mersenne.BoundedBlockSUnitReduction
import CollatzLean.Collatz3.Mersenne.SourceDefectBridge
import CollatzLean.Collatz3.Arithmetic.TwoSidedSignedSparsePow3

/-!
# Collatz3 Mersenne: block sparse certificate の two-layer 構造

`BoundedBlockSUnitReduction` が作る certificate では、すべての項の 3-adic exponent が
`0` または block depth `k` の二層に限られることを証明する。

これにより、深い数論 target `TwoSidedSignedSparsePow3` が得られれば、
Collatz 側へ

`k < (A+B+7)^(C0*(A+B+7))`

型の explicit defect bound を直接戻せる。

`+7` なのは、既存 certificate の selected cardinality `A+B+5` をそのまま使い、
冪 envelope 内部でさらに `D+2` が現れるためである。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic
open Arithmetic.SignedTwoThreeUnit

namespace BlockSparseSUnit

/-- source missing term の 3-exponent は常に `k`。 -/
theorem sourceMissingTerms_threeExp_eq
    {k offset : ℕ} {bits : List Bool} {t : SignedTwoThreeUnit}
    (ht : t ∈ sourceMissingTerms k offset bits) :
    t.threeExp = k := by
  induction bits generalizing offset with
  | nil =>
      simp [sourceMissingTerms] at ht
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [sourceMissingTerms, Bool.false_eq_true, ↓reduceIte,
            List.nil_append] at ht
          exact ih ht
      | true =>
          simp only [sourceMissingTerms, ↓reduceIte, List.cons_append,
            List.nil_append, List.mem_cons] at ht
          rcases ht with hHead | hTail
          · subst t
            simp [neg]
          · exact ih hTail

/-- one-zero 層から再利用している target missing term は 3-exponent `0`。 -/
theorem targetMissingTerms_threeExp_eq_zero
    {r : ℕ} {bits : List Bool} {t : SignedTwoThreeUnit}
    (ht : t ∈ SparseSUnit.missingTerms r bits) :
    t.threeExp = 0 := by
  induction bits generalizing r with
  | nil =>
      simp [SparseSUnit.missingTerms] at ht
  | cons b bs ih =>
      cases b with
      | false =>
          simp only [SparseSUnit.missingTerms, Bool.false_eq_true, ↓reduceIte,
            List.nil_append] at ht
          exact ih ht
      | true =>
          simp only [SparseSUnit.missingTerms, ↓reduceIte, List.cons_append,
            List.nil_append, List.mem_cons] at ht
          rcases ht with hHead | hTail
          · subst t
            simp [pos]
          · exact ih hTail

/-- even-side の各項は 3-exponent `0` または `k`。 -/
theorem evenTerms_twoLayer
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    {t : SignedTwoThreeUnit}
    (ht : t ∈ evenTerms k sourceLength r targetLength sourceTail targetBits) :
    IsTwoLayerAt k t := by
  simp only [evenTerms, List.mem_cons, List.mem_append] at ht
  rcases ht with hLead | hRest
  · subst t
    exact Or.inr rfl
  · rcases hRest with hSparse | hEnds
    · rcases hSparse with hSource | hTarget
      · exact Or.inr (sourceMissingTerms_threeExp_eq hSource)
      · exact Or.inl (targetMissingTerms_threeExp_eq_zero hTarget)
    · rcases hEnds with hShift | hTop
      · subst t
        exact Or.inl rfl
      · rcases hTop with hTop | hNil
        · subst t
          exact Or.inl rfl
        · simp at hNil

/--
block sparse index が指す全 unit は 3-exponent `0` または `k` の二層にある。
-/
theorem indexedTerm_twoLayer
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool)
    (i : BlockSparseIndex k sourceLength r targetLength sourceTail targetBits) :
    IsTwoLayerAt k
      (indexedTerm k sourceLength r targetLength sourceTail targetBits i) := by
  rcases i with i | i
  · have hCases : i.1 = 0 ∨ i.1 = 1 := by omega
    rcases hCases with hZero | hOne
    · have hi : i = (⟨0, by decide⟩ : Fin 2) := by
        apply Fin.ext
        exact hZero
      subst i
      simp [indexedTerm, IsTwoLayerAt, negOne, neg]
    · have hi : i = (⟨1, by decide⟩ : Fin 2) := by
        apply Fin.ext
        exact hOne
      subst i
      simp [indexedTerm, IsTwoLayerAt, negThree, neg]
  · exact evenTerms_twoLayer (List.get_mem _ _)

end BlockSparseSUnit

/--
定数 `C0` の two-sided signed sparse `3^k` bound を仮定すると、
coefficient/target defect `A,B` から block depth の冪型上界を得る。
-/
theorem blockDepth_lt_twoSidedSparseEnvelope
    {C0 A B k r u x y : ℕ}
    (hSparse : TwoSidedSignedSparsePow3WithConstant C0)
    (hBlock : BlockData k r u x y)
    (hSourceDefect : Binary.HasZeroDefectAtMost u A)
    (hTargetDefect : Binary.HasZeroDefectAtMost y B) :
    k < twoSidedSparseEnvelope C0 (A + B + 5) := by
  rcases hSourceDefect.exists_sparseComplement with
    ⟨sourceLength, sourceBits, hSourceLen, hSourceCount, hSourceEq⟩
  rcases hTargetDefect.exists_sparseComplement with
    ⟨targetLength, targetBits, hTargetLen, hTargetCount, hTargetEq⟩
  rcases BlockSparseSUnit.sourceBits_eq_false_cons
      hBlock hSourceLen hSourceEq with
    ⟨sourceTail, hSourceBits⟩
  subst sourceBits
  let term := BlockSparseSUnit.indexedTerm
    k sourceLength r targetLength sourceTail targetBits
  let three := BlockSparseSUnit.threeIndex
    k sourceLength r targetLength sourceTail targetBits
  rcases BlockSparseSUnit.exists_nondegenerateCertificate
      hBlock hSourceLen hSourceEq hTargetEq with
    ⟨selected, hCard, hNondegenerate, hThreeMem⟩
  apply hSparse (A + B + 5) term selected k
  · calc
      selected.card ≤
          Binary.oneCount sourceTail + Binary.oneCount targetBits + 5 := hCard
      _ ≤ A + B + 5 := by
        have hSourceCount' : Binary.oneCount sourceTail ≤ A := by
          simpa [Binary.oneCount] using hSourceCount
        omega
  · simpa [term] using hNondegenerate
  · refine ⟨three, ?_, ?_⟩
    · simpa [three] using hThreeMem
    · simp [term, three]
  · intro i hi
    exact BlockSparseSUnit.indexedTerm_twoLayer
      k sourceLength r targetLength sourceTail targetBits i

/-- source 本体 `x` の defect を使う直接版。 -/
theorem blockDepth_lt_twoSidedSparseEnvelope_sourceTarget
    {C0 A B k r u x y : ℕ}
    (hSparse : TwoSidedSignedSparsePow3WithConstant C0)
    (hBlock : BlockData k r u x y)
    (hSourceDefect : Binary.HasZeroDefectAtMost x A)
    (hTargetDefect : Binary.HasZeroDefectAtMost y B) :
    k < twoSidedSparseEnvelope C0 (A + B + 5) := by
  exact blockDepth_lt_twoSidedSparseEnvelope hSparse hBlock
    (hBlock.coefficient_hasZeroDefectAtMost hSourceDefect)
    hTargetDefect

/--
`TwoSidedSignedSparsePow3` が成立するなら、ある絶対定数 `C0` で
すべての source/target bounded-defect block に同じ冪型 bound が使える。
-/
theorem exists_absolute_twoSidedSparse_blockDepth_bound
    (hSparse : TwoSidedSignedSparsePow3) :
    ∃ C0 : ℕ,
      ∀ A B k r u x y : ℕ,
        BlockData k r u x y →
        Binary.HasZeroDefectAtMost x A →
        Binary.HasZeroDefectAtMost y B →
        k < twoSidedSparseEnvelope C0 (A + B + 5) := by
  rcases hSparse with ⟨C0, hC0⟩
  refine ⟨C0, ?_⟩
  intro A B k r u x y hBlock hSource hTarget
  exact blockDepth_lt_twoSidedSparseEnvelope_sourceTarget
    hC0 hBlock hSource hTarget

end Mersenne
end Collatz3
