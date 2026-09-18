import CollatzLean.Collatz3.Mersenne.BoundedBlockSUnitReduction
import CollatzLean.Collatz3.Arithmetic.TwoSidedSignedSparsePow3

/-!
# Collatz3 Mersenne: exact block-sparse equation と hole complexity

定量化では generic S-unit equation へ早く移りすぎると、Collatz block 固有の
符号・top term・hole 配置を失う。

そこでこのファイルでは、`BlockData` と source/target の sparse complement から得られる
exact equation

`-1 - 3^k + 2^n 3^k - 3^k S + 2^r T + 2^r - 2^(L+r) = 0`

をそのまま保持する。

`S` と `T` の one-count の和を hole complexity とみなし、

`G(k) ≤ holes`

を将来の定量数論 target とする。
概念的な第一目標は `G(k) ≍ log k / log log k` だが、ここでは具体式を仮定しない。

既存 ESS 型仮定からは qualitative に
「holes を固定したまま `k` を arbitrarily large にできない」ことまで証明する。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic
open Arithmetic.SignedTwoThreeUnit

/--
coefficient `u` と endpoint `y` が、合計 `D` 個以下の missing bits を持つ
sparse-complement representation を持つ。
-/
def SparseEndpointComplementsAtMost
    (u y D : ℕ) : Prop :=
  ∃ sourceLength targetLength : ℕ,
    ∃ sourceBits targetBits : List Bool,
      sourceBits.length = sourceLength ∧
      targetBits.length = targetLength ∧
      Binary.oneCount sourceBits + Binary.oneCount targetBits ≤ D ∧
      u + Binary.valueLSB sourceBits + 1 = 2 ^ sourceLength ∧
      y + Binary.valueLSB targetBits + 1 = 2 ^ targetLength

namespace SparseEndpointComplementsAtMost

/-- hole bound を大きくしても sparse-complement witness は保存される。 -/
theorem mono
    {u y D E : ℕ}
    (h : SparseEndpointComplementsAtMost u y D)
    (hDE : D ≤ E) :
    SparseEndpointComplementsAtMost u y E := by
  rcases h with
    ⟨sourceLength, targetLength, sourceBits, targetBits,
      hSourceLen, hTargetLen, hCount, hSourceEq, hTargetEq⟩
  exact ⟨sourceLength, targetLength, sourceBits, targetBits,
    hSourceLen, hTargetLen, le_trans hCount hDE, hSourceEq, hTargetEq⟩

end SparseEndpointComplementsAtMost

/--
BlockData から現れる exact two-sided sparse equation。

source 側は `3^k` layer、target 側は pure dyadic layer で、
`sourceTail` / `targetBits` がそれぞれ missing positions を表す。
-/
structure ExactBlockSparseEquation
    (k sourceLength r targetLength : ℕ)
    (sourceTail targetBits : List Bool) : Prop where
  sourceLength_pos : 0 < sourceLength
  exitDepth_pos : 0 < r
  equation :
    (-1 : ℤ) - (3 : ℤ) ^ k +
        (2 : ℤ) ^ sourceLength * (3 : ℤ) ^ k -
        (3 : ℤ) ^ k *
          (Binary.valueLSB (false :: sourceTail) : ℤ) +
        (2 : ℤ) ^ r * (Binary.valueLSB targetBits : ℤ) +
        (2 : ℤ) ^ r -
        (2 : ℤ) ^ (targetLength + r) = 0

/--
深さ `k` の exact block-sparse equation は、最低 `G k` 個の holes を必要とする。

これは quantitative route の中心 target。
一般 two-layer S-unit equation より狭く、実際の BlockData の符号構造を保持する。
-/
def BlockSparsePow3LowerBound
    (G : ℕ → ℕ) : Prop :=
  ∀ k sourceLength r targetLength : ℕ,
    ∀ sourceTail targetBits : List Bool,
      ExactBlockSparseEquation
        k sourceLength r targetLength sourceTail targetBits →
      G k ≤ Binary.oneCount sourceTail + Binary.oneCount targetBits

/--
fixed hole complexity `D` の exact block-sparse equationでは、depth は一様有界。
-/
def BlockSparsePow3Escape : Prop :=
  ∀ D : ℕ,
    ∃ K : ℕ,
      ∀ k sourceLength r targetLength : ℕ,
        ∀ sourceTail targetBits : List Bool,
          ExactBlockSparseEquation
            k sourceLength r targetLength sourceTail targetBits →
          Binary.oneCount sourceTail + Binary.oneCount targetBits ≤ D →
          k < K

namespace BlockSparseSUnit

/--
exact block-sparse equation だけから univ `{2,3}`-unit zero-sum を復元する。
`BlockData` 自体は不要。
-/
theorem indexedTerm_univ_sum_zero_of_exactEquation
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hEq : ExactBlockSparseEquation
      k sourceLength r targetLength sourceTail targetBits) :
    Finset.sum
        (Finset.univ : Finset
          (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits))
        (fun i =>
          (indexedTerm k sourceLength r targetLength sourceTail targetBits i).value) = 0 := by
  rw [Fintype.sum_sum_type, Fin.sum_univ_two]
  simp [indexedTerm, evenTerms_value_sum]
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hEq.equation

/--
exact block-sparse equation から、`-3^k` anchor を含む nondegenerate certificate を取る。

既存の `+5` 評価を一つ詰める。
`-1` を含む極小 zero-sum からその `-1` を erase しているため、
最終 certificate は univ より少なくとも1項小さく、

`card ≤ source holes + target holes + 4`

となる。
-/
theorem exists_nondegenerateCertificate_tight_of_exactEquation
    {k sourceLength r targetLength : ℕ}
    {sourceTail targetBits : List Bool}
    (hEq : ExactBlockSparseEquation
      k sourceLength r targetLength sourceTail targetBits) :
    ∃ selected : Finset
        (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits),
      selected.card ≤
        Binary.oneCount sourceTail + Binary.oneCount targetBits + 4 ∧
      NondegenerateSumOne
        (fun i =>
          (indexedTerm k sourceLength r targetLength sourceTail targetBits i).value)
        selected ∧
      threeIndex k sourceLength r targetLength sourceTail targetBits ∈ selected := by
  classical
  let term := indexedTerm k sourceLength r targetLength sourceTail targetBits
  let three := threeIndex k sourceLength r targetLength sourceTail targetBits
  let one := oneIndex k sourceLength r targetLength sourceTail targetBits
  have hUnivZero :
      Vanishes
        (fun i => (term i).value)
        (Finset.univ : Finset
          (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits)) := by
    unfold Vanishes
    simpa [term] using
      indexedTerm_univ_sum_zero_of_exactEquation hEq
  rcases exists_anchorMinimalVanishing
      (v := fun i => (term i).value)
      three
      (s₀ := (Finset.univ : Finset
        (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits)))
      (by simp)
      hUnivZero with
    ⟨s, hsUniv, hMinimal⟩
  have hOne : one ∈ s := by
    apply vanishing_contains_one hEq.sourceLength_pos hEq.exitDepth_pos
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
  have hSelectedSub : selected ⊆ s := by
    intro i hi
    have hi' : i ∈ s.erase one := by
      simpa [selected] using hi
    exact (Finset.mem_erase.mp hi').2
  have hSelectedNe : selected ≠ s := by
    intro hEqSet
    have hOneSelected : one ∈ selected := by
      rw [hEqSet]
      exact hOne
    simp [selected] at hOneSelected
  have hProper : selected ⊂ s :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hSelectedSub, hSelectedNe⟩
  have hCardLt : selected.card < s.card :=
    Finset.card_lt_card hProper
  have hSCard :
      s.card ≤
        (Finset.univ : Finset
          (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits)).card :=
    Finset.card_le_card hsUniv
  have hUnivCard :
      (Finset.univ : Finset
          (BlockSparseIndex k sourceLength r targetLength sourceTail targetBits)).card =
        Binary.oneCount sourceTail + Binary.oneCount targetBits + 5 := by
    simpa only [Finset.card_univ] using
      blockSparseIndex_card k sourceLength r targetLength sourceTail targetBits
  refine ⟨selected, ?_, hNondegenerate, hThreeSelected⟩
  rw [hUnivCard] at hSCard
  omega

end BlockSparseSUnit

/--
`BlockData` と sparse endpoint complements から exact block-sparse equation を取り出す。

quantitative proof はここから先で `BlockData` の意味論を忘れてよい。
-/
theorem exists_exactBlockSparseEquation_of_sparseComplements
    {k r u x y D : ℕ}
    (hBlock : BlockData k r u x y)
    (hSparse : SparseEndpointComplementsAtMost u y D) :
    ∃ sourceLength targetLength : ℕ,
      ∃ sourceTail targetBits : List Bool,
        ExactBlockSparseEquation
          k sourceLength r targetLength sourceTail targetBits ∧
        Binary.oneCount sourceTail + Binary.oneCount targetBits ≤ D := by
  rcases hSparse with
    ⟨sourceLength, targetLength, sourceBits, targetBits,
      hSourceLen, hTargetLen, hCount, hSourceEq, hTargetEq⟩
  rcases BlockSparseSUnit.sourceBits_eq_false_cons
      hBlock hSourceLen hSourceEq with
    ⟨sourceTail, hSourceBits⟩
  subst sourceBits
  have hSourceLengthPos : 0 < sourceLength := by
    simp at hSourceLen
    omega
  have hCount' :
      Binary.oneCount sourceTail + Binary.oneCount targetBits ≤ D := by
    simpa [Binary.oneCount] using hCount
  refine ⟨sourceLength, targetLength, sourceTail, targetBits, ?_, hCount'⟩
  exact ⟨
    hSourceLengthPos,
    hBlock.exitDepth_pos,
    BlockSparseSUnit.blockEquation_int hBlock hSourceEq hTargetEq
  ⟩

/--
exact block-sparse lower bound `G` があれば、任意の BlockData sparse witness に対して
`G k ≤ D` を直接得る。
-/
theorem blockSparseLowerBound_of_sparseComplements
    {G : ℕ → ℕ}
    (hLower : BlockSparsePow3LowerBound G)
    {k r u x y D : ℕ}
    (hBlock : BlockData k r u x y)
    (hSparse : SparseEndpointComplementsAtMost u y D) :
    G k ≤ D := by
  rcases exists_exactBlockSparseEquation_of_sparseComplements hBlock hSparse with
    ⟨sourceLength, targetLength, sourceTail, targetBits, hEq, hCount⟩
  exact le_trans
    (hLower k sourceLength r targetLength sourceTail targetBits hEq)
    hCount

/--
既存 ESS 型 exponent bound から、exact block-sparse equation の fixed-hole escape を得る。

certificate 項数は hole 数 `D` に固定定数4を足しただけなので、
qualitative な `holes → ∞` が従う。
-/
theorem blockSparsePow3Escape_of_twoThreeUnitBound
    (hSUnit : NondegenerateTwoThreeUnitExponentBound) :
    BlockSparsePow3Escape := by
  intro D
  rcases hSUnit (D + 4) with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k sourceLength r targetLength sourceTail targetBits hEq hCount
  let term := BlockSparseSUnit.indexedTerm
    k sourceLength r targetLength sourceTail targetBits
  let three := BlockSparseSUnit.threeIndex
    k sourceLength r targetLength sourceTail targetBits
  rcases BlockSparseSUnit.exists_nondegenerateCertificate_tight_of_exactEquation hEq with
    ⟨selected, hCard, hNondegenerate, hThreeMem⟩
  apply hK term selected k
  · calc
      selected.card ≤
          Binary.oneCount sourceTail + Binary.oneCount targetBits + 4 := hCard
      _ ≤ D + 4 := by omega
  · simpa [term] using hNondegenerate
  · refine ⟨three, ?_, ?_⟩
    · simpa [three] using hThreeMem
    · simp [term, three]

/--
quantitative hole lower bound `G` が発散するなら、fixed-hole escape が従う。
-/
theorem BlockSparsePow3LowerBound.to_escape
    {G : ℕ → ℕ}
    (hLower : BlockSparsePow3LowerBound G)
    (hGrowth : NatTendsToInfinity G) :
    BlockSparsePow3Escape := by
  intro D
  rcases hGrowth D with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k sourceLength r targetLength sourceTail targetBits hEq hCount
  have hComplexity :
      G k ≤ Binary.oneCount sourceTail + Binary.oneCount targetBits :=
    hLower k sourceLength r targetLength sourceTail targetBits hEq
  by_contra hNot
  have hk : K ≤ k := by
    omega
  have hLarge : D < G k := hK k hk
  omega

end Mersenne
end Collatz3
