import CollatzLean.Collatz3.Mersenne.BoundedBlockSUnitReduction

/-!
# Collatz3 Mersenne: bounded block defect escape

一般 `BlockData`

`x + 1 = 2^k * u`
`2^r * y + 1 = 3^k * u`

について、source coefficient `u` と endpoint `y` の binary zero defect を
それぞれ固定上限 `A`, `B` に抑えたまま、block depth `k` を無限に大きくできない、
という一般 obstruction を定義して証明する。

one-zero の `u = 2^n - 1` や Region I/II/III の領域分割は使わない。
外部の深い数論入力は既存の
`Arithmetic.NondegenerateTwoThreeUnitExponentBound`
だけである。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic
open Arithmetic.SignedTwoThreeUnit

/--
source coefficient defect `A` と target defect `B` を固定すると、
一般 Mersenne block depth `k` は一様有界、という性質。
-/
def BoundedBlockDefectEscape : Prop :=
  ∀ A B : ℕ,
    ∃ K : ℕ,
      ∀ k r u x y : ℕ,
        BlockData k r u x y →
        Binary.HasZeroDefectAtMost u A →
        Binary.HasZeroDefectAtMost y B →
        k < K

/--
ESS 型の固定項数 `{2,3}`-unit exponent bound から、
一般 `BoundedBlockDefectEscape` が従う。

source/target の sparse complement を合わせた certificate の項数は
高々 `A + B + 5`。
-/
theorem boundedBlockDefectEscape_of_twoThreeUnitBound
    (hSUnit : NondegenerateTwoThreeUnitExponentBound) :
    BoundedBlockDefectEscape := by
  intro A B
  rcases hSUnit (A + B + 5) with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k r u x y hBlock hSourceDefect hTargetDefect
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
  apply hK term selected k
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

/--
ESS 型入力から、指定した defect bounds `A,B` に対する block depth bound を直接読む。
-/
theorem exists_blockDepth_bound_of_twoThreeUnitBound
    (hSUnit : NondegenerateTwoThreeUnitExponentBound)
    (A B : ℕ) :
    ∃ K : ℕ,
      ∀ k r u x y : ℕ,
        BlockData k r u x y →
        Binary.HasZeroDefectAtMost u A →
        Binary.HasZeroDefectAtMost y B →
        k < K := by
  exact boundedBlockDefectEscape_of_twoThreeUnitBound hSUnit A B

end Mersenne
end Collatz3
