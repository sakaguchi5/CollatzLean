import CollatzLean.Collatz3.Mersenne.BoundedBlockSUnitReduction
import CollatzLean.Collatz3.Mersenne.SourceDefectBridge
import CollatzLean.Collatz3.Arithmetic.TwoThreeUnitQuantitative

/-!
# Collatz3 Mersenne: defect bound から block depth の定量上界

既存の `BoundedBlockDefectEscape` は

`source defect ≤ A`, `target defect ≤ B`

から `∃ K, k < K` を得る存在形だった。

このファイルでは定量 `{2,3}`-unit interface
`NondegenerateTwoThreeUnitExponentBoundBy F`
を使い、同じ reduction から直接

`k < F (A + B + 5)`

を得る。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic
open Arithmetic.SignedTwoThreeUnit

/--
coefficient `u` の defect が `A` 以下、target `y` の defect が `B` 以下なら、
block depth は `F (A+B+5)` 未満。
-/
theorem blockDepth_lt_defectBound
    {F : ℕ → ℕ}
    (hF : NondegenerateTwoThreeUnitExponentBoundBy F)
    {A B k r u x y : ℕ}
    (hBlock : BlockData k r u x y)
    (hSourceDefect : Binary.HasZeroDefectAtMost u A)
    (hTargetDefect : Binary.HasZeroDefectAtMost y B) :
    k < F (A + B + 5) := by
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
  apply hF (A + B + 5) term selected k
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
source 本体 `x` の defect bound から読める直接版。

`SourceDefectBridge` により `x` の defect bound を coefficient `u` へ移し、
同じ `F (A+B+5)` をそのまま使う。
-/
theorem blockDepth_lt_sourceTargetDefectBound
    {F : ℕ → ℕ}
    (hF : NondegenerateTwoThreeUnitExponentBoundBy F)
    {A B k r u x y : ℕ}
    (hBlock : BlockData k r u x y)
    (hSourceDefect : Binary.HasZeroDefectAtMost x A)
    (hTargetDefect : Binary.HasZeroDefectAtMost y B) :
    k < F (A + B + 5) := by
  exact blockDepth_lt_defectBound hF hBlock
    (hBlock.coefficient_hasZeroDefectAtMost hSourceDefect)
    hTargetDefect

/--
既存の存在版 ESS interface から classical choice した bound function に対しても、
定量式 `k < F(A+B+5)` をそのまま読める。

ただし、この chosen function 自体には explicit growth rate は付いていない。
-/
theorem blockDepth_lt_chosenDefectBound
    (hSUnit : NondegenerateTwoThreeUnitExponentBound)
    {A B k r u x y : ℕ}
    (hBlock : BlockData k r u x y)
    (hSourceDefect : Binary.HasZeroDefectAtMost x A)
    (hTargetDefect : Binary.HasZeroDefectAtMost y B) :
    k < chosenTwoThreeUnitExponentBound hSUnit (A + B + 5) := by
  exact blockDepth_lt_sourceTargetDefectBound
    (chosenTwoThreeUnitExponentBound_spec hSUnit)
    hBlock hSourceDefect hTargetDefect

end Mersenne
end Collatz3
