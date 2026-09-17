import CollatzLean.Collatz3.OneZeroConditional.SparseEquationEscape
import CollatzLean.Collatz3.Mersenne.OneZeroSUnitReduction

/-!
# Collatz3 OneZeroConditional: ESS 型 `{2,3}`-unit finiteness から sparse escape へ

Collatz 側の reduction は `Mersenne.OneZeroSUnitReduction` で無条件に完了している。
このファイルでは、外部数論入力を

`Arithmetic.NondegenerateTwoThreeUnitExponentBound`

の一つだけに縮約し、既存 `SparseComplementEquationEscape` を導く。

想定する数学的供給源は Evertse--Schlickewei--Schmidt 型の
nondegenerate S-unit equation finiteness。
この interface 自体は axiom ではない。
-/

namespace Collatz3
namespace OneZeroConditional

open Arithmetic
open Arithmetic.SignedTwoThreeUnit

/--
固定項数の nondegenerate `{2,3}`-unit exponent bound だけで、
既存 sparse-complement escape interface が従う。
-/
theorem sparseComplementEquationEscape_of_twoThreeUnitBound
    (hSUnit : NondegenerateTwoThreeUnitExponentBound) :
    SparseComplementEquationEscape := by
  intro B
  rcases hSUnit (B + 5) with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k n r length missingBits hr hLength hCount hEq
  clear hLength
  let term := Mersenne.SparseSUnit.indexedTerm
    k n r length missingBits
  let three := Mersenne.SparseSUnit.threeIndex
    k n r length missingBits
  rcases Mersenne.SparseSUnit.exists_nondegenerateCertificate
      (k := k) (n := n) (r := r) (length := length)
      (bits := missingBits) hr hEq with
    ⟨selected, hCard, hNondegenerate, hThreeMem⟩
  apply hK term selected k
  · calc
      selected.card ≤ Binary.oneCount missingBits + 5 := hCard
      _ ≤ B + 5 := by omega
  · simpa [term] using hNondegenerate
  · refine ⟨three, ?_, ?_⟩
    · simpa [three] using hThreeMem
    · simp [term, three]

/-- ESS 型入力から global one-zero bounded-defect escape を直接得る。 -/
theorem boundedDefectEscape_of_twoThreeUnitBound
    (hSUnit : NondegenerateTwoThreeUnitExponentBound) :
    BoundedDefectEscape := by
  exact boundedDefectEscape_of_sparseComplementEquation
    (sparseComplementEquationEscape_of_twoThreeUnitBound hSUnit)

/-- ESS 型入力から通常の depth bound を読む。 -/
theorem exists_depth_bound_of_twoThreeUnitBound
    (hSUnit : NondegenerateTwoThreeUnitExponentBound)
    (B : ℕ) :
    ∃ K : ℕ,
      ∀ k n y : ℕ,
        Mersenne.OneZeroExit k n y →
        Binary.HasZeroDefectAtMost y B →
        k < K := by
  exact exists_depth_bound
    (boundedDefectEscape_of_twoThreeUnitBound hSUnit) B

end OneZeroConditional
end Collatz3
