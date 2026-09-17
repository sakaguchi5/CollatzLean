import CollatzLean.Collatz3.Mersenne.OneZeroSparseComplement
import CollatzLean.Collatz3.OneZeroConditional.BoundedDefectEscape


/-!
# Collatz3 OneZeroConditional: sparse-complement equation から直接 escape する interface

三領域分割とは別ルートで、前半で得た exact equation

`3^k(2^n-1) + 2^r*missing + 2^r = 2^(L+r) + 1`

を外部 S-unit / Baker 型数論へ直接渡すための最小 interface。

この `Prop` 自体は axiom ではない。
-/

namespace Collatz3
namespace OneZeroConditional

/--
固定 sparsity bound `B` では sparse-complement equation の `k` が一様有界、という外部入力。
-/
def SparseComplementEquationEscape : Prop :=
  ∀ B : ℕ,
    ∃ K : ℕ,
      ∀ k n r length : ℕ,
        ∀ missingBits : List Bool,
          0 < r →
          missingBits.length = length →
          Binary.oneCount missingBits ≤ B →
          3 ^ k * (2 ^ n - 1) +
              2 ^ r * Binary.valueLSB missingBits + 2 ^ r =
            2 ^ (length + r) + 1 →
          k < K

/-- sparse equation の一様有界性だけで global one-zero bounded-defect escape が従う。 -/
theorem boundedDefectEscape_of_sparseComplementEquation
    (hSparse : SparseComplementEquationEscape) :
    BoundedDefectEscape := by
  unfold BoundedDefectEscape
  intro B
  rcases hSparse B with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k n y hk hExit hDefect
  rcases hExit.exists_sparseComplementEquation hDefect with
    ⟨r, length, missingBits, hr, hy, hLen, hCount, hEq⟩
  have hlt : k < K :=
    hK k n r length missingBits hr hLen hCount hEq
  omega

/-- sparse-equation route から通常の depth bound を直接読む。 -/
theorem exists_depth_bound_of_sparseComplementEquation
    (hSparse : SparseComplementEquationEscape)
    (B : ℕ) :
    ∃ K : ℕ,
      ∀ k n y : ℕ,
        Mersenne.OneZeroExit k n y →
        Binary.HasZeroDefectAtMost y B →
        k < K := by
  exact exists_depth_bound
    (boundedDefectEscape_of_sparseComplementEquation hSparse) B

end OneZeroConditional
end Collatz3
