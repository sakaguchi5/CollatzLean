import CollatzLean.Collatz3.OneZeroConditional.BoundedDefectEscape


/-!
# Collatz3 OneZeroConditional: global escape の sequence-level consequences

`BoundedDefectEscape` を、候補 family の Mersenne depth が一様有界であるという形へ読み替える。
新しい数論仮定は導入しない。
-/

namespace Collatz3
namespace OneZeroConditional

/-- depth sequence が cofinal、すなわち任意の threshold 以上へ到達する。 -/
def DepthCofinal (k : ℕ → ℕ) : Prop :=
  ∀ K : ℕ, ∃ i : ℕ, K ≤ k i

/--
global bounded-defect escape の下では、固定 defect bound を満たす任意の one-zero family の
Mersenne depth は一つの `K` で一様に抑えられる。
-/
theorem family_depth_bounded
    (hEscape : BoundedDefectEscape)
    (B : ℕ)
    (k n y : ℕ → ℕ)
    (hExit : ∀ i : ℕ, Mersenne.OneZeroExit (k i) (n i) (y i))
    (hDefect : ∀ i : ℕ, Binary.HasZeroDefectAtMost (y i) B) :
    ∃ K : ℕ, ∀ i : ℕ, k i < K := by
  rcases exists_depth_bound hEscape B with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro i
  exact hK (k i) (n i) (y i) (hExit i) (hDefect i)

/--
固定 bounded defect を保つ one-zero exit family の depth は cofinal にはなれない。
-/
theorem no_cofinal_boundedDefect_family
    (hEscape : BoundedDefectEscape)
    (B : ℕ)
    (k n y : ℕ → ℕ)
    (hExit : ∀ i : ℕ, Mersenne.OneZeroExit (k i) (n i) (y i))
    (hDefect : ∀ i : ℕ, Binary.HasZeroDefectAtMost (y i) B) :
    ¬ DepthCofinal k := by
  intro hCofinal
  rcases family_depth_bounded hEscape B k n y hExit hDefect with
    ⟨K, hBound⟩
  rcases hCofinal K with ⟨i, hi⟩
  have hlt := hBound i
  omega

end OneZeroConditional
end Collatz3
