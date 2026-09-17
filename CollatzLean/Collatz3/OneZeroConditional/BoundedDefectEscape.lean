import CollatzLean.Collatz3.OneZeroConditional.StableDefectGrowth
import CollatzLean.Collatz3.OneZeroConditional.Pow3RunGrowth
import CollatzLean.Collatz3.OneZeroConditional.SparseWindowGrowth


/-!
# Collatz3 OneZeroConditional: one-zero bounded-defect escape

stable / overlap / periodic の三領域で eventual escape が得られれば、
one-zero family 全体で固定 target defect を保った Mersenne depth `k` は一様有界になる。

ここが C1 の統合定理。
三つの外部入力はすべて `Prop` interface であり、`axiom` は使わない。
-/

namespace Collatz3
namespace OneZeroConditional

/-- one-zero family 全体での bounded-defect eventual escape。 -/
def BoundedDefectEscape : Prop :=
  ∀ B : ℕ,
    ∃ K : ℕ,
      ∀ k n y : ℕ,
        K ≤ k →
        Mersenne.OneZeroExit k n y →
        Binary.HasZeroDefectAtMost y B →
        False

/-- 三領域の escape interface を束ねると global one-zero escape が得られる。 -/
theorem boundedDefectEscape_of_regions
    (hStable : StableDefectGrowth)
    (hOverlap : Pow3RunGrowth)
    (hPeriodic : SparseWindowGrowth) :
    BoundedDefectEscape := by
  intro B
  rcases hStable B with ⟨Ks, hKs⟩
  rcases hOverlap B with ⟨Ko, hKo⟩
  rcases hPeriodic B with ⟨Kp, hKp⟩
  let K : ℕ := max Ks (max Ko Kp)
  refine ⟨K, ?_⟩
  intro k n y hk hExit hDefect
  have hkS : Ks ≤ k := by
    dsimp [K] at hk
    omega
  have hkO : Ko ≤ k := by
    dsimp [K] at hk
    omega
  have hkP : Kp ≤ k := by
    dsimp [K] at hk
    omega
  rcases Mersenne.oneZeroRegion_trichotomy k n with hS | hRest
  · exact hKs k n y hkS hS hExit hDefect
  · rcases hRest with hO | hP
    · exact hKo k n y hkO hO hExit hDefect
    · exact hKp k n y hkP hP hExit hDefect

/--
global escape を通常の「`k < K(B)`」という有界性の形で読む。
-/
theorem exists_depth_bound
    (h : BoundedDefectEscape)
    (B : ℕ) :
    ∃ K : ℕ,
      ∀ k n y : ℕ,
        Mersenne.OneZeroExit k n y →
        Binary.HasZeroDefectAtMost y B →
        k < K := by
  rcases h B with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k n y hExit hDefect
  by_contra hNot
  have hk : K ≤ k := by omega
  exact hK k n y hk hExit hDefect

end OneZeroConditional
end Collatz3
