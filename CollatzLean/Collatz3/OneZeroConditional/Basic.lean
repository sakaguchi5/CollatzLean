import CollatzLean.Collatz3.Mersenne.OneZeroRegions

/-!
# Collatz3 OneZeroConditional: region escape の薄い共通 interface

固定 defect bound `B` に対し、指定 region 内で十分大きい Mersenne depth `k` を
one-zero macro exit が持てない、という eventual escape property だけを抽象化する。

これは axiom ではなく単なる `Prop` interface。
外部 number theory を後で形式化したとき、この `Prop` を theorem として埋めればよい。
-/

namespace Collatz3
namespace OneZeroConditional

/-- one-zero exit に対する generic eventual region escape property。 -/
def EventualRegionEscape
    (region : ℕ → ℕ → Prop) : Prop :=
  ∀ B : ℕ,
    ∃ K : ℕ,
      ∀ k n y : ℕ,
        K ≤ k →
        region k n →
        Mersenne.OneZeroExit k n y →
        Binary.HasZeroDefectAtMost y B →
        False

namespace EventualRegionEscape

/-- region を狭めれば escape property は保存される。 -/
theorem mono
    {R S : ℕ → ℕ → Prop}
    (h : EventualRegionEscape R)
    (hSub : ∀ k n, S k n → R k n) :
    EventualRegionEscape S := by
  intro B
  rcases h B with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k n y hk hS hExit hDefect
  exact hK k n y hk (hSub k n hS) hExit hDefect

end EventualRegionEscape

end OneZeroConditional
end Collatz3
