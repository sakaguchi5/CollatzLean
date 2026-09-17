import CollatzLean.Collatz3.OneZeroConditional.Basic


/-!
# Collatz3 OneZeroConditional: region escape の derived calculus

既存 `EventualRegionEscape` の論理演算だけをまとめる。
新しい number-theory 仮定は導入しない。
-/

namespace Collatz3
namespace OneZeroConditional

/-- fixed defect bound `B` と threshold `K` における region escape。 -/
def RegionEscapeAt
    (region : ℕ → ℕ → Prop)
    (B K : ℕ) : Prop :=
  ∀ k n y : ℕ,
    K ≤ k →
    region k n →
    Mersenne.OneZeroExit k n y →
    Binary.HasZeroDefectAtMost y B →
    False

/-- `EventualRegionEscape` は各 `B` に threshold が存在することそのもの。 -/
theorem eventualRegionEscape_iff
    (region : ℕ → ℕ → Prop) :
    EventualRegionEscape region ↔
      ∀ B : ℕ, ∃ K : ℕ, RegionEscapeAt region B K := by
  rfl

namespace RegionEscapeAt

/-- threshold を大きくしても escape は保存される。 -/
theorem threshold_mono
    {R : ℕ → ℕ → Prop} {B K K' : ℕ}
    (h : RegionEscapeAt R B K)
    (hKK : K ≤ K') :
    RegionEscapeAt R B K' := by
  intro k n y hk hR hExit hDefect
  exact h k n y (le_trans hKK hk) hR hExit hDefect

/-- defect bound を小さくすれば同じ threshold で escape する。 -/
theorem defect_antitone
    {R : ℕ → ℕ → Prop} {A B K : ℕ}
    (h : RegionEscapeAt R B K)
    (hAB : A ≤ B) :
    RegionEscapeAt R A K := by
  intro k n y hk hR hExit hDefect
  exact h k n y hk hR hExit (hDefect.mono hAB)

end RegionEscapeAt

namespace EventualRegionEscape

/-- 二つの region で eventual escape すれば、その和集合でも eventual escape。 -/
theorem union
    {R S : ℕ → ℕ → Prop}
    (hR : EventualRegionEscape R)
    (hS : EventualRegionEscape S) :
    EventualRegionEscape (fun k n => R k n ∨ S k n) := by
  intro B
  rcases hR B with ⟨KR, hKR⟩
  rcases hS B with ⟨KS, hKS⟩
  refine ⟨max KR KS, ?_⟩
  intro k n y hk hRegion hExit hDefect
  have hkR : KR ≤ k := by omega
  have hkS : KS ≤ k := by omega
  rcases hRegion with hRegionR | hRegionS
  · exact hKR k n y hkR hRegionR hExit hDefect
  · exact hKS k n y hkS hRegionS hExit hDefect

/-- region が常に偽なら自明に eventual escape。 -/
theorem falseRegion :
    EventualRegionEscape (fun _ _ => False) := by
  intro B
  refine ⟨0, ?_⟩
  intro k n y hk hFalse hExit hDefect
  exact hFalse

end EventualRegionEscape

end OneZeroConditional
end Collatz3
