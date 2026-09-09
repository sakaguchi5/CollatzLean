import CollatzLean.Collatz3.Experimental2.SlopeExistence
import CollatzLean.Collatz3.Experimental2.RationalMechanical
import CollatzLean.Collatz3.Experimental2.MechanicalRoof
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: unit-carry roof と mechanical roof の特徴付け

`HasUnitCarry β` から exact Real slope をデータとして保存せず、

`∃! σ, IsRoofSlope β σ`

を得る。

その slope は irrational なら lower mechanical、
rational なら既約 `p/q` の lower / upper 二型に分かれる。

逆に lower / upper mechanical roof から `HasUnitCarry` を復元し、
最終的に存在形の iff を得る。
-/

namespace Collatz3
namespace Experimental2

namespace IsLowerMechanicalRoof

theorem hasUnitCarry
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ) :
    HasUnitCarry β := by
  have hBounds :
      ∀ a b : ℕ,
        β a + β b ≤ β (a + b) ∧
          β (a + b) ≤ β a + β b + 1 := by
    intro a b
    have hA := M a
    have hB := M b
    have hAB := M (a + b)
    have hSlopeAdd :
        ((a + b : ℕ) : ℝ) * σ =
          (a : ℝ) * σ + (b : ℝ) * σ := by
      push_cast
      ring
    have hLowerR :
        ((β a + β b : ℕ) : ℝ) <
          ((β (a + b) + 1 : ℕ) : ℝ) := by
      push_cast
      rw [hSlopeAdd] at hAB
      nlinarith [hA.1, hB.1, hAB.2]
    have hUpperR :
        (β (a + b) : ℝ) <
          ((β a + β b + 2 : ℕ) : ℝ) := by
      push_cast
      rw [hSlopeAdd] at hAB
      nlinarith [hA.2, hB.2, hAB.1]
    constructor
    · have h :
          β a + β b < β (a + b) + 1 := by
        exact_mod_cast hLowerR
      omega
    · have h :
          β (a + b) < β a + β b + 2 := by
        exact_mod_cast hUpperR
      omega
  unfold HasUnitCarry
  constructor
  · unfold IsSuperadditiveRoof
    intro a b
    exact (hBounds a b).1
  · unfold HasUnitUpperDefect
    intro a b
    exact (hBounds a b).2

end IsLowerMechanicalRoof

namespace IsUpperMechanicalRoof

theorem hasUnitCarry
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsUpperMechanicalRoof β σ) :
    HasUnitCarry β := by
  have hBounds :
      ∀ a b : ℕ,
        β a + β b ≤ β (a + b) ∧
          β (a + b) ≤ β a + β b + 1 := by
    intro a b
    by_cases ha : a = 0
    · subst a
      simp [M.1]
    by_cases hb : b = 0
    · subst b
      simp [M.1]
    have haPos : 0 < a := Nat.pos_of_ne_zero ha
    have hbPos : 0 < b := Nat.pos_of_ne_zero hb
    have habPos : 0 < a + b := by
      omega
    have hA := M.2 a haPos
    have hB := M.2 b hbPos
    have hAB := M.2 (a + b) habPos
    have hSlopeAdd :
        ((a + b : ℕ) : ℝ) * σ =
          (a : ℝ) * σ + (b : ℝ) * σ := by
      push_cast
      ring
    have hLowerR :
        ((β a + β b : ℕ) : ℝ) <
          ((β (a + b) + 1 : ℕ) : ℝ) := by
      push_cast
      rw [hSlopeAdd] at hAB
      nlinarith [hA.1, hB.1, hAB.2]
    have hUpperR :
        (β (a + b) : ℝ) <
          ((β a + β b + 2 : ℕ) : ℝ) := by
      push_cast
      rw [hSlopeAdd] at hAB
      nlinarith [hA.2, hB.2, hAB.1]
    constructor
    · have h :
          β a + β b < β (a + b) + 1 := by
        exact_mod_cast hLowerR
      omega
    · have h :
          β (a + b) < β a + β b + 2 := by
        exact_mod_cast hUpperR
      omega
  unfold HasUnitCarry
  constructor
  · unfold IsSuperadditiveRoof
    intro a b
    exact (hBounds a b).1
  · unfold HasUnitUpperDefect
    intro a b
    exact (hBounds a b).2

end IsUpperMechanicalRoof

namespace HasUnitCarry

/-- irrational roof slope なら lower mechanical。 -/
theorem lowerMechanical_of_irrational_roofSlope
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (S : IsRoofSlope β σ)
    (hIrr : Irrational σ) :
    IsLowerMechanicalRoof β σ := by
  intro n
  by_cases hn : n = 0
  · subst n
    simp [IsNatFloor, U.zero_eq]
  · exact isNatFloor_of_roofSlope_noIntegralMultiple
      S (irrational_hasNoIntegralMultiple hIrr)
      (Nat.pos_of_ne_zero hn)

/--
rational roof slope なら lower / upper mechanical のどちらか。

既約 `p/q` を内部で抽出し、分母 boundary の二型から全幅へ伝播する。
-/
theorem lower_or_upperMechanical_of_rational_roofSlope
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (S : IsRoofSlope β σ)
    (hNotIrr : ¬ Irrational σ) :
    IsLowerMechanicalRoof β σ ∨ IsUpperMechanicalRoof β σ := by
  have hσNonneg : 0 ≤ σ := by
    have h := (S 1 (by omega)).1
    norm_num at h
    exact le_trans (Nat.cast_nonneg (β 1)) h
  obtain ⟨p, q, hq, hCoprime, hSlope⟩ :=
    exists_reduced_nat_ratio_of_not_irrational_nonneg
      hNotIrr hσNonneg
  have Sscaled : IsScaledRationalSlope β p q := by
    rw [hSlope] at S
    exact roofSlope_to_scaledRational hq S
  rcases rationalSlope_denominator_two_boundary_types Sscaled with hLower | hUpper
  · left
    intro n
    by_cases hn : n = 0
    · subst n
      simp [IsNatFloor, U.zero_eq]
    · have hnPos := Nat.pos_of_ne_zero hn
      have hWindow := Sscaled.2 n hnPos
      have hStrict :=
        U.rationalLower_strictUpper Sscaled hCoprime hLower hnPos
      rw [hSlope]
      have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
      have hFrac :
          (n : ℝ) * ((p : ℝ) / (q : ℝ)) =
            ((n * p : ℕ) : ℝ) / (q : ℝ) := by
        push_cast
        ring
      rw [hFrac]
      constructor
      · apply (le_div_iff₀ hqR).2
        exact_mod_cast (show β n * q ≤ n * p by
          simpa [Nat.mul_comm] using hWindow.1)
      · apply (div_lt_iff₀ hqR).2
        exact_mod_cast (show n * p < (β n + 1) * q by
          simpa [Nat.mul_comm] using hStrict)
  · right
    refine ⟨U.zero_eq, ?_⟩
    intro n hnPos
    have hWindow := Sscaled.2 n hnPos
    have hStrict :=
      U.rationalUpper_strictLower Sscaled hCoprime hUpper hnPos
    rw [hSlope]
    have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
    have hFrac :
        (n : ℝ) * ((p : ℝ) / (q : ℝ)) =
          ((n * p : ℕ) : ℝ) / (q : ℝ) := by
      push_cast
      ring
    rw [hFrac]
    constructor
    · apply (lt_div_iff₀ hqR).2
      exact_mod_cast (show β n * q < n * p by
        simpa [Nat.mul_comm] using hStrict)
    · apply (div_le_iff₀ hqR).2
      exact_mod_cast (show n * p ≤ (β n + 1) * q by
        simpa [Nat.mul_comm] using hWindow.2)

/-- 任意の roof slope は lower / upper mechanical のどちらか。 -/
theorem lower_or_upperMechanical_of_roofSlope
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (S : IsRoofSlope β σ) :
    IsLowerMechanicalRoof β σ ∨ IsUpperMechanicalRoof β σ := by
  classical
  by_cases hIrr : Irrational σ
  · exact Or.inl (U.lowerMechanical_of_irrational_roofSlope S hIrr)
  · exact U.lower_or_upperMechanical_of_rational_roofSlope S hIrr

/-- unit-carry roof は何らかの lower / upper mechanical slope を持つ。 -/
theorem exists_lower_or_upperMechanicalRoof
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∃ σ : ℝ,
      IsLowerMechanicalRoof β σ ∨
        IsUpperMechanicalRoof β σ := by
  obtain ⟨σ, S⟩ := U.exists_roofSlope
  exact ⟨σ, U.lower_or_upperMechanical_of_roofSlope S⟩

end HasUnitCarry

/-- 最終特徴付け: unit-carry roof と mechanical roof の存在は同値。 -/
theorem hasUnitCarry_iff_exists_mechanicalRoof
    {β : ℕ → ℕ} :
    HasUnitCarry β ↔
      ∃ σ : ℝ,
        IsLowerMechanicalRoof β σ ∨
          IsUpperMechanicalRoof β σ := by
  constructor
  · intro U
    exact U.exists_lower_or_upperMechanicalRoof
  · rintro ⟨σ, hLower | hUpper⟩
    · exact hLower.hasUnitCarry
    · exact hUpper.hasUnitCarry

end Experimental2
end Collatz3
