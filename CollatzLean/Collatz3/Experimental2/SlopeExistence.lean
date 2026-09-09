import CollatzLean.Collatz3.Experimental2.RoofCore
import CollatzLean.Collatz3.Experimental2.SlopeWindow
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: unit-carry roof の slope 存在と一意性

exact slope を `noncomputable def` として保存しない。

`HasUnitCarry β` から

`∃! σ, IsRoofSlope β σ`

を直接証明し、Real の上限 `sSup` は存在証明の内部でのみ用いる。
-/

namespace Collatz3
namespace Experimental2

namespace HasUnitCarry

/-- 共通倍数比較から得る direct roof の cross inequality。 -/
theorem roof_cross_mul_lt
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {m n : ℕ}
    (hm : 0 < m) :
    n * β m < m * (β n + 1) := by
  have h := U.below_criticalChord (m := n) (r := m) hm
  simpa [criticalDepth, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h

/--
unit-carry roof は slope window を満たす実数を持つ。

lower ratio 全体の `sSup` を証明内部の witness として使う。
-/
theorem exists_roofSlope
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∃ σ : ℝ, IsRoofSlope β σ := by
  let A : Set ℝ :=
    {x | ∃ n : ℕ, 0 < n ∧
      x = (β n : ℝ) / (n : ℝ)}
  have hA_nonempty : A.Nonempty := by
    refine ⟨(β 1 : ℝ), ?_⟩
    refine ⟨1, by omega, ?_⟩
    norm_num
  have hCross :
      ∀ {m n : ℕ}, 0 < m → 0 < n →
        (β m : ℝ) / (m : ℝ) <
          ((β n : ℝ) + 1) / (n : ℝ) := by
    intro m n hm hn
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hNat := U.roof_cross_mul_lt (m := m) (n := n) hm
    have hCast :
        (n : ℝ) * (β m : ℝ) <
          (m : ℝ) * ((β n : ℝ) + 1) := by
      exact_mod_cast hNat
    apply (div_lt_div_iff₀ hmR hnR).2
    nlinarith
  have hA_bdd : BddAbove A := by
    refine ⟨(β 1 : ℝ) + 1, ?_⟩
    intro x hx
    rcases hx with ⟨m, hm, rfl⟩
    have h := hCross hm (n := 1) (by omega)
    simpa using le_of_lt h
  refine ⟨sSup A, ?_⟩
  intro n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hLowerRatio :
      (β n : ℝ) / (n : ℝ) ≤ sSup A := by
    apply le_csSup hA_bdd
    exact ⟨n, hn, rfl⟩
  have hUpperRatio :
      sSup A ≤ ((β n : ℝ) + 1) / (n : ℝ) := by
    apply csSup_le hA_nonempty
    intro x hx
    rcases hx with ⟨m, hm, rfl⟩
    exact le_of_lt (hCross hm hn)
  constructor
  · have h := (div_le_iff₀ hnR).mp hLowerRatio
    nlinarith
  · have h := (le_div_iff₀ hnR).mp hUpperRatio
    nlinarith

/-- slope は存在し、しかも一意。 -/
theorem existsUnique_roofSlope
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∃! σ : ℝ, IsRoofSlope β σ := by
  obtain ⟨σ, Sσ⟩ := U.exists_roofSlope
  refine ⟨σ, Sσ, ?_⟩
  intro τ Sτ
  exact roofSlope_unique Sτ Sσ

end HasUnitCarry

/-- 任意の roof slope は `β(1)` と `β(1)+1` の間にある。 -/
theorem roofSlope_mem_anchorInterval
    {β : ℕ → ℕ}
    {σ : ℝ}
    (S : IsRoofSlope β σ) :
    (β 1 : ℝ) ≤ σ ∧ σ ≤ (β 1 : ℝ) + 1 := by
  simpa using S 1 (by omega)

end Experimental2
end Collatz3
