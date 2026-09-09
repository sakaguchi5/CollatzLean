import CollatzLean.Collatz3.Experimental.CarryWordMechanicalFormula
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Collatz3 experimental: unit-carry roof と mechanical roof の特徴付け

ここまでの流れは

`HasUnitCarry β -> canonical slope -> mechanical residual`

という片方向だった。
このファイルでは逆向きを証明し、`HasUnitCarry` 自体を mechanical geometry で特徴付ける。

lower mechanical cell は

`k ≤ nρ < k+1`

upper mechanical cell は

`k < nρ ≤ k+1`

である。

linear part `n*a` とこれらの residual cell から、加法誤差が必ず `0` または `1` に収まることを
直接示す。したがって mechanical 表現は unit-carry の consequence であるだけでなく、
逆に unit-carry を再構成する十分条件でもある。
-/

namespace Collatz3
namespace Experimental

/--
lower mechanical roof。

各幅 `n` で `β(n)` を `n*a + k` と分解でき、
residual `k` が `nρ` の通常の floor cell に入る。
-/
def IsLowerMechanicalRoof
    (β : ℕ → ℕ)
    (a : ℕ)
    (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧
    ∀ n : ℕ,
      ∃ k : ℕ,
        β n = n * a + k ∧
          IsNatFloor k ((n : ℝ) * ρ)

/--
upper mechanical roof。

`n=0` では `β(0)=0`、正幅では residual が upper cell
`k < nρ ≤ k+1` に入る。
-/
def IsUpperMechanicalRoof
    (β : ℕ → ℕ)
    (a : ℕ)
    (ρ : ℝ) : Prop :=
  0 ≤ ρ ∧
    β 0 = 0 ∧
      ∀ n : ℕ, 0 < n →
        ∃ k : ℕ,
          β n = n * a + k ∧
            IsNatUpperCell k ((n : ℝ) * ρ)

namespace IsLowerMechanicalRoof

/-- lower mechanical roof は concrete な `Nat.floor` 公式そのもの。 -/
theorem eq_linear_add_natFloor
    {β : ℕ → ℕ}
    {a : ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β a ρ)
    (n : ℕ) :
    β n = n * a + ⌊(n : ℝ) * ρ⌋₊ := by
  obtain ⟨k, hBeta, hCell⟩ := M.2 n
  have hNonneg : 0 ≤ (n : ℝ) * ρ := by
    exact mul_nonneg (by positivity) M.1
  have hFloor :
      ⌊(n : ℝ) * ρ⌋₊ = k := by
    exact (Nat.floor_eq_iff hNonneg).2 (by
      simpa [IsNatFloor] using hCell)
  rw [hBeta, hFloor]

/--
lower mechanical roof なら加法誤差は必ず `0` または `1`。
したがって `HasUnitCarry` が復元される。
-/
theorem hasUnitCarry
    {β : ℕ → ℕ}
    {a : ℕ}
    {ρ : ℝ}
    (M : IsLowerMechanicalRoof β a ρ) :
    HasUnitCarry β := by
  intro m n
  obtain ⟨km, hBetaM, hCellM⟩ := M.2 m
  obtain ⟨kn, hBetaN, hCellN⟩ := M.2 n
  obtain ⟨kmn, hBetaMN, hCellMN⟩ := M.2 (m + n)
  have hM := (show
      (km : ℝ) ≤ (m : ℝ) * ρ ∧
        (m : ℝ) * ρ < (km : ℝ) + 1 by
    simpa [IsNatFloor] using hCellM)
  have hN := (show
      (kn : ℝ) ≤ (n : ℝ) * ρ ∧
        (n : ℝ) * ρ < (kn : ℝ) + 1 by
    simpa [IsNatFloor] using hCellN)
  have hMN := (show
      (kmn : ℝ) ≤ ((m + n : ℕ) : ℝ) * ρ ∧
        ((m + n : ℕ) : ℝ) * ρ < (kmn : ℝ) + 1 by
    simpa [IsNatFloor] using hCellMN)
  have hSlopeAdd :
      ((m + n : ℕ) : ℝ) * ρ =
        (m : ℝ) * ρ + (n : ℝ) * ρ := by
    push_cast
    ring
  have hLowerR :
      ((km + kn : ℕ) : ℝ) < ((kmn + 1 : ℕ) : ℝ) := by
    push_cast
    rw [hSlopeAdd] at hMN
    nlinarith
  have hUpperR :
      (kmn : ℝ) < ((km + kn + 2 : ℕ) : ℝ) := by
    push_cast
    rw [hSlopeAdd] at hMN
    nlinarith
  have hLowerNat : km + kn ≤ kmn := by
    have h : km + kn < kmn + 1 := by
      exact_mod_cast hLowerR
    omega
  have hUpperNat : kmn ≤ km + kn + 1 := by
    have h : kmn < km + kn + 2 := by
      exact_mod_cast hUpperR
    omega
  constructor
  · rw [hBetaM, hBetaN, hBetaMN]
    simp only [Nat.add_mul]
    omega
  · rw [hBetaM, hBetaN, hBetaMN]
    simp only [Nat.add_mul]
    omega

end IsLowerMechanicalRoof

namespace IsUpperMechanicalRoof

/-- upper mechanical roof は concrete には `Nat.ceil(nρ)-1` で書ける。 -/
theorem eq_linear_add_natCeil_sub_one
    {β : ℕ → ℕ}
    {a : ℕ}
    {ρ : ℝ}
    (M : IsUpperMechanicalRoof β a ρ)
    (n : ℕ) :
    β n = n * a + (⌈(n : ℝ) * ρ⌉₊ - 1) := by
  by_cases hn : n = 0
  · subst n
    simp [M.2.1]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    obtain ⟨k, hBeta, hCell⟩ := M.2.2 n hnPos
    have hCell' :
        (k : ℝ) < (n : ℝ) * ρ ∧
          (n : ℝ) * ρ ≤ (k : ℝ) + 1 := by
      simpa [IsNatUpperCell] using hCell
    have hCeil :
        ⌈(n : ℝ) * ρ⌉₊ = k + 1 := by
      apply (Nat.ceil_eq_iff (Nat.add_one_ne_zero k)).2
      simpa using hCell'
    rw [hBeta, hCeil]
    simp

/--
upper mechanical roof からも `HasUnitCarry` が復元される。

両区間が正幅なら upper cell の加法だけで示し、
どちらかが幅 `0` なら `β(0)=0` から直ちに従う。
-/
theorem hasUnitCarry
    {β : ℕ → ℕ}
    {a : ℕ}
    {ρ : ℝ}
    (M : IsUpperMechanicalRoof β a ρ) :
    HasUnitCarry β := by
  intro m n
  by_cases hm : m = 0
  · subst m
    simp [M.2.1]
  by_cases hn : n = 0
  · subst n
    simp [M.2.1]
  have hmPos : 0 < m := Nat.pos_of_ne_zero hm
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  have hmnPos : 0 < m + n := by omega
  obtain ⟨km, hBetaM, hCellM⟩ := M.2.2 m hmPos
  obtain ⟨kn, hBetaN, hCellN⟩ := M.2.2 n hnPos
  obtain ⟨kmn, hBetaMN, hCellMN⟩ := M.2.2 (m + n) hmnPos
  have hM := (show
      (km : ℝ) < (m : ℝ) * ρ ∧
        (m : ℝ) * ρ ≤ (km : ℝ) + 1 by
    simpa [IsNatUpperCell] using hCellM)
  have hN := (show
      (kn : ℝ) < (n : ℝ) * ρ ∧
        (n : ℝ) * ρ ≤ (kn : ℝ) + 1 by
    simpa [IsNatUpperCell] using hCellN)
  have hMN := (show
      (kmn : ℝ) < ((m + n : ℕ) : ℝ) * ρ ∧
        ((m + n : ℕ) : ℝ) * ρ ≤ (kmn : ℝ) + 1 by
    simpa [IsNatUpperCell] using hCellMN)
  have hSlopeAdd :
      ((m + n : ℕ) : ℝ) * ρ =
        (m : ℝ) * ρ + (n : ℝ) * ρ := by
    push_cast
    ring
  have hLowerR :
      ((km + kn : ℕ) : ℝ) < ((kmn + 1 : ℕ) : ℝ) := by
    push_cast
    rw [hSlopeAdd] at hMN
    nlinarith
  have hUpperR :
      (kmn : ℝ) < ((km + kn + 2 : ℕ) : ℝ) := by
    push_cast
    rw [hSlopeAdd] at hMN
    nlinarith
  have hLowerNat : km + kn ≤ kmn := by
    have h : km + kn < kmn + 1 := by
      exact_mod_cast hLowerR
    omega
  have hUpperNat : kmn ≤ km + kn + 1 := by
    have h : kmn < km + kn + 2 := by
      exact_mod_cast hUpperR
    omega
  constructor
  · rw [hBetaM, hBetaN, hBetaMN]
    simp only [Nat.add_mul]
    omega
  · rw [hBetaM, hBetaN, hBetaMN]
    simp only [Nat.add_mul]
    omega

end IsUpperMechanicalRoof

namespace HasUnitCarry

/--
`HasUnitCarry β` なら canonical な `a = β(1)` と `ρ = residualSlope β` を使って、
lower または upper mechanical roof が得られる。

無理数 case は lower、rational case は分母境界の lower / upper 型に従って分かれる。
-/
theorem canonical_lower_or_upperMechanicalRoof
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    IsLowerMechanicalRoof β (β 1) (residualSlope β) ∨
      IsUpperMechanicalRoof β (β 1) (residualSlope β) := by
  classical
  by_cases hIrr : Irrational (residualSlope β)
  · left
    refine ⟨U.residualSlope_mem_unitInterval.1, ?_⟩
    intro n
    refine ⟨roofResidual β n, U.beta_eq_linear_add_residual n, ?_⟩
    by_cases hn : n = 0
    · subst n
      simp [IsNatFloor, U.roofResidual_zero]
    · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
      exact
        U.residual_isNatFloor_of_residualSlope_irrational
          hIrr hnPos
  · obtain ⟨p, q, hq, _hpq, hCoprime, hSlope, S⟩ :=
      U.exists_reduced_scaledRationalSlope_of_not_irrational hIrr
    rcases rationalSlope_denominator_two_boundary_types S with hLower | hUpper
    · left
      refine ⟨U.residualSlope_mem_unitInterval.1, ?_⟩
      intro n
      refine ⟨roofResidual β n, U.beta_eq_linear_add_residual n, ?_⟩
      by_cases hn : n = 0
      · subst n
        simp [IsNatFloor, U.roofResidual_zero]
      · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
        rw [hSlope]
        exact U.rationalLower_isNatFloor
          S hCoprime hLower hnPos
    · right
      refine ⟨U.residualSlope_mem_unitInterval.1, U.zero_eq, ?_⟩
      intro n hnPos
      refine ⟨roofResidual β n, U.beta_eq_linear_add_residual n, ?_⟩
      rw [hSlope]
      exact U.rationalUpper_isNatUpperCell
        S hCoprime hUpper hnPos

/-- canonical mechanical 表現から existential 表現を取り出す短い wrapper。 -/
theorem exists_lower_or_upperMechanicalRoof
    {β : ℕ → ℕ}
    (U : HasUnitCarry β) :
    ∃ a : ℕ, ∃ ρ : ℝ,
      IsLowerMechanicalRoof β a ρ ∨
        IsUpperMechanicalRoof β a ρ := by
  exact ⟨β 1, residualSlope β, U.canonical_lower_or_upperMechanicalRoof⟩

end HasUnitCarry

/--
canonical な最終特徴付け:

`HasUnitCarry β` であることと、canonical linear part `β(1)` と canonical slope
`residualSlope β` によって lower / upper mechanical roof として表せることは同値。

したがって unit-carry は mechanical roof geometry を特徴付ける薄い公理になっている。
-/
theorem hasUnitCarry_iff_canonicalMechanicalRoof
    {β : ℕ → ℕ} :
    HasUnitCarry β ↔
      IsLowerMechanicalRoof β (β 1) (residualSlope β) ∨
        IsUpperMechanicalRoof β (β 1) (residualSlope β) := by
  constructor
  · intro U
    exact U.canonical_lower_or_upperMechanicalRoof
  · intro h
    rcases h with hLower | hUpper
    · exact hLower.hasUnitCarry
    · exact hUpper.hasUnitCarry

/--
存在形で書いた特徴付け。

canonical 版から直ちに従うが、mechanical roof を独立対象として再利用するときに便利な形。
-/
theorem hasUnitCarry_iff_exists_mechanicalRoof
    {β : ℕ → ℕ} :
    HasUnitCarry β ↔
      ∃ a : ℕ, ∃ ρ : ℝ,
        IsLowerMechanicalRoof β a ρ ∨
          IsUpperMechanicalRoof β a ρ := by
  constructor
  · intro U
    exact U.exists_lower_or_upperMechanicalRoof
  · rintro ⟨a, ρ, hLower | hUpper⟩
    · exact hLower.hasUnitCarry
    · exact hUpper.hasUnitCarry

end Experimental
end Collatz3
