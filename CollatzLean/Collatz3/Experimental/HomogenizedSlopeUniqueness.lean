import CollatzLean.Collatz3.Experimental.HomogenizedSlopeExistence
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Collatz3 experimental: homogenized slope の一意性

`IsHomogenizedSlope β ρ` が与える幅 1 の整数窓だけから、slope 自体が一意であることを示す。

`HasUnitCarry` はこの一意性 theorem には不要。
unit-carry roof が必要になるのは、canonical な `residualSlope β` が実際にこの窓を満たすことを
接続する corollary 側だけである。
-/

namespace Collatz3
namespace Experimental

/--
同じ residual に対する homogenized slope は一意。

両方の slope が各正整数 `n` について

`γ(n) ≤ nρ ≤ γ(n)+1`

を満たすなら、差は全ての `n` について `1/n` 以下になる。
Archimedean 性により差は 0 しかあり得ない。
-/
theorem homogenizedSlope_unique
    {β : ℕ → ℕ}
    {ρ σ : ℝ}
    (Sρ : IsHomogenizedSlope β ρ)
    (Sσ : IsHomogenizedSlope β σ) :
    ρ = σ := by
  apply le_antisymm
  · by_contra hNot
    have hlt : σ < ρ := lt_of_not_ge hNot
    have hgap : 0 < ρ - σ := sub_pos.mpr hlt
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hgap
    let n : ℕ := k + 1
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    have hρ := Sρ n hn
    have hσ := Sσ n hn
    have hGapMul :
        (n : ℝ) * (ρ - σ) ≤ 1 := by
      linarith [hρ.2, hσ.1]
    have hGapLe :
        ρ - σ ≤ 1 / (n : ℝ) := by
      apply (le_div_iff₀ hnR).2
      nlinarith [hGapMul]
    have hk' :
        1 / (n : ℝ) < ρ - σ := by
      simpa [n] using hk
    exact (not_lt_of_ge hGapLe) hk'
  · by_contra hNot
    have hlt : ρ < σ := lt_of_not_ge hNot
    have hgap : 0 < σ - ρ := sub_pos.mpr hlt
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hgap
    let n : ℕ := k + 1
    have hn : 0 < n := by
      dsimp [n]
      omega
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    have hρ := Sρ n hn
    have hσ := Sσ n hn
    have hGapMul :
        (n : ℝ) * (σ - ρ) ≤ 1 := by
      linarith [hσ.2, hρ.1]
    have hGapLe :
        σ - ρ ≤ 1 / (n : ℝ) := by
      apply (le_div_iff₀ hnR).2
      nlinarith [hGapMul]
    have hk' :
        1 / (n : ℝ) < σ - ρ := by
      simpa [n] using hk
    exact (not_lt_of_ge hGapLe) hk'

namespace HasUnitCarry

/--
unit-carry roof に対する任意の homogenized slope は、
canonical construction `residualSlope β` と一致する。
-/
theorem homogenizedSlope_eq_residualSlope
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {ρ : ℝ}
    (S : IsHomogenizedSlope β ρ) :
    ρ = residualSlope β := by
  exact homogenizedSlope_unique S U.residualSlope_isHomogenizedSlope

end HasUnitCarry
end Experimental
end Collatz3
