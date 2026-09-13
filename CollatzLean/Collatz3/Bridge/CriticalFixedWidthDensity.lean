import CollatzLean.Collatz3.Bridge.CriticalFixedWidthCounting
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: fixed-width critical start の自然密度

前段の exact block counting と bounded discrepancy から、固定幅 `m > 0` の
actual critical start 集合が自然密度

`N_m / M_m`

を持つことを `Tendsto` として形式化する。
-/

namespace Collatz3
namespace Bridge

open Filter Topology

/-- `X` 未満にある幅 `m` critical starts の割合。 -/
noncomputable def fixedWidthCriticalStartRatio
    (m X : ℕ) : ℝ :=
  (actualCriticalStartCount m X : ℝ) / (X : ℝ)

/-- 固定幅 `m` の exact density candidate `N_m / M_m`。 -/
noncomputable def fixedWidthCriticalStartDensity
    (m : ℕ) : ℝ :=
  (criticalPartitionCount m : ℝ) / (criticalStartModulus m : ℝ)

/--
自然数値 count が cross-multiplied bounded discrepancy を持てば、
count/X は `N/M` へ収束するという一般補題。
-/
theorem tendsto_ratio_of_nat_cross_discrepancy
    (M N : ℕ)
    (hM : 0 < M)
    (C : ℕ → ℕ)
    (hDisc :
      ∀ X : ℕ,
        M * C X ≤ N * X + M * N ∧
        N * X ≤ M * C X + M * N) :
    Tendsto
      (fun X : ℕ => (C X : ℝ) / (X : ℝ))
      atTop
      (𝓝 ((N : ℝ) / (M : ℝ))) := by
  let d : ℝ := (N : ℝ) / (M : ℝ)
  have hErr :
      Tendsto (fun X : ℕ => (N : ℝ) / (X : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (N : ℝ)
  have hConst : Tendsto (fun _ : ℕ => d) atTop (𝓝 d) :=
    tendsto_const_nhds
  have hLower :
      Tendsto
        (fun X : ℕ => d - (N : ℝ) / (X : ℝ))
        atTop (𝓝 d) := by
    simpa using hConst.sub hErr
  have hUpper :
      Tendsto
        (fun X : ℕ => d + (N : ℝ) / (X : ℝ))
        atTop (𝓝 d) := by
    simpa using hConst.add hErr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
  · filter_upwards [eventually_gt_atTop 0] with X hX
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hNat := (hDisc X).2
    have hCast :
        (N : ℝ) * (X : ℝ) ≤
          (M : ℝ) * (C X : ℝ) + (M : ℝ) * (N : ℝ) := by
      exact_mod_cast hNat
    have hNum :
        (N : ℝ) * (X : ℝ) - (M : ℝ) * (N : ℝ) ≤
          (M : ℝ) * (C X : ℝ) := by
      linarith
    calc
      d - (N : ℝ) / (X : ℝ)
          =
          ((N : ℝ) * (X : ℝ) - (M : ℝ) * (N : ℝ)) /
            ((M : ℝ) * (X : ℝ)) := by
              dsimp [d]
              field_simp [ne_of_gt hMR, ne_of_gt hXR]
      _ ≤
          ((M : ℝ) * (C X : ℝ)) /
            ((M : ℝ) * (X : ℝ)) :=
        (div_le_div_iff_of_pos_right (mul_pos hMR hXR)).2 hNum
      _ = (C X : ℝ) / (X : ℝ) := by
        field_simp [ne_of_gt hMR, ne_of_gt hXR]
  · filter_upwards [eventually_gt_atTop 0] with X hX
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
    have hNat := (hDisc X).1
    have hCast :
        (M : ℝ) * (C X : ℝ) ≤
          (N : ℝ) * (X : ℝ) + (M : ℝ) * (N : ℝ) := by
      exact_mod_cast hNat
    calc
      (C X : ℝ) / (X : ℝ)
          =
          ((M : ℝ) * (C X : ℝ)) /
            ((M : ℝ) * (X : ℝ)) := by
              field_simp [ne_of_gt hMR, ne_of_gt hXR]
      _ ≤
          ((N : ℝ) * (X : ℝ) + (M : ℝ) * (N : ℝ)) /
            ((M : ℝ) * (X : ℝ)) :=
        (div_le_div_iff_of_pos_right (mul_pos hMR hXR)).2 hCast
      _ = d + (N : ℝ) / (X : ℝ) := by
        dsimp [d]
        field_simp [ne_of_gt hMR, ne_of_gt hXR]

/--
固定幅 `m > 0` の actual critical starts は自然密度 `N_m / M_m` を持つ。
-/
theorem fixedWidthCriticalStartRatio_tendsto
    {m : ℕ}
    (hm : 0 < m) :
    Tendsto
      (fixedWidthCriticalStartRatio m)
      atTop
      (𝓝 (fixedWidthCriticalStartDensity m)) := by
  unfold fixedWidthCriticalStartRatio fixedWidthCriticalStartDensity
  exact
    tendsto_ratio_of_nat_cross_discrepancy
      (criticalStartModulus m)
      (criticalPartitionCount m)
      (criticalStartModulus_pos m)
      (actualCriticalStartCount m)
      (fun X => actualCriticalStartCount_cross_discrepancy (m := m) (X := X) hm)

end Bridge
end Collatz3
