import CollatzLean.Collatz3.Bridge.CollatzLogPhase
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Collatz3 Bridge: actual log-phase 補正の定量評価

`collatzLogCorrection x = log₂(1 + 1/(3x))`

は正で、`x` が大きくなると小さい。ここでは第三段の near-return 評価に必要な
一点ごとの elementary bound

`0 < δ(x) ≤ 1 / (3x * ln 2)`

を証明する。
-/

namespace Collatz3
namespace Bridge

/-- 正の自然数では `+1` 補正は strict に正。 -/
theorem collatzLogCorrection_pos
    {x : ℕ}
    (hx : 0 < x) :
    0 < collatzLogCorrection x := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hFrac :
      (0 : ℝ) < 1 / ((3 : ℝ) * (x : ℝ)) := by positivity
  unfold collatzLogCorrection
  exact
    Real.logb_pos
      (by norm_num : (1 : ℝ) < 2)
      (by linarith : (1 : ℝ) < 1 + 1 / ((3 : ℝ) * (x : ℝ)))

/--
標準不等式 `log(1+t) ≤ t` を base 2 へ移した直接の上界。
-/
theorem collatzLogCorrection_le_div_log_two
    {x : ℕ}
    (hx : 0 < x) :
    collatzLogCorrection x ≤
      (1 / ((3 : ℝ) * (x : ℝ))) / Real.log 2 := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hThreeX : (0 : ℝ) < (3 : ℝ) * (x : ℝ) := by positivity
  have hArg :
      (0 : ℝ) < 1 + 1 / ((3 : ℝ) * (x : ℝ)) := by positivity
  have hLogTwo : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num)
  unfold collatzLogCorrection Real.logb
  apply (div_le_div_iff_of_pos_right hLogTwo).2
  calc
    Real.log (1 + 1 / ((3 : ℝ) * (x : ℝ))) ≤
        (1 + 1 / ((3 : ℝ) * (x : ℝ))) - 1 :=
      Real.log_le_sub_one_of_pos hArg
    _ = 1 / ((3 : ℝ) * (x : ℝ)) := by ring

/-- 論文・計算で使いやすい `1 / (3x ln 2)` 形の上界。 -/
theorem collatzLogCorrection_le_inv_three_mul_log_two
    {x : ℕ}
    (hx : 0 < x) :
    collatzLogCorrection x ≤
      1 / (((3 : ℝ) * (x : ℝ)) * Real.log 2) := by
  have hThreeX : (0 : ℝ) < (3 : ℝ) * (x : ℝ) := by
    have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    positivity
  have hLogTwo : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num)
  calc
    collatzLogCorrection x ≤
        (1 / ((3 : ℝ) * (x : ℝ))) / Real.log 2 :=
      collatzLogCorrection_le_div_log_two hx
    _ = 1 / (((3 : ℝ) * (x : ℝ)) * Real.log 2) := by
      field_simp [hThreeX.ne', hLogTwo.ne']

end Bridge

namespace OddStep

/-- actual odd-only step では、その始点に付随する log 補正は strict に正。 -/
theorem logCorrection_pos
    {e x y : ℕ}
    (h : OddStep e x y) :
    0 < Bridge.collatzLogCorrection x :=
  Bridge.collatzLogCorrection_pos h.start_pos

/-- actual odd-only step の log 補正に対する `1/(3x ln 2)` 上界。 -/
theorem logCorrection_le_inv_three_mul_log_two
    {e x y : ℕ}
    (h : OddStep e x y) :
    Bridge.collatzLogCorrection x ≤
      1 / (((3 : ℝ) * (x : ℝ)) * Real.log 2) :=
  Bridge.collatzLogCorrection_le_inv_three_mul_log_two h.start_pos

/--
一歩の phase law と補正の符号・上界を一つに束ねた第三段向け API。
-/
theorem logPhase_step_with_correction_bounds
    {e x y : ℕ}
    (h : OddStep e x y) :
    Bridge.collatzLogPhase y =
        Int.fract
          (Bridge.collatzLogPhase x + Bridge.collatzLogRotation +
            Bridge.collatzLogCorrection x) ∧
      0 < Bridge.collatzLogCorrection x ∧
      Bridge.collatzLogCorrection x ≤
        1 / (((3 : ℝ) * (x : ℝ)) * Real.log 2) := by
  exact ⟨h.logPhase_step, h.logCorrection_pos,
    h.logCorrection_le_inv_three_mul_log_two⟩

end OddStep
end Collatz3
