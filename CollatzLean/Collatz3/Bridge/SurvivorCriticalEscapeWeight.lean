import CollatzLean.Collatz3.Bridge.SurvivorDefectBeattyScale
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscape
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: critical escape weight

2021 年論文の critical Sturmian 列で現れる有限段階の重みを、
現在の power-form Beatty roof だけから読む薄い実数座標として切り出す。

`w_m = 2^(beattyIndex m) / 3^(m+1)`

と置く。これは real / 2進 completion の同一視を一切使わない。
既存の Beatty power bounds だけから

`1/6 < w_m <= 1/3`

を得る。

infinite survivor では

`beattyIndex m = D_m + delta_m`

なので actual normalized escape increment は exact に

`a_m = w_m / 2^delta_m`

となる。また Beatty roof の一歩差

`beattyIndex (m+1) = beattyIndex m + 1 + s_m`

から

`w_(m+1) = (2^(1+s_m)/3) w_m`

を得る。

最後に既存 Beatty scale

`P_m = 3^m / 2^(beattyIndex m)`

とは

`w_m = 1 / (3 P_m)`

で exact に一致する。

新しい orbit notion は導入せず、追加 definition は scalar `criticalEscapeWeight` 一個だけ。
-/

namespace Collatz3
namespace Bridge

/--
critical Beatty roof に対応する一歩 escape weight。

`w_m = 2^(beattyIndex m) / 3^(m+1)`。
-/
noncomputable def criticalEscapeWeight (m : ℕ) : ℝ :=
  (2 : ℝ) ^ Critical.beattyIndex m / (3 : ℝ) ^ (m + 1)

/-- critical escape weight は常に正。 -/
theorem criticalEscapeWeight_pos (m : ℕ) :
    0 < criticalEscapeWeight m := by
  unfold criticalEscapeWeight
  positivity

/--
critical escape weight と既存 Beatty scale の exact inverse relation。

`w_m = 1 / (3 P_m)`。
-/
theorem criticalEscapeWeight_eq_one_div_three_mul_beattyScale
    (m : ℕ) :
    criticalEscapeWeight m = 1 / (3 * survivorBeattyScale m) := by
  unfold criticalEscapeWeight survivorBeattyScale
  rw [pow_succ]
  field_simp

/--
critical escape weight は exact に `(1/6, 1/3]` に入る。

これは `P_m in [1,2)` と `w_m = 1/(3P_m)` だけから従う。
-/
theorem criticalEscapeWeight_mem_Ioc_one_six_one_third
    (m : ℕ) :
    (1 : ℝ) / 6 < criticalEscapeWeight m ∧
      criticalEscapeWeight m ≤ (1 : ℝ) / 3 := by
  rw [criticalEscapeWeight_eq_one_div_three_mul_beattyScale]
  have hP := survivorBeattyScale_mem_Ico_one_two m
  have hPPos : 0 < survivorBeattyScale m :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hP.1
  have hDenPos : 0 < 3 * survivorBeattyScale m := by positivity
  constructor
  · apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 6) hDenPos).2
    nlinarith [hP.2]
  · apply (div_le_div_iff₀ hDenPos (by norm_num : (0 : ℝ) < 3)).2
    nlinarith [hP.1]

/--
Beatty roof の一歩差を normalized Sturmian step で書いた exact identity。

`beattyIndex (m+1) = beattyIndex m + 1 + s_m`。
-/
theorem beattyIndex_succ_eq_add_one_add_survivorSturmianStep
    (m : ℕ) :
    Critical.beattyIndex (m + 1) =
      Critical.beattyIndex m + 1 + survivorSturmianStep m := by
  have hm := index_le_beattyIndex m
  have hm1 := index_le_beattyIndex (m + 1)
  have hInc := Critical.beattyIndex_lt_succ m
  unfold survivorSturmianStep survivorRoofExcess
  omega

/--
critical escape weight の exact one-step recurrence。

`w_(m+1) = (2^(1+s_m)/3) * w_m`。
-/
theorem criticalEscapeWeight_succ
    (m : ℕ) :
    criticalEscapeWeight (m + 1) =
      ((2 : ℝ) ^ (1 + survivorSturmianStep m) / 3) *
        criticalEscapeWeight m := by
  have hBeatty := beattyIndex_succ_eq_add_one_add_survivorSturmianStep m
  unfold criticalEscapeWeight
  rw [hBeatty]
  rw [show Critical.beattyIndex m + 1 + survivorSturmianStep m =
      Critical.beattyIndex m + (1 + survivorSturmianStep m) by omega]
  rw [pow_add]
  rw [show m + 1 + 1 = (m + 1) + 1 by rfl, pow_succ]
  field_simp

end Bridge

namespace OddOrbit

open Bridge

/--
infinite survivor の normalized escape increment は、critical weight を
current defect scale `2^delta_m` で割ったものに exact に一致する。

`a_m = w_m / 2^delta_m`。
-/
theorem normalizedEscapeIncrement_eq_criticalEscapeWeight_div_twoPowDefect
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    O.normalizedEscapeIncrement m =
      criticalEscapeWeight m /
        (2 : ℝ) ^ infiniteSurvivorDefect O.exponent m := by
  have hBeatty := beattyIndex_eq_prefixDepth_add_defect SInf m
  unfold normalizedEscapeIncrement criticalEscapeWeight
  rw [hBeatty, pow_add]
  field_simp
  ring

end OddOrbit
end Collatz3
