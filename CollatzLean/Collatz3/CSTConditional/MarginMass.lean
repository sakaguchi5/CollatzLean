import CollatzLean.Collatz3.CSTConditional.FutureMinimum
import CollatzLean.Collatz3.Bridge.SurvivorFutureMinimumMarginMass

/-!
# Collatz3 CSTConditional: Global CST 下の unconditional margin-mass bounds

unconditional 本体の `SurvivorFutureMinimumMarginMass` では、defect-growth 版だけ
有限区間の transition-by-transition 非減少性を仮定していた。

Global CST の下では `B` および positive excess が消え、標準 future-minimum 列の defect は
自動的に非減少となる。従って同じ margin-mass inequality から `hNondec` を除去できる。

新しい primitive definition は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

namespace FutureMinima

/-- Global CST 下では任意有限区間で `defect growth = #A` が無条件に使える。 -/
theorem defect_end_eq_start_add_count_A_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    infiniteSurvivorDefect O.exponent (F.index (n + q)) =
      infiniteSurvivorDefect O.exponent (F.index n) +
        (F.symbolWord n q).count .A := by
  apply F.defect_end_eq_start_add_count_A_of_nondec S hStandard
  intro t _ht0 _htq
  exact F.defect_nondec_of_globalCST G S hStandard t

/--
Global CST 下の exact defect-growth margin lower bound。

`defectGrowth / 2 - 1 - μ(start) + μ(end) ≤ Σ μ(r_t)`。
-/
theorem half_defectGrowth_sub_endpoint_le_margin_sum_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) / 2 - 1 -
          criticalMargin (F.index n) +
          criticalMargin (F.index (n + q)) ≤
      ((F.lengthWord n q).map criticalMargin).sum := by
  apply F.half_defectGrowth_sub_endpoint_le_margin_sum_of_nondec S hStandard
  intro t _ht0 _htq
  exact F.defect_nondec_of_globalCST G S hStandard t

/--
Global CST 下では endpoint 項を消した中心評価にも追加の monotonicity 仮定が不要。

`defectGrowth / 2 - 2 < Σ μ(r_t)`。
-/
theorem half_defectGrowth_sub_two_lt_margin_sum_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) / 2 - 2 <
      ((F.lengthWord n q).map criticalMargin).sum := by
  apply F.half_defectGrowth_sub_two_lt_margin_sum_of_nondec S hStandard
  intro t _ht0 _htq
  exact F.defect_nondec_of_globalCST G S hStandard t

/-- upper form: `defectGrowth < 2 * Σ μ(r_t) + 4`。 -/
theorem defectGrowth_cast_lt_two_margin_sum_add_four_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) <
      2 * ((F.lengthWord n q).map criticalMargin).sum + 4 := by
  apply F.defectGrowth_cast_lt_two_margin_sum_add_four_of_nondec S hStandard
  intro t _ht0 _htq
  exact F.defect_nondec_of_globalCST G S hStandard t

/--
必要 growth `d` を外から与える版。Global CST 下では monotonicity witness を渡す必要がない。
-/
theorem required_defectGrowth_half_sub_two_lt_margin_sum_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n q d : ℕ}
    (hGrowth :
      d ≤
        infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n)) :
    (d : ℝ) / 2 - 2 <
      ((F.lengthWord n q).map criticalMargin).sum := by
  apply
    F.required_defectGrowth_half_sub_two_lt_margin_sum_of_nondec
      S hStandard
  · intro t _ht0 _htq
    exact F.defect_nondec_of_globalCST G S hStandard t
  · exact hGrowth

end FutureMinima
end OddOrbit
end Collatz3
