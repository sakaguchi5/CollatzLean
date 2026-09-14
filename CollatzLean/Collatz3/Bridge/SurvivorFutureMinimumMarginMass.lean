import CollatzLean.Collatz3.Bridge.SurvivorFutureMinimumABCRigidity
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: ABC 文字数制約から critical-margin 総量制約へ

標準 survivor future-minimum の有限 ABC word について、すでに

* `#A ≤ 2 #C + 2`,
* `#C = Σ μ(r_t) + μ(start) - μ(end)`

が exact に得られている。

このファイルでは新しい primitive definition を一切導入せず、二式を直接合成する。

中心となる exact inequality は

`#A / 2 - 1 - μ(start) + μ(end) ≤ Σ μ(r_t)`。

さらに `0 < μ ≤ 1` だけで endpoint 項を落とすと

`#A / 2 - 2 < Σ μ(r_t)`

となる。

非減少 defect 区間では `defectGrowth = #A` なので、同じ評価をそのまま

`defectGrowth / 2 - 2 < Σ μ(r_t)`

へ移せる。これにより、symbolic rise/recharge 制約が actual correction budget と
直接比較できる real-valued margin mass constraint へ変換される。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

namespace FutureMinima

/--
ABC 文字数制約と margin telescope を合成した exact upper form。

`#A ≤ 2 * (Σ μ(r_t) + μ(start) - μ(end)) + 2`。

survivor / defect 非減少性は不要で、標準 future-minimum 列であることだけを使う。
-/
theorem count_A_cast_le_two_margin_sum_add_endpoint
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((F.symbolWord n q).count .A : ℝ) ≤
      2 *
          (((F.lengthWord n q).map criticalMargin).sum +
            criticalMargin (F.index n) -
            criticalMargin (F.index (n + q))) +
        2 := by
  have hCount :=
    F.symbolWord_count_A_le_two_count_C_add_two S hStandard n q
  have hCountR :
      ((F.symbolWord n q).count .A : ℝ) ≤
        2 * ((F.symbolWord n q).count .C : ℝ) + 2 := by
    exact_mod_cast hCount
  have hC :=
    F.count_C_eq_margin_sum_add_start_sub_end n q
  rw [hC] at hCountR
  exact hCountR

/--
前 theorem を margin mass の lower bound として解いた exact form。

`#A / 2 - 1 - μ(start) + μ(end) ≤ Σ μ(r_t)`。
-/
theorem half_count_A_sub_endpoint_le_margin_sum
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((F.symbolWord n q).count .A : ℝ) / 2 - 1 -
          criticalMargin (F.index n) +
          criticalMargin (F.index (n + q)) ≤
      ((F.lengthWord n q).map criticalMargin).sum := by
  have h :=
    F.count_A_cast_le_two_margin_sum_add_endpoint
      S hStandard n q
  linarith

/--
endpoint margin を `0 < μ ≤ 1` だけで消した coarse count form。

`#A / 2 - 2 < Σ μ(r_t)`。

strict inequality なのは終点 margin が strict positive だから。
-/
theorem half_count_A_sub_two_lt_margin_sum
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((F.symbolWord n q).count .A : ℝ) / 2 - 2 <
      ((F.lengthWord n q).map criticalMargin).sum := by
  have hExact :=
    F.half_count_A_sub_endpoint_le_margin_sum
      S hStandard n q
  have hStartLe := criticalMargin_le_one (F.index n)
  have hEndPos := criticalMargin_pos (F.index (n + q))
  linarith

/--
同じ coarse count constraint を upper form で書いたもの。

`#A < 2 * Σ μ(r_t) + 4`。
-/
theorem count_A_cast_lt_two_margin_sum_add_four
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((F.symbolWord n q).count .A : ℝ) <
      2 * ((F.lengthWord n q).map criticalMargin).sum + 4 := by
  have h :=
    F.half_count_A_sub_two_lt_margin_sum
      S hStandard n q
  linarith

/--
非減少 defect 区間で `defectGrowth = #A` を exact margin lower bound へ移した形。

`defectGrowth / 2 - 1 - μ(start) + μ(end) ≤ Σ μ(r_t)`。
-/
theorem half_defectGrowth_sub_endpoint_le_margin_sum_of_nondec
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n q : ℕ}
    (hNondec :
      ∀ t : ℕ,
        n ≤ t →
        t < n + q →
        infiniteSurvivorDefect O.exponent (F.index t) ≤
          infiniteSurvivorDefect O.exponent (F.index (t + 1))) :
    ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) / 2 - 1 -
          criticalMargin (F.index n) +
          criticalMargin (F.index (n + q)) ≤
      ((F.lengthWord n q).map criticalMargin).sum := by
  have hDef :=
    F.defect_end_eq_start_add_count_A_of_nondec
      S hStandard hNondec
  have hSub :
      infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) =
        (F.symbolWord n q).count .A := by
    omega
  have hSubR :
      ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
            infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) =
        ((F.symbolWord n q).count .A : ℝ) := by
    exact_mod_cast hSub
  rw [hSubR]
  exact
    F.half_count_A_sub_endpoint_le_margin_sum
      S hStandard n q

/--
endpoint margin を消した defect-growth の coarse lower bound。

`defectGrowth / 2 - 2 < Σ μ(r_t)`。

これは symbolic dynamics から得た文字数制約を、今後 actual correction budget と
直接衝突させるための中心 API。
-/
theorem half_defectGrowth_sub_two_lt_margin_sum_of_nondec
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n q : ℕ}
    (hNondec :
      ∀ t : ℕ,
        n ≤ t →
        t < n + q →
        infiniteSurvivorDefect O.exponent (F.index t) ≤
          infiniteSurvivorDefect O.exponent (F.index (t + 1))) :
    ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) / 2 - 2 <
      ((F.lengthWord n q).map criticalMargin).sum := by
  have hExact :=
    F.half_defectGrowth_sub_endpoint_le_margin_sum_of_nondec
      S hStandard hNondec
  have hStartLe := criticalMargin_le_one (F.index n)
  have hEndPos := criticalMargin_pos (F.index (n + q))
  linarith

/--
coarse defect-growth constraint の upper form。

`defectGrowth < 2 * Σ μ(r_t) + 4`。
-/
theorem defectGrowth_cast_lt_two_margin_sum_add_four_of_nondec
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n q : ℕ}
    (hNondec :
      ∀ t : ℕ,
        n ≤ t →
        t < n + q →
        infiniteSurvivorDefect O.exponent (F.index t) ≤
          infiniteSurvivorDefect O.exponent (F.index (t + 1))) :
    ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) <
      2 * ((F.lengthWord n q).map criticalMargin).sum + 4 := by
  have h :=
    F.half_defectGrowth_sub_two_lt_margin_sum_of_nondec
      S hStandard hNondec
  linarith

/--
必要な defect growth `d` を外から与えるための wrapper。

区間内で少なくとも `d` だけ defect を増やすには

`d / 2 - 2 < Σ μ(r_t)`

だけの critical-margin mass が必要。
-/
theorem required_defectGrowth_half_sub_two_lt_margin_sum_of_nondec
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n q d : ℕ}
    (hNondec :
      ∀ t : ℕ,
        n ≤ t →
        t < n + q →
        infiniteSurvivorDefect O.exponent (F.index t) ≤
          infiniteSurvivorDefect O.exponent (F.index (t + 1)))
    (hGrowth :
      d ≤
        infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n)) :
    (d : ℝ) / 2 - 2 <
      ((F.lengthWord n q).map criticalMargin).sum := by
  have hMass :=
    F.half_defectGrowth_sub_two_lt_margin_sum_of_nondec
      S hStandard hNondec
  have hGrowthR :
      (d : ℝ) ≤
        ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
            infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) := by
    exact_mod_cast hGrowth
  linarith

end FutureMinima
end OddOrbit
end Collatz3
