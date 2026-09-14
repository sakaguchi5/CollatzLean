import CollatzLean.Collatz3.CSTConditional.ACCounting

/-!
# Collatz3 CSTConditional: defect と critical-margin の exact 保存則

AC 二文字化により、有限 future-minimum 区間の transition 数 `q` は

* `A` の個数 = defect growth
* `C` の個数 = critical-margin cocycle の wrap 数

へ exact に分解される。

既存の margin telescope

`#C = Σ μ(r_t) + μ(start) - μ(end)`

を代入すると

`defectGrowth + Σ μ(r_t) + μ(start) - μ(end) = q`

という exact conservation law が得られる。

さらに `q ≤ 3#C+2` を代入し、長い future-minimum 区間には線形量の
margin mass が必要であることも derived theorem として与える。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

namespace FutureMinima

/--
Global CST 下の中心 exact conservation law。

`defectGrowth + marginSum + μ(start) - μ(end) = q`。
-/
theorem defectGrowth_add_margin_balance_eq_transitions_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) +
        ((F.lengthWord n q).map criticalMargin).sum +
        criticalMargin (F.index n) -
        criticalMargin (F.index (n + q)) =
      (q : ℝ) := by
  have hNat :=
    F.defectGrowth_add_count_C_eq_transitions_of_globalCST
      G S hStandard n q
  have hNatR :
      (((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
            infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) +
          ((F.symbolWord n q).count .C : ℝ)) =
        (q : ℝ) := by
    exact_mod_cast hNat
  have hC := F.count_C_eq_margin_sum_add_start_sub_end n q
  rw [hC] at hNatR
  linarith

/--
Exact conservation を defect growth について解いた形。
-/
theorem defectGrowth_cast_eq_transitions_sub_margin_balance_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) =
      (q : ℝ) -
        ((F.lengthWord n q).map criticalMargin).sum -
        criticalMargin (F.index n) +
        criticalMargin (F.index (n + q)) := by
  have h :=
    F.defectGrowth_add_margin_balance_eq_transitions_of_globalCST
      G S hStandard n q
  linarith

/--
Exact conservation を margin balance について解いた形。

margin balance は `q - defectGrowth`、すなわち exact に `#C`。
-/
theorem margin_balance_eq_transitions_sub_defectGrowth_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((F.lengthWord n q).map criticalMargin).sum +
        criticalMargin (F.index n) -
        criticalMargin (F.index (n + q)) =
      (q : ℝ) -
        ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) := by
  have h :=
    F.defectGrowth_add_margin_balance_eq_transitions_of_globalCST
      G S hStandard n q
  linarith

/--
`q ≤ 3#C+2` を margin telescope へ代入した endpoint 付き線形評価。
-/
theorem transitions_cast_le_three_margin_balance_add_two_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    (q : ℝ) ≤
      3 *
          (((F.lengthWord n q).map criticalMargin).sum +
            criticalMargin (F.index n) -
            criticalMargin (F.index (n + q))) + 2 := by
  have hNat :=
    F.transitions_le_three_count_C_add_two_of_globalCST
      G S hStandard n q
  have hR :
      (q : ℝ) ≤
        3 * ((F.symbolWord n q).count .C : ℝ) + 2 := by
    exact_mod_cast hNat
  have hC := F.count_C_eq_margin_sum_add_start_sub_end n q
  rw [hC] at hR
  exact hR

/--
同じ線形評価を margin balance の下界として書いた版。

`(q-2)/3 ≤ marginBalance`。
-/
theorem transitions_sub_two_div_three_le_margin_balance_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((q : ℝ) - 2) / 3 ≤
      ((F.lengthWord n q).map criticalMargin).sum +
        criticalMargin (F.index n) -
        criticalMargin (F.index (n + q)) := by
  have h :=
    F.transitions_cast_le_three_margin_balance_add_two_of_globalCST
      G S hStandard n q
  linarith

/--
endpoint margin を `0 < μ ≤ 1` で粗く消した線形 margin-mass lower bound。

任意の長さ `q` の標準 future-minimum 区間で
`(q-2)/3 - 1 < Σ μ(r_t)`。
-/
theorem transitions_sub_two_div_three_sub_one_lt_margin_sum_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((q : ℝ) - 2) / 3 - 1 <
      ((F.lengthWord n q).map criticalMargin).sum := by
  have h :=
    F.transitions_sub_two_div_three_le_margin_balance_of_globalCST
      G S hStandard n q
  have hStart := criticalMargin_le_one (F.index n)
  have hEnd := criticalMargin_pos (F.index (n + q))
  linarith

/--
必要な future-minimum transition 数 `q` そのものから margin mass が線形成長することの別表現。

`q < 3 * Σμ + 5`。
-/
theorem transitions_cast_lt_three_margin_sum_add_five_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    (q : ℝ) <
      3 * ((F.lengthWord n q).map criticalMargin).sum + 5 := by
  have h :=
    F.transitions_sub_two_div_three_sub_one_lt_margin_sum_of_globalCST
      G S hStandard n q
  linarith


/--
局所 `C / AC / AAC` cell はそれぞれ margin wrap を exact に1回だけ消費する。

各場合で、その cell 長だけの `count C` が exact `1` であることを
既存 margin telescope へ入れた形。
-/
theorem local_cell_margin_balance_cases_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (t : ℕ) :
    (O.transitionSymbol (F.index t) (F.index (t + 1)) = .C ∧
      ((F.lengthWord t 1).map criticalMargin).sum +
          criticalMargin (F.index t) -
          criticalMargin (F.index (t + 1)) = 1) ∨
    (O.transitionSymbol (F.index t) (F.index (t + 1)) = .A ∧
      O.transitionSymbol (F.index (t + 1)) (F.index (t + 2)) = .C ∧
      ((F.lengthWord t 2).map criticalMargin).sum +
          criticalMargin (F.index t) -
          criticalMargin (F.index (t + 2)) = 1) ∨
    (O.transitionSymbol (F.index t) (F.index (t + 1)) = .A ∧
      O.transitionSymbol (F.index (t + 1)) (F.index (t + 2)) = .A ∧
      O.transitionSymbol (F.index (t + 2)) (F.index (t + 3)) = .C ∧
      ((F.lengthWord t 3).map criticalMargin).sum +
          criticalMargin (F.index t) -
          criticalMargin (F.index (t + 3)) = 1) := by
  rcases F.local_C_AC_AAC_cases_of_globalCST G S hStandard t with
    hC | hAC | hAAC
  · left
    have hTel := F.count_C_eq_margin_sum_add_start_sub_end t 1
    have hCount : (F.symbolWord t 1).count .C = 1 := by
      simp [FutureMinima.symbolWord, hC]
    rw [hCount] at hTel
    norm_num at hTel
    exact ⟨hC, hTel.symm⟩
  · right
    left
    have hTel := F.count_C_eq_margin_sum_add_start_sub_end t 2
    have hCount : (F.symbolWord t 2).count .C = 1 := by
      simp [FutureMinima.symbolWord, hAC.1, hAC.2, Nat.add_assoc]
    rw [hCount] at hTel
    norm_num at hTel
    exact ⟨hAC.1, hAC.2, hTel.symm⟩
  · right
    right
    have hTel := F.count_C_eq_margin_sum_add_start_sub_end t 3
    have hCount : (F.symbolWord t 3).count .C = 1 := by
      simp [FutureMinima.symbolWord, hAAC.1, hAAC.2.1, hAAC.2.2,
        Nat.add_assoc]
    rw [hCount] at hTel
    norm_num at hTel
    exact ⟨hAAC.1, hAAC.2.1, hAAC.2.2, hTel.symm⟩

end FutureMinima
end OddOrbit
end Collatz3
