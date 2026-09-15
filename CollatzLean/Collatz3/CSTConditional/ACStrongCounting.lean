import CollatzLean.Collatz3.CSTConditional.ACMarginFloor
import CollatzLean.Collatz3.CSTConditional.ACConservation
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional: universal margin floor から得る強い A-count bound

Global CST 下では各標準 future-minimum block length `r_t` に

`log2(4/3) <= criticalMargin(r_t)`

という一様下界がある。
一方 exact conservation law は

`#A + sum margin(r_t) + margin(start) - margin(end) = q`

と読める。
従って従来の finite-state bound `#A <= 2#C+2` より強い実数評価

`#A < log2(3/2) * q + 1`

を得る。

さらに `log2(3/2) < 3/5` を純粋な `((3/2)^5 < 2^3)` から証明し、
5 transitions の任意区間には `A` が高々3個、従って `C` が少なくとも2個あることを導く。

新しい counting state は導入しない。
-/

namespace Collatz3
namespace Bridge

/-- `1 - log2(4/3) = log2(3/2)`。 -/
theorem one_sub_logb_two_four_thirds_eq_logb_two_three_halves :
    1 - Real.logb 2 ((4 : ℝ) / 3) =
      Real.logb 2 ((3 : ℝ) / 2) := by
  rw [logb_two_four_div_three_eq_two_sub_logb_three]
  rw [logb_two_three_div_two]
  ring

/-- `log2(3/2) < 3/5` の exact rational comparison。 -/
theorem logb_two_three_halves_lt_three_fifths :
    Real.logb 2 ((3 : ℝ) / 2) < (3 : ℝ) / 5 := by
  have hArg : (0 : ℝ) < ((3 : ℝ) / 2) ^ (5 : ℕ) := by
    positivity
  have hPowLt : ((3 : ℝ) / 2) ^ (5 : ℕ) < (8 : ℝ) := by
    norm_num
  have hLogLt :
      Real.logb 2 (((3 : ℝ) / 2) ^ (5 : ℕ)) <
        Real.logb 2 (8 : ℝ) :=
    Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hArg hPowLt
  rw [Real.logb_pow] at hLogLt
  rw [show (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) by norm_num,
    Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] at hLogLt
  norm_num at hLogLt
  nlinarith

end Bridge

namespace OddOrbit

open Bridge
open CSTConditional

namespace FutureMinima

/--
標準 future-minimum `q` transitions の margin sum は
`q * log2(4/3)` 以上。
-/
theorem logb_four_thirds_mul_transitions_le_margin_sum_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    (q : ℝ) * Real.logb 2 ((4 : ℝ) / 3) ≤
      ((F.lengthWord n q).map criticalMargin).sum := by
  induction q generalizing n with
  | zero =>
      simp [FutureMinima.lengthWord]
  | succ q ih =>
      have hNext :
          O.NextFutureMinimum (F.index n) (F.index (n + 1)) :=
        (F.isStandard_iff_nextFutureMinimum).1 hStandard n
      have hFloor :=
        O.nextFutureMinimum_logb_four_thirds_le_criticalMargin_of_globalCST
          G SInf (F.minimum n) hNext
      have hTail := ih (n := n + 1)
      simp only [FutureMinima.lengthWord, List.map_cons, List.sum_cons]
      push_cast
      nlinarith

/--
Global CST 下の強い A-count estimate。

`#A < log2(3/2) * q + 1`。
-/
theorem count_A_cast_lt_logb_three_halves_mul_transitions_add_one_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    ((F.symbolWord n q).count .A : ℝ) <
      Real.logb 2 ((3 : ℝ) / 2) * (q : ℝ) + 1 := by
  have hConservation :=
    F.defectGrowth_add_margin_balance_eq_transitions_of_globalCST
      G SInf hStandard n q
  have hGrowthNat :=
    F.defectGrowth_eq_count_A_of_globalCST
      G SInf hStandard n q
  have hGrowthR :
      ((infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n) : ℕ) : ℝ) =
        ((F.symbolWord n q).count .A : ℝ) := by
    exact_mod_cast hGrowthNat
  rw [hGrowthR] at hConservation
  have hMargin :=
    F.logb_four_thirds_mul_transitions_le_margin_sum_of_globalCST
      G SInf hStandard n q
  have hStartPos := criticalMargin_pos (F.index n)
  have hEndLe := criticalMargin_le_one (F.index (n + q))
  have hCoeff := one_sub_logb_two_four_thirds_eq_logb_two_three_halves
  rw [← hCoeff]
  nlinarith

/--
任意の5 transition 区間には `A` は高々3個。
-/
theorem symbolWord_count_A_le_three_of_five_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n : ℕ) :
    (F.symbolWord n 5).count .A ≤ 3 := by
  have hBound :=
    F.count_A_cast_lt_logb_three_halves_mul_transitions_add_one_of_globalCST
      G SInf hStandard n 5
  have hLog := logb_two_three_halves_lt_three_fifths
  have hCast : ((F.symbolWord n 5).count .A : ℝ) < 4 := by
    norm_num at hBound
    nlinarith
  have hNat : (F.symbolWord n 5).count .A < 4 := by
    exact_mod_cast hCast
  omega

/--
任意の5 transition 区間には `C` が少なくとも2個ある。
従って従来の「3本に少なくとも1個 C」より強い有限 window 制約を得る。
-/
theorem two_le_symbolWord_count_C_of_five_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n : ℕ) :
    2 ≤ (F.symbolWord n 5).count .C := by
  have hPartition :=
    F.symbolWord_count_A_add_count_C_eq_transitions_of_globalCST G n 5
  have hA :=
    F.symbolWord_count_A_le_three_of_five_of_globalCST
      G SInf hStandard n
  omega

end FutureMinima
end OddOrbit
end Collatz3
