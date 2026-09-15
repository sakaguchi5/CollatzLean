import CollatzLean.Collatz3.CSTConditional.ACSturmianRefinement
import CollatzLean.Collatz3.Bridge.SurvivorDefectActualResidue
import CollatzLean.Collatz3.Bridge.SurvivorDefectNormalizedActual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Collatz3 CSTConditional: actual residue fraction の一歩 dynamics

既存 actual compact coordinate は

`V_m = k_m + theta_m`

と ordinary quotient `k_m` と residue fraction `theta_m` に exact 分解される。
また survivor 一歩 recurrence は

`V_(m+1)
  = (3 V_m + 2^(-(delta_m+2))) / 2^(1+s_m)`

である。

この二式を代入するだけで `theta_m` 自身の exact 一歩 recurrence を得る。
新しい residue state は導入しない。

さらに Global CST 下の `A` transition では前段により開始 Sturmian step が `1` なので、
分母は exact `4` に固定される。
これは actual residue dynamics と completion 側の `s=1` branch を同じ局所記号で
比較するための直接 bridge になる。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
actual residue fraction `theta` の一般一歩 recurrence。
-/
theorem defectActualResidueFraction_succ_eq
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (m : ℕ) :
    O.defectActualResidueFraction (m + 1) =
      (3 *
          ((O.defectActualQuotient m : ℝ) +
            O.defectActualResidueFraction m) +
          1 / (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2)) /
        (2 : ℝ) ^ (1 + survivorSturmianStep m) -
      (O.defectActualQuotient (m + 1) : ℝ) := by
  have hStep := O.defectNormalizedActualValue_succ SInf m
  rw [O.defectNormalizedActualValue_eq_quotient_add_residueFraction m] at hStep
  rw [O.defectNormalizedActualValue_eq_quotient_add_residueFraction (m + 1)] at hStep
  linarith

/-- Sturmian step `0` branch では actual residue recurrence の分母は exact `2`。 -/
theorem defectActualResidueFraction_succ_eq_of_sturmianStep_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hStepZero : survivorSturmianStep m = 0) :
    O.defectActualResidueFraction (m + 1) =
      (3 *
          ((O.defectActualQuotient m : ℝ) +
            O.defectActualResidueFraction m) +
          1 / (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2)) / 2 -
      (O.defectActualQuotient (m + 1) : ℝ) := by
  rw [O.defectActualResidueFraction_succ_eq SInf m, hStepZero]
  norm_num

/-- Sturmian step `1` branch では actual residue recurrence の分母は exact `4`。 -/
theorem defectActualResidueFraction_succ_eq_of_sturmianStep_one
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {m : ℕ}
    (hStepOne : survivorSturmianStep m = 1) :
    O.defectActualResidueFraction (m + 1) =
      (3 *
          ((O.defectActualQuotient m : ℝ) +
            O.defectActualResidueFraction m) +
          1 / (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent m + 2)) / 4 -
      (O.defectActualQuotient (m + 1) : ℝ) := by
  rw [O.defectActualResidueFraction_succ_eq SInf m, hStepOne]
  norm_num

/--
Global CST 下で `A` transition が始まる位置では、actual residue dynamics は
必ず `s=1`、すなわち denominator `4` branch に入る。
-/
theorem defectActualResidueFraction_succ_eq_of_symbol_A_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hA : O.transitionSymbol i j = .A) :
    O.defectActualResidueFraction (i + 1) =
      (3 *
          ((O.defectActualQuotient i : ℝ) +
            O.defectActualResidueFraction i) +
          1 / (2 : ℝ) ^ (infiniteSurvivorDefect O.exponent i + 2)) / 4 -
      (O.defectActualQuotient (i + 1) : ℝ) := by
  have hStepOne :=
    O.nextFutureMinimum_symbol_A_sturmianStep_eq_one_of_globalCST
      G SInf hStart hNext hA
  exact
    O.defectActualResidueFraction_succ_eq_of_sturmianStep_one
      SInf hStepOne

end OddOrbit
end Collatz3
