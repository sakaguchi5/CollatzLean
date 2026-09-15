import CollatzLean.Collatz3.CSTConditional.ACSturmianRefinement
import CollatzLean.Collatz3.CSTConditional.FlatStructure
import CollatzLean.Collatz3.Bridge.SurvivorFutureMinimumABCRigidity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Collatz3 CSTConditional: 全 A/C block の universal critical-margin floor

既存 unconditional rigidity では `A` block に対して

`criticalMargin(length) >= log2(4/3)`

が証明されている。
Global CST 下ではさらに、`A/C` の別に関係なく非自明 next-future-minimum block が

`beattyIndex r = beattyIndex (r-1) + 2`

を満たす。長さ一では margin が exact に `log2(4/3)`。
従って Global CST 下の **すべての** next-future-minimum block が同じ margin floor を持つ。

新しい margin notion は追加しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
Global CST 下の任意 next-future-minimum block length は
`criticalMargin >= log2(4/3)` を満たす。
-/
theorem nextFutureMinimum_logb_four_thirds_le_criticalMargin_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    Real.logb 2 ((4 : ℝ) / 3) ≤
      criticalMargin (j - i) := by
  let r : ℕ := j - i
  have hrPos : 0 < r := by
    dsimp [r]
    exact Nat.sub_pos_of_lt hNext.1
  by_cases hrOne : r = 1
  · change Real.logb 2 ((4 : ℝ) / 3) ≤ criticalMargin r
    rw [hrOne, criticalMargin_eq_beattyIndex_add_one_sub]
    rw [Critical.beattyIndex_one]
    rw [logb_two_four_div_three_eq_two_sub_logb_three]
    norm_num
  · have hrGt : 1 < r := by omega
    have hLong : i + 1 < j := by
      dsimp [r] at hrGt
      omega
    have hStructure :=
      O.nextFutureMinimum_nontrivial_jumpTwo_suffixExcessOne_of_globalCST
        G SInf hStart hNext hLong
    have hJump :
        Critical.beattyIndex r =
          Critical.beattyIndex (r - 1) + 2 := by
      simpa [r] using hStructure.1
    have hCell := beattyIndex_isLowerMechanical_logb_two_three (r - 1)
    change
      (Critical.beattyIndex (r - 1) : ℝ) ≤
          ((r - 1 : ℕ) : ℝ) * Real.logb 2 3 ∧
        ((r - 1 : ℕ) : ℝ) * Real.logb 2 3 <
          (Critical.beattyIndex (r - 1) : ℝ) + 1 at hCell
    have hJumpR :
        (Critical.beattyIndex r : ℝ) =
          (Critical.beattyIndex (r - 1) : ℝ) + 2 := by
      exact_mod_cast hJump
    have hrDecomp : r = (r - 1) + 1 := by omega
    have hrDecompR :
        (r : ℝ) = ((r - 1 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hrDecomp
    change Real.logb 2 ((4 : ℝ) / 3) ≤ criticalMargin r
    rw [logb_two_four_div_three_eq_two_sub_logb_three]
    rw [criticalMargin_eq_beattyIndex_add_one_sub, hJumpR, hrDecompR]
    linarith [hCell.2]

end OddOrbit
end Collatz3
