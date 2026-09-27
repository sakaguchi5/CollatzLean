import CollatzLean.Collatz3.CSTCarry.FinalWrapLowerBound
import Mathlib.Tactic.IntervalCases

/-!
# Collatz3 CSTCarry: P <= 26 の final wrap 排除

critical row envelope から得る上界

  S <= criticalWeightedDefectUpper P

と、final wrap 仮定から得る下界

  2^H + 4 * 3^P <= S

を比較する。

`P <= 26` では幅だけの有限算術として

  criticalWeightedDefectUpper P < 2^H + 4 * 3^P

が成立するため矛盾する。

ここでは `native_decide` に依存せず、Beatty index 0..26 の power-form certificate を
`norm_num` で確認してから有限区間を閉じる。
-/

namespace Collatz3
namespace CSTCarry

open Critical

/--
`2^q < 3^m <= 2^(q+1)` なら power-form Beatty index は exact に `q`。
-/
theorem beattyIndex_eq_of_power_bounds
    {m q : ℕ}
    (hLower : 2 ^ q < 3 ^ m)
    (hUpper : 3 ^ m ≤ 2 ^ (q + 1)) :
    beattyIndex m = q := by
  have hLe : beattyIndex m ≤ q := beattyIndex_le_of_upper hUpper
  by_contra hNe
  have hLt : beattyIndex m < q := by omega
  have hExp : beattyIndex m + 1 ≤ q := by omega
  have hBeattyUpper := beattyIndex_upper m
  have hPowLe :
      2 ^ (beattyIndex m + 1) ≤ 2 ^ q :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hExp
  have hBad : 3 ^ m ≤ 2 ^ q := le_trans hBeattyUpper hPowLe
  omega

@[simp] theorem beattyIndex_small_0 : beattyIndex 0 = 0 := by
  simp only [beattyIndex_zero]

@[simp] theorem beattyIndex_small_1 : beattyIndex 1 = 1 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_2 : beattyIndex 2 = 3 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_3 : beattyIndex 3 = 4 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_4 : beattyIndex 4 = 6 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_5 : beattyIndex 5 = 7 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_6 : beattyIndex 6 = 9 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_7 : beattyIndex 7 = 11 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_8 : beattyIndex 8 = 12 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_9 : beattyIndex 9 = 14 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_10 : beattyIndex 10 = 15 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_11 : beattyIndex 11 = 17 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_12 : beattyIndex 12 = 19 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_13 : beattyIndex 13 = 20 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_14 : beattyIndex 14 = 22 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_15 : beattyIndex 15 = 23 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_16 : beattyIndex 16 = 25 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_17 : beattyIndex 17 = 26 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_18 : beattyIndex 18 = 28 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_19 : beattyIndex 19 = 30 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_20 : beattyIndex 20 = 31 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_21 : beattyIndex 21 = 33 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_22 : beattyIndex 22 = 34 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_23 : beattyIndex 23 = 36 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_24 : beattyIndex 24 = 38 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_25 : beattyIndex 25 = 39 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

@[simp] theorem beattyIndex_small_26 : beattyIndex 26 = 41 := by
  apply beattyIndex_eq_of_power_bounds <;> norm_num

/--
幅 2..26 では critical defect envelope が final-wrap lower bound に届かない。
-/
theorem criticalWeightedDefectUpper_lt_finalWrapLower_le_26
    {P : ℕ}
    (hP2 : 2 ≤ P)
    (hP26 : P ≤ 26) :
    criticalWeightedDefectUpper P <
      2 ^ criticalTwoDepth P + 4 * 3 ^ P := by
  interval_cases P <;>
    norm_num [criticalWeightedDefectUpper, criticalTwoDepth]

/--
中心結論。

critical row envelope + strict actual ordering を満たす幅 `2 <= P <= 26` の
carry realization は final wrap で終われない。

従って final carry は必ず `2^criticalTwoDepth P` 未満。
-/
theorem CarryRealizes.final_lt_modulus_of_criticalRows_le_26
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ criticalTwoDepth P) rows 0 digits F)
    (hRows : CriticalCarryRows P rows)
    (hP2 : 2 ≤ P)
    (hP26 : P ≤ 26) :
    F < 2 ^ criticalTwoDepth P := by
  by_contra hNot
  have hFinalWrap : 2 ^ criticalTwoDepth P ≤ F := by omega
  have hLower :
      2 ^ criticalTwoDepth P + 4 * 3 ^ P ≤
        ferrersWeightedDefect rows :=
    h.finalWrap_defect_lowerBound_of_criticalRows
      hRows (by omega) hFinalWrap
  have hUpper :
      ferrersWeightedDefect rows ≤ criticalWeightedDefectUpper P :=
    hRows.weightedDefect_le_upper
  have hGap :=
    criticalWeightedDefectUpper_lt_finalWrapLower_le_26 hP2 hP26
  omega

end CSTCarry
end Collatz3
