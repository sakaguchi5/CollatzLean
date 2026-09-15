import CollatzLean.Collatz3.CSTConditional.FutureMinimumLocalRoof
import CollatzLean.Collatz3.CSTConditional.AFutureMinimumDefectFloor
import CollatzLean.Collatz3.Bridge.SurvivorSegmentDefect

/-!
# Collatz3 CSTConditional: future minimum の global defect と local roof defect

Global CST の下で future minimum `start` を固定する。
長さ `length` の actual segment に対する local roof defect

`d_start(length) = beattyIndex(length) - twoSteps(segment)`

は、global survivor defect の増分と独立な量ではない。
Beatty index の加法公式と actual two-depth の加法公式を合わせると

`delta_(start+length)
  = delta_start + d_start(length) + beattyCarry(start,length)`

が exact に成り立つ。

新しい defect / state / profile は定義しない。
既存の `infiniteSurvivorDefect` と `futureMinimum_localRoofDefect` の関係だけを
薄い derived theorem として記録する。

さらに `LinearDefectLowerBound` を仮定すると、固定 future-minimum anchor から見た
local roof defect は任意の固定深さを最終的に越える。
従って既存の「bounded depth band は density zero」を、A 型では
「bounded depth band は tail から完全に消える」まで強化できる。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
Global CST future minimum を基点にした exact defect identity。

`delta_(start+length) = delta_start + localRoofDefect + carry`。
-/
theorem futureMinimum_defect_eq_start_add_localRoofDefect_add_carry_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    (length : ℕ) :
    infiniteSurvivorDefect O.exponent (start + length) =
      infiniteSurvivorDefect O.exponent start +
        O.futureMinimum_localRoofDefect start length +
          Critical.beattyCarry start length := by
  have hLocal :=
    O.segmentTwoSteps_add_futureMinimum_localRoofDefect_eq_beattyIndex_of_globalCST
      G hStart length
  have hDepth := O.infinitePrefixDepth_add_eq start length
  have hBeatty := Critical.beattyIndex_add_eq start length
  have hStartDefect := beattyIndex_eq_prefixDepth_add_defect SInf start
  have hEndDefect :=
    beattyIndex_eq_prefixDepth_add_defect SInf (start + length)
  omega

/--
上の exact identity から、local roof defect を除いた global defect growth は
高々一個の Beatty carry だけである。
-/
theorem futureMinimum_defect_le_start_add_localRoofDefect_add_one_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start)
    (length : ℕ) :
    infiniteSurvivorDefect O.exponent (start + length) ≤
      infiniteSurvivorDefect O.exponent start +
        O.futureMinimum_localRoofDefect start length + 1 := by
  have hExact :=
    O.futureMinimum_defect_eq_start_add_localRoofDefect_add_carry_of_globalCST
      G SInf hStart length
  have hCarry := Critical.beattyCarry_le_one start length
  omega

/--
survivor future minimum の最初の一 odd-step は local Beatty roof に exact に接する。

future minimum では exponent が `1`、かつ `beattyIndex 1 = 1` なので
`futureMinimum_localRoofDefect start 1 = 0`。
-/
theorem futureMinimum_localRoofDefect_one_eq_zero
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {start : ℕ}
    (hStart : O.FutureMinimumAt start) :
    O.futureMinimum_localRoofDefect start 1 = 0 := by
  have he : O.exponent start = 1 :=
    O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor SInf hStart
  unfold futureMinimum_localRoofDefect
  rw [show 1 = 0 + 1 by omega, O.segmentWord_succ]
  simp [he, Critical.beattyIndex_one]

/--
A 型の linear defect lower bound が有効な late future minimum を固定すると、
任意の固定 roof depth `D` は sufficiently long local segment では必ず超えられる。

これは density statement ではなく eventual statement である。
-/
theorem exists_localRoofDefect_gt_after_of_linearDefect
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N start : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ start)
    (hStart : O.FutureMinimumAt start)
    (D : ℕ) :
    ∃ R : ℕ,
      ∀ length : ℕ,
        R ≤ length →
          D < O.futureMinimum_localRoofDefect start length := by
  let R : ℕ :=
    K * (infiniteSurvivorDefect O.exponent start + (D + 1)) + 1
  refine ⟨R, ?_⟩
  intro length hLength
  have hIndex :
      K * (infiniteSurvivorDefect O.exponent start + (D + 1)) <
        start + length := by
    dsimp [R] at hLength
    omega
  have hFloor :=
    O.futureMinimum_defect_add_succ_le_of_scaled_index_lt_of_linearDefect
      hLinear hLate (by omega : start ≤ start + length) hIndex
  have hExact :=
    O.futureMinimum_defect_eq_start_add_localRoofDefect_add_carry_of_globalCST
      G SInf hStart length
  have hCarry := Critical.beattyCarry_le_one start length
  omega

end OddOrbit
end Collatz3
