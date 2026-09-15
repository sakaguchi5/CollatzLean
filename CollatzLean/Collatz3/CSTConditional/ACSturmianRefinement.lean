import CollatzLean.Collatz3.CSTConditional.FutureMinimumCutGeometry
import CollatzLean.Collatz3.CSTConditional.FlatStructure
import CollatzLean.Collatz3.CSTConditional.ACStructure
import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumNoTripleRise

/-!
# Collatz3 CSTConditional: A/C transition と absolute Sturmian step の精密化

Global CST で raw `B` が消えた後の next-future-minimum transition は `A` または `C`。
ここでは新しい alphabet を作らず、既存の

* `transitionSymbol`
* `survivorSturmianStep`
* proper-tail carry / excess

だけでさらに細かく読む。

中心結果は次である。

* `A` transition の開始 absolute Sturmian step は必ず `1`。
* 非自明 `A` block では先頭一歩を除いた proper tail が exact `(carry,excess)=(1,1)`。
* 長さ一の `C` は Sturmian step `0`。
* 非自明 `C` は
  `step=0, tail=(1,1)` または `step=1, tail=(0,1)` の二型。

`C0/C1` の新しい inductive type は導入しない。
必要な分類は conjunction / disjunction の theorem だけで保持する。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
Global CST 下の `A` transition は開始位置の absolute survivor Sturmian step を `1` に固定する。
-/
theorem nextFutureMinimum_symbol_A_sturmianStep_eq_one_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hA : O.transitionSymbol i j = .A) :
    survivorSturmianStep i = 1 := by
  have hRise :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 :=
    (O.nextFutureMinimum_symbol_A_iff_defect_succ SInf hNext).1 hA
  have hOne := O.futureMinimum_localRoofDefect_one_eq_zero SInf hStart
  have hStepExact :=
    O.futureMinimum_defect_eq_start_add_localRoofDefect_add_carry_of_globalCST
      G SInf hStart 1
  rw [hOne, Nat.add_zero] at hStepExact
  have hCarryOne : Critical.beattyCarry i 1 = 1 := by
    by_cases hShort : j = i + 1
    · subst j
      omega
    · have hij : i < j := hNext.1
      have hInternal : i + 1 < j := by omega
      have hTailDefect :=
        O.nextFutureMinimum_defect_le_internal
          SInf hNext (k := i + 1) (by omega) hInternal
      have hCarryBound := Critical.beattyCarry_le_one i 1
      omega
  have hBridge := Bridge.survivorSturmianStep_eq_beattyCarry_one i
  rw [hBridge]
  exact hCarryOne

/--
非自明 `A` block では、先頭一歩を除いた proper tail が exact `(1,1)`。

これは whole A rise が開始一歩ですでに作られ、その defect level を終点まで維持することを表す。
-/
theorem nextFutureMinimum_symbol_A_nontrivial_tail_one_one_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hA : O.transitionSymbol i j = .A)
    (hLong : i + 1 < j) :
    Critical.beattyCarry (i + 1) (j - (i + 1)) = 1 ∧
      O.segmentBeattyExcess (i + 1) (j - (i + 1)) = 1 := by
  have hRise :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 :=
    (O.nextFutureMinimum_symbol_A_iff_defect_succ SInf hNext).1 hA
  have hStepOne :=
    O.nextFutureMinimum_symbol_A_sturmianStep_eq_one_of_globalCST
      G SInf hStart hNext hA
  have hOne := O.futureMinimum_localRoofDefect_one_eq_zero SInf hStart
  have hStepExact :=
    O.futureMinimum_defect_eq_start_add_localRoofDefect_add_carry_of_globalCST
      G SInf hStart 1
  rw [hOne, Nat.add_zero] at hStepExact
  have hFirstCarry : Critical.beattyCarry i 1 = 1 := by
    have hBridge := Bridge.survivorSturmianStep_eq_beattyCarry_one i
    rw [hBridge] at hStepOne
    exact hStepOne
  have hTailStructure :=
    O.nextFutureMinimum_nontrivial_jumpTwo_suffixExcessOne_of_globalCST
      G SInf hStart hNext hLong
  have hTailExcess := hTailStructure.2
  have hTailBalance :=
    O.nextFutureMinimum_properSuffix_defect_balance
      SInf hNext (k := i + 1) (by omega) hLong
  have hTailCarry :
      Critical.beattyCarry (i + 1) (j - (i + 1)) = 1 := by
    rw [hTailExcess, hRise] at hTailBalance
    rw [hFirstCarry] at hStepExact
    omega
  exact ⟨hTailCarry, hTailExcess⟩

/--
長さ一の `C` transition では、開始点 `i` の absolute Sturmian step は `0`。
-/
theorem nextFutureMinimum_symbol_C_length_one_sturmianStep_eq_zero
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hNext : O.NextFutureMinimum i j)
    (hC : O.transitionSymbol i j = .C)
    (hLengthOne : j = i + 1) :
    survivorSturmianStep i = 0 := by
  subst j
  have hCarry : Critical.beattyCarry i 1 = 0 := by
    have h := (O.transitionSymbol_eq_C_iff i (i + 1)).1 hC
    simpa using h
  have hBridge := Bridge.survivorSturmianStep_eq_beattyCarry_one i
  rw [hBridge]
  exact hCarry

/--
非自明 `C` block の exact 二分岐。

* `step=0` なら proper tail は `(carry,excess)=(1,1)`。
* `step=1` なら proper tail は `(carry,excess)=(0,1)`。
-/
theorem nextFutureMinimum_symbol_C_nontrivial_sturmianTail_cases_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hC : O.transitionSymbol i j = .C)
    (hLong : i + 1 < j) :
    (survivorSturmianStep i = 0 ∧
        Critical.beattyCarry (i + 1) (j - (i + 1)) = 1 ∧
        O.segmentBeattyExcess (i + 1) (j - (i + 1)) = 1) ∨
      (survivorSturmianStep i = 1 ∧
        Critical.beattyCarry (i + 1) (j - (i + 1)) = 0 ∧
        O.segmentBeattyExcess (i + 1) (j - (i + 1)) = 1) := by
  have hFlat :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i :=
    (O.nextFutureMinimum_defect_flat_iff_symbol_C_of_globalCST
      G SInf hStart hNext).2 hC
  have hOne := O.futureMinimum_localRoofDefect_one_eq_zero SInf hStart
  have hStepExact :=
    O.futureMinimum_defect_eq_start_add_localRoofDefect_add_carry_of_globalCST
      G SInf hStart 1
  rw [hOne, Nat.add_zero] at hStepExact
  have hTailStructure :=
    O.nextFutureMinimum_nontrivial_jumpTwo_suffixExcessOne_of_globalCST
      G SInf hStart hNext hLong
  have hTailExcess := hTailStructure.2
  have hTailBalance :=
    O.nextFutureMinimum_properSuffix_defect_balance
      SInf hNext (k := i + 1) (by omega) hLong
  rcases Critical.beattyCarry_eq_zero_or_one i 1 with hFirstZero | hFirstOne
  · left
    have hTailCarry :
        Critical.beattyCarry (i + 1) (j - (i + 1)) = 1 := by
      rw [hTailExcess, hFlat] at hTailBalance
      rw [hFirstZero] at hStepExact
      omega
    have hStepZero : survivorSturmianStep i = 0 := by
      have hBridge := Bridge.survivorSturmianStep_eq_beattyCarry_one i
      rw [hBridge]
      exact hFirstZero
    exact ⟨hStepZero, hTailCarry, hTailExcess⟩
  · right
    have hTailCarry :
        Critical.beattyCarry (i + 1) (j - (i + 1)) = 0 := by
      rw [hTailExcess, hFlat] at hTailBalance
      rw [hFirstOne] at hStepExact
      omega
    have hStepOne : survivorSturmianStep i = 1 := by
      have hBridge := Bridge.survivorSturmianStep_eq_beattyCarry_one i
      rw [hBridge]
      exact hFirstOne
    exact ⟨hStepOne, hTailCarry, hTailExcess⟩

end OddOrbit
end Collatz3
