import CollatzLean.Collatz3.CSTConditional.FutureMinimum
import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumNoTripleRise

/-!
# Collatz3 CSTConditional: AC 二文字系の局所構造

このファイルは `GlobalCST` を仮定した場合だけ使う条件付き結果を置く。

Global CST により future minimum を始点とする有限 segment の Beatty excess は `0` になる。
特に next-future-minimum block では既存の roof lower bound と合わせて total two-depth が
`beattyIndex r` に exact に一致する。

従って next-future-minimum transition は

* `A` : carry `1`, defect `+1`, margin 和 `≤ 1`
* `C` : carry `0`, defect flat, margin 和 `> 1`

の二文字だけになる。

さらに unconditional に証明済みの三連続 rise 禁止を合わせると、任意位置から見た
最初の `C` までの局所 cell は exact に

* `C`
* `AC`
* `AAC`

の三型のどれかになる。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
Global CST 下では next-future-minimum block の total two-depth は
その block 長 `r=j-i` の Beatty roof `beattyIndex r` に exact に一致する。
-/
theorem nextFutureMinimum_segmentTwoSteps_eq_beattyIndex_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    Word.twoSteps (O.segmentWord i (j - i)) =
      Critical.beattyIndex (j - i) := by
  have hZero :=
    O.segmentBeattyExcess_eq_zero_of_futureMinimum
      (r := j - i) G hStart
  have hDepth :=
    O.nextFutureMinimum_beattyIndex_add_segmentBeattyExcess_eq_segmentTwoSteps
      hNext
  rw [hZero] at hDepth
  omega

/--
Global CST 下の next-future-minimum whole block は coefficient として strict expanding。

actual endpoint は future minimum 性により始点以上だが、pure coefficient だけを見ると
`2^H < 3^r` 側に固定される。
-/
theorem nextFutureMinimum_twoPow_lt_threePow_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    2 ^ Word.twoSteps (O.segmentWord i (j - i)) <
      3 ^ (j - i) := by
  have hDepth :=
    O.nextFutureMinimum_segmentTwoSteps_eq_beattyIndex_of_globalCST
      G hStart hNext
  rw [hDepth]
  exact Critical.beattyIndex_lower_strict (Nat.sub_pos_of_lt hNext.1)

/--
Global CST 下では future minimum 起点の raw symbol `A` は carry `1` と exact に同値。

excess `0` は Global CST から自動的に従うので、`A` の判定に残る情報は carry だけ。
-/
theorem transitionSymbol_eq_A_iff_carry_one_of_futureMinimum_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i) :
    O.transitionSymbol i j = .A ↔
      Critical.beattyCarry i (j - i) = 1 := by
  have hZero :=
    O.segmentBeattyExcess_eq_zero_of_futureMinimum
      (r := j - i) G hStart
  rw [O.transitionSymbol_eq_A_iff i j]
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, hZero⟩

/--
Global CST 下では `A` と critical-margin threshold の下側が exact に一致する。
-/
theorem transitionSymbol_eq_A_iff_criticalMargin_add_le_one_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i) :
    O.transitionSymbol i j = .A ↔
      criticalMargin i + criticalMargin (j - i) ≤ 1 := by
  rw [O.transitionSymbol_eq_A_iff_carry_one_of_futureMinimum_of_globalCST G hStart]
  exact beattyCarry_eq_one_iff_criticalMargin_add_le_one i (j - i)

/--
Global CST 下では next-future-minimum の defect 増分は Beatty carry そのもの。

一般の保存則 `δ_j + excess = δ_i + carry` で excess が `0` に固定されるため。
-/
theorem nextFutureMinimum_defect_eq_add_carry_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    infiniteSurvivorDefect O.exponent j =
      infiniteSurvivorDefect O.exponent i +
        Critical.beattyCarry i (j - i) := by
  have hZero :=
    O.segmentBeattyExcess_eq_zero_of_futureMinimum
      (r := j - i) G hStart
  have hBalance := O.nextFutureMinimum_defect_balance S hNext
  rw [hZero] at hBalance
  omega

/--
Global CST 下では next-future-minimum の defect `+1` と margin threshold の下側が exact に同値。
-/
theorem nextFutureMinimum_defect_succ_iff_criticalMargin_add_le_one_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 ↔
      criticalMargin i + criticalMargin (j - i) ≤ 1 := by
  rw [← O.nextFutureMinimum_symbol_A_iff_defect_succ S hNext]
  exact
    O.transitionSymbol_eq_A_iff_criticalMargin_add_le_one_of_globalCST
      G hStart

/--
Global CST 下では next-future-minimum の defect flat と margin wrap `>1` が exact に同値。
-/
theorem nextFutureMinimum_defect_flat_iff_one_lt_criticalMargin_add_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i ↔
      1 < criticalMargin i + criticalMargin (j - i) := by
  rw [O.nextFutureMinimum_defect_flat_iff_symbol_C_of_globalCST
        G S hStart hNext]
  rw [O.transitionSymbol_eq_C_iff i j]
  exact beattyCarry_eq_zero_iff_one_lt_criticalMargin_add i (j - i)

/--
Global CST 下の next-future-minimum defect は一回ごとに「据え置き」か「+1」の二択。
-/
theorem nextFutureMinimum_defect_eq_or_succ_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i ∨
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1 := by
  rcases O.transitionSymbol_A_or_C_of_futureMinimum_of_globalCST
      (j := j) G hStart with hA | hC
  · right
    exact (O.nextFutureMinimum_symbol_A_iff_defect_succ S hNext).1 hA
  · left
    exact
      (O.nextFutureMinimum_defect_flat_iff_symbol_C_of_globalCST
        G S hStart hNext).2 hC

namespace FutureMinima

/--
Global CST 下の標準 future-minimum 列では、任意の連続三 transition の中に必ず `C` がある。

`B` が消えたので、三本とも `C` でないなら三本とも `A`。
これは unconditional な三連続 defect-rise 禁止と矛盾する。
-/
theorem three_consecutive_transitions_contains_C_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (t : ℕ) :
    O.transitionSymbol (F.index t) (F.index (t + 1)) = .C ∨
      O.transitionSymbol (F.index (t + 1)) (F.index (t + 2)) = .C ∨
      O.transitionSymbol (F.index (t + 2)) (F.index (t + 3)) = .C := by
  have hNext :
      ∀ u : ℕ,
        O.NextFutureMinimum (F.index u) (F.index (u + 1)) :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard
  rcases O.transitionSymbol_A_or_C_of_futureMinimum_of_globalCST
      (j := F.index (t + 1)) G (F.minimum t) with hA0 | hC0
  · rcases O.transitionSymbol_A_or_C_of_futureMinimum_of_globalCST
        (j := F.index (t + 2)) G (F.minimum (t + 1)) with hA1 | hC1
    · rcases O.transitionSymbol_A_or_C_of_futureMinimum_of_globalCST
          (j := F.index (t + 3)) G (F.minimum (t + 2)) with hA2 | hC2
      · have hRise0 :=
          (O.nextFutureMinimum_symbol_A_iff_defect_succ S (hNext t)).1 hA0
        have hRise1 :=
          (O.nextFutureMinimum_symbol_A_iff_defect_succ S (hNext (t + 1))).1 hA1
        have hRise2 :=
          (O.nextFutureMinimum_symbol_A_iff_defect_succ S (hNext (t + 2))).1 hA2
        exfalso
        exact
          O.not_three_consecutive_nextFutureMinimum_defect_rises
            S (F.minimum t) (hNext t) (hNext (t + 1)) (hNext (t + 2))
            ⟨hRise0, hRise1, hRise2⟩
      · exact Or.inr (Or.inr hC2)
    · exact Or.inr (Or.inl hC1)
  · exact Or.inl hC0

/--
Global CST 下で任意位置から最初の `C` までを見ると、局所 cell は exact に
`C / AC / AAC` の三型のどれか。
-/
theorem local_C_AC_AAC_cases_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (t : ℕ) :
    O.transitionSymbol (F.index t) (F.index (t + 1)) = .C ∨
      (O.transitionSymbol (F.index t) (F.index (t + 1)) = .A ∧
        O.transitionSymbol (F.index (t + 1)) (F.index (t + 2)) = .C) ∨
      (O.transitionSymbol (F.index t) (F.index (t + 1)) = .A ∧
        O.transitionSymbol (F.index (t + 1)) (F.index (t + 2)) = .A ∧
        O.transitionSymbol (F.index (t + 2)) (F.index (t + 3)) = .C) := by
  rcases O.transitionSymbol_A_or_C_of_futureMinimum_of_globalCST
      (j := F.index (t + 1)) G (F.minimum t) with hA0 | hC0
  · rcases O.transitionSymbol_A_or_C_of_futureMinimum_of_globalCST
        (j := F.index (t + 2)) G (F.minimum (t + 1)) with hA1 | hC1
    · have hThree :=
        F.three_consecutive_transitions_contains_C_of_globalCST
          G S hStandard t
      rcases hThree with hC0' | hC1' | hC2
      · rw [hA0] at hC0'
        contradiction
      · rw [hA1] at hC1'
        contradiction
      · exact Or.inr (Or.inr ⟨hA0, hA1, hC2⟩)
    · exact Or.inr (Or.inl ⟨hA0, hC1⟩)
  · exact Or.inl hC0

/-- Global CST 下では任意位置から高々三 transition 以内に `C` が現れる。 -/
theorem exists_C_within_three_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (t : ℕ) :
    ∃ d : ℕ,
      d ≤ 2 ∧
        O.transitionSymbol (F.index (t + d)) (F.index (t + d + 1)) = .C := by
  rcases F.local_C_AC_AAC_cases_of_globalCST G S hStandard t with
    hC | hAC | hAAC
  · exact ⟨0, by omega, by simpa using hC⟩
  · exact ⟨1, by omega, by simpa [Nat.add_assoc] using hAC.2⟩
  · exact ⟨2, by omega, by simpa [Nat.add_assoc] using hAAC.2.2⟩

/--
局所 `C / AC / AAC` cell は defect 増加量もそれぞれ exact `0 / 1 / 2`。
-/
theorem local_cell_defect_cases_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (t : ℕ) :
    (O.transitionSymbol (F.index t) (F.index (t + 1)) = .C ∧
      infiniteSurvivorDefect O.exponent (F.index (t + 1)) =
        infiniteSurvivorDefect O.exponent (F.index t)) ∨
    (O.transitionSymbol (F.index t) (F.index (t + 1)) = .A ∧
      O.transitionSymbol (F.index (t + 1)) (F.index (t + 2)) = .C ∧
      infiniteSurvivorDefect O.exponent (F.index (t + 2)) =
        infiniteSurvivorDefect O.exponent (F.index t) + 1) ∨
    (O.transitionSymbol (F.index t) (F.index (t + 1)) = .A ∧
      O.transitionSymbol (F.index (t + 1)) (F.index (t + 2)) = .A ∧
      O.transitionSymbol (F.index (t + 2)) (F.index (t + 3)) = .C ∧
      infiniteSurvivorDefect O.exponent (F.index (t + 3)) =
        infiniteSurvivorDefect O.exponent (F.index t) + 2) := by
  have hNext :
      ∀ u : ℕ,
        O.NextFutureMinimum (F.index u) (F.index (u + 1)) :=
    (F.isStandard_iff_nextFutureMinimum).1 hStandard
  rcases F.local_C_AC_AAC_cases_of_globalCST G S hStandard t with
    hC | hAC | hAAC
  · left
    refine ⟨hC, ?_⟩
    exact
      (O.nextFutureMinimum_defect_flat_iff_symbol_C_of_globalCST
        G S (F.minimum t) (hNext t)).2 hC
  · right
    left
    have hRise :=
      (O.nextFutureMinimum_symbol_A_iff_defect_succ S (hNext t)).1 hAC.1
    have hFlat :=
      (O.nextFutureMinimum_defect_flat_iff_symbol_C_of_globalCST
        G S (F.minimum (t + 1)) (hNext (t + 1))).2 hAC.2
    refine ⟨hAC.1, hAC.2, ?_⟩
    have hFlat' :
        infiniteSurvivorDefect O.exponent (F.index (t + 2)) =
          infiniteSurvivorDefect O.exponent (F.index (t + 1)) := by
      simpa [Nat.add_assoc] using hFlat
    omega
  · right
    right
    have hRise0 :=
      (O.nextFutureMinimum_symbol_A_iff_defect_succ S (hNext t)).1 hAAC.1
    have hRise1 :=
      (O.nextFutureMinimum_symbol_A_iff_defect_succ S (hNext (t + 1))).1 hAAC.2.1
    have hFlat :=
      (O.nextFutureMinimum_defect_flat_iff_symbol_C_of_globalCST
        G S (F.minimum (t + 2)) (hNext (t + 2))).2 hAAC.2.2
    refine ⟨hAAC.1, hAAC.2.1, hAAC.2.2, ?_⟩
    have hRise1' :
        infiniteSurvivorDefect O.exponent (F.index (t + 2)) =
          infiniteSurvivorDefect O.exponent (F.index (t + 1)) + 1 := by
      simpa [Nat.add_assoc] using hRise1
    have hFlat' :
        infiniteSurvivorDefect O.exponent (F.index (t + 3)) =
          infiniteSurvivorDefect O.exponent (F.index (t + 2)) := by
      simpa [Nat.add_assoc] using hFlat
    omega

end FutureMinima
end OddOrbit
end Collatz3
