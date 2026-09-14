import CollatzLean.Collatz3.CSTConditional.ACStructure
import CollatzLean.Collatz3.CSTConditional.MarginMass
import CollatzLean.Collatz3.Bridge.SurvivorFutureMinimumABCRigidity

/-!
# Collatz3 CSTConditional: AC word の有限文字数算術

Global CST 下では future-minimum symbol word から `B` が完全に消える。
この事実を有限 word の count identity へ持ち上げる。

主な帰結は

* `#B = 0`
* `#A + #C = q`
* survivor 標準列では `defectGrowth = #A`
* 従って `defectGrowth + #C = q`
* 三状態 automaton の既存評価 `#A ≤ 2#C+2` と合わせて
  `q ≤ 3#C+2` および `3*defectGrowth ≤ 2q+2`

である。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

namespace FutureMinima

/-- Global CST 下では有限 future-minimum symbol word に `B` は一文字もない。 -/
theorem symbolWord_count_B_eq_zero_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (n q : ℕ) :
    (F.symbolWord n q).count .B = 0 := by
  induction q generalizing n with
  | zero =>
      simp [symbolWord]
  | succ q ih =>
      have hNoB :=
        O.transitionSymbol_ne_B_of_futureMinimum_of_globalCST
          (j := F.index (n + 1)) G (F.minimum n)
      simp [symbolWord, hNoB, ih]

/--
Global CST 下では有限 symbol word の全 transition 数は `#A + #C` に exact 分解される。
-/
theorem symbolWord_count_A_add_count_C_eq_transitions_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (n q : ℕ) :
    (F.symbolWord n q).count .A +
        (F.symbolWord n q).count .C = q := by
  induction q generalizing n with
  | zero =>
      simp [symbolWord]
  | succ q ih =>
      rcases O.transitionSymbol_A_or_C_of_futureMinimum_of_globalCST
          (j := F.index (n + 1)) G (F.minimum n) with hA | hC
      · simp [symbolWord, hA]
        have hTail := ih (n + 1)
        omega
      · simp [symbolWord, hC]
        have hTail := ih (n + 1)
        omega

/-- `#C = q - #A` の自然数版。 -/
theorem symbolWord_count_C_eq_transitions_sub_count_A_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (n q : ℕ) :
    (F.symbolWord n q).count .C =
      q - (F.symbolWord n q).count .A := by
  have h :=
    F.symbolWord_count_A_add_count_C_eq_transitions_of_globalCST G n q
  omega

/-- `#A = q - #C` の自然数版。 -/
theorem symbolWord_count_A_eq_transitions_sub_count_C_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (n q : ℕ) :
    (F.symbolWord n q).count .A =
      q - (F.symbolWord n q).count .C := by
  have h :=
    F.symbolWord_count_A_add_count_C_eq_transitions_of_globalCST G n q
  omega

/-- Global CST 下の標準 survivor 列では defect growth は `#A` と exact に一致する。 -/
theorem defectGrowth_eq_count_A_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    infiniteSurvivorDefect O.exponent (F.index (n + q)) -
        infiniteSurvivorDefect O.exponent (F.index n) =
      (F.symbolWord n q).count .A := by
  have h :=
    F.defect_end_eq_start_add_count_A_of_globalCST
      G S hStandard n q
  omega

/--
Global CST 下の exact 自然数保存則。

`defectGrowth + #C = q`。

各 transition は defect に変換される `A` か、margin wrap を起こす `C` のどちらか。
-/
theorem defectGrowth_add_count_C_eq_transitions_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    (infiniteSurvivorDefect O.exponent (F.index (n + q)) -
        infiniteSurvivorDefect O.exponent (F.index n)) +
      (F.symbolWord n q).count .C = q := by
  have hGrowth :=
    F.defectGrowth_eq_count_A_of_globalCST G S hStandard n q
  have hCount :=
    F.symbolWord_count_A_add_count_C_eq_transitions_of_globalCST G n q
  omega

/-- `#C = q - defectGrowth` の exact 版。 -/
theorem count_C_eq_transitions_sub_defectGrowth_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    (F.symbolWord n q).count .C =
      q -
        (infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n)) := by
  have h :=
    F.defectGrowth_add_count_C_eq_transitions_of_globalCST
      G S hStandard n q
  omega

/--
既存 automaton bound `#A ≤ 2#C+2` と AC 分解を合わせると
`q ≤ 3#C+2`。

端の未完 cell が高々二個の `A` を持てることに対応する。
-/
theorem transitions_le_three_count_C_add_two_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    q ≤ 3 * (F.symbolWord n q).count .C + 2 := by
  have hPartition :=
    F.symbolWord_count_A_add_count_C_eq_transitions_of_globalCST G n q
  have hABC :=
    F.symbolWord_count_A_le_two_count_C_add_two S hStandard n q
  omega

/-- 同じ評価を `q-2 ≤ 3#C` と書いた版。 -/
theorem transitions_sub_two_le_three_count_C_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    q - 2 ≤ 3 * (F.symbolWord n q).count .C := by
  have h :=
    F.transitions_le_three_count_C_add_two_of_globalCST
      G S hStandard n q
  omega

/--
Global CST 下では transition 数が3以上なら、その区間には少なくとも一つ `C` がある。
-/
theorem count_C_pos_of_three_le_transitions_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n q : ℕ}
    (hq : 3 ≤ q) :
    0 < (F.symbolWord n q).count .C := by
  have h :=
    F.transitions_le_three_count_C_add_two_of_globalCST
      G S hStandard n q
  omega

/-- `C` が一度もない有限区間の長さは高々2。 -/
theorem transitions_le_two_of_count_C_eq_zero_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    {n q : ℕ}
    (hC : (F.symbolWord n q).count .C = 0) :
    q ≤ 2 := by
  have h :=
    F.transitions_le_three_count_C_add_two_of_globalCST
      G S hStandard n q
  rw [hC] at h
  omega

/--
Global CST 下の defect growth 密度評価。

`3 * defectGrowth ≤ 2q + 2`。

長い future-minimum 列で defect は transition 数の約 `2/3` より速く増えられない。
-/
theorem three_mul_defectGrowth_le_two_mul_transitions_add_two_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    3 *
        (infiniteSurvivorDefect O.exponent (F.index (n + q)) -
          infiniteSurvivorDefect O.exponent (F.index n)) ≤
      2 * q + 2 := by
  have hGrowth :=
    F.defectGrowth_eq_count_A_of_globalCST G S hStandard n q
  have hPartition :=
    F.symbolWord_count_A_add_count_C_eq_transitions_of_globalCST G n q
  have hABC :=
    F.symbolWord_count_A_le_two_count_C_add_two S hStandard n q
  omega

/-- defect growth は transition 数そのものを越えない。 -/
theorem defectGrowth_le_transitions_of_globalCST
    {O : Collatz3.OddOrbit}
    (F : O.FutureMinima)
    (G : GlobalCST)
    (S : O.IsInfiniteCoefficientSurvivor)
    (hStandard : F.IsStandard)
    (n q : ℕ) :
    infiniteSurvivorDefect O.exponent (F.index (n + q)) -
        infiniteSurvivorDefect O.exponent (F.index n) ≤ q := by
  have h :=
    F.defectGrowth_add_count_C_eq_transitions_of_globalCST
      G S hStandard n q
  omega

end FutureMinima
end OddOrbit
end Collatz3
