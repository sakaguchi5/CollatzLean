import CollatzLean.Collatz3.CSTCarry.CriticalRowEnvelope
import CollatzLean.Collatz3.CSTCarry.CarryBudget
import CollatzLean.Collatz3.CSTCarry.CarryResidueBridge

/-!
# Collatz3 CSTCarry: final wrap の lower bound

このファイルでは

  final carry >= 2^H

を仮定したときに、critical row geometry から

  U = finalCarry - 2^H > 0,
  4 | U,
  ferrersWeightedDefect >= 2^H + 4 * 3^P

を導く。

`CriticalCarryRows` は actual profile bridge の代わりに置いた巨大 structure ではなく、
前段で分離した row envelope + strict actual ordering の薄い predicate である。
-/

namespace Collatz3
namespace CSTCarry

open Critical

/-- positive width なら critical terminal depth は少なくとも 2。 -/
theorem two_le_criticalTwoDepth_of_pos
    {P : ℕ}
    (hP : 0 < P) :
    2 ≤ criticalTwoDepth P := by
  have hOne : 1 ≤ P := hP
  have hThree : 3 ≤ 3 ^ P := by
    have hPow := Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) hOne
    simpa using hPow
  have hUpper := beattyIndex_upper P
  have hIdxPos : 0 < beattyIndex P := by
    by_contra hNot
    have hEq : beattyIndex P = 0 := by omega
    rw [hEq] at hUpper
    norm_num at hUpper
    omega
  unfold criticalTwoDepth
  omega

namespace CarryRealizes

/--
final wrap が起きているなら weighted defect は正。

defect が 0 なら global invariant と ternary digit range が直接矛盾する。
-/
theorem weightedDefect_pos_of_final_wrap
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hFinalWrap : 2 ^ H ≤ F) :
    0 < ferrersWeightedDefect rows := by
  by_contra hNot
  have hSZero : ferrersWeightedDefect rows = 0 := by omega
  have hInv := h.invariant_zero
  rw [hSZero, add_zero] at hInv
  have hC := h.ternaryDigitsValue_lt_pow
  have hMPos : 0 < 2 ^ H :=
    pow_pos (by decide : 0 < (2 : ℕ)) H
  have hLeftLt :
      2 ^ H * ternaryDigitsValue digits <
        2 ^ H * 3 ^ rows.length :=
    (Nat.mul_lt_mul_left hMPos).2 hC
  have hContr :
      3 ^ rows.length * F < 3 ^ rows.length * 2 ^ H := by
    calc
      3 ^ rows.length * F
          = 2 ^ H * ternaryDigitsValue digits := hInv.symm
      _ < 2 ^ H * 3 ^ rows.length := hLeftLt
      _ = 3 ^ rows.length * 2 ^ H := by ring
  have hGe :
      3 ^ rows.length * 2 ^ H ≤ 3 ^ rows.length * F :=
    Nat.mul_le_mul_left (3 ^ rows.length) hFinalWrap
  exact (not_lt_of_ge hGe) hContr

/--
critical rows の positive weighted defect は modulus の倍数にならない。
従って final wrap は equality `F = 2^H` では終われず、strict に上へ出る。
-/
theorem final_wrap_strict_of_criticalRows
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ criticalTwoDepth P) rows 0 digits F)
    (hRows : CriticalCarryRows P rows)
    (hFinalWrap : 2 ^ criticalTwoDepth P ≤ F) :
    2 ^ criticalTwoDepth P < F := by
  have hSPos := h.weightedDefect_pos_of_final_wrap hFinalWrap
  have hNotDvd :
      ¬ 2 ^ criticalTwoDepth P ∣ ferrersWeightedDefect rows :=
    weightedDefect_not_modulus_dvd_of_pos
      hRows.2 hRows.insideBitWidth hSPos
  by_contra hNot
  have hFEq : F = 2 ^ criticalTwoDepth P := by omega
  have hInv := h.invariant_zero
  rw [hFEq] at hInv
  have hRight :
      2 ^ criticalTwoDepth P ∣
        3 ^ rows.length * 2 ^ criticalTwoDepth P :=
    dvd_mul_left _ _
  rw [← hInv] at hRight
  have hLeft :
      2 ^ criticalTwoDepth P ∣
        2 ^ criticalTwoDepth P * ternaryDigitsValue digits :=
    dvd_mul_right _ _
  have hSub := Nat.dvd_sub hRight hLeft
  have hS :
      2 ^ criticalTwoDepth P ∣ ferrersWeightedDefect rows := by
    simpa using hSub
  exact hNotDvd hS

/-- critical row envelope の下では final carry 自身が 4 の倍数。 -/
theorem four_dvd_finalCarry_of_criticalRows
    {P H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hRows : CriticalCarryRows P rows)
    (hH : 2 ≤ H) :
    4 ∣ F := by
  have hM4 : 4 ∣ 2 ^ H := four_dvd_twoPow hH
  have hS4 : 4 ∣ ferrersWeightedDefect rows :=
    hRows.four_dvd_weightedDefect
  have hLeft :
      4 ∣ 2 ^ H * ternaryDigitsValue digits + ferrersWeightedDefect rows :=
    dvd_add
      (dvd_mul_of_dvd_left hM4 (ternaryDigitsValue digits))
      hS4
  have hProd : 4 ∣ 3 ^ rows.length * F := by
    rw [← h.invariant_zero]
    exact hLeft
  have hCoprime : Nat.Coprime 4 (3 ^ rows.length) := by
    exact (by decide : Nat.Coprime 4 3).pow_right rows.length
  exact (hCoprime.dvd_mul_left).1 hProd

/-- final overhang `F - 2^H` も 4 の倍数。 -/
theorem four_dvd_finalOverhang_of_criticalRows
    {P H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hRows : CriticalCarryRows P rows)
    (hH : 2 ≤ H) :
    4 ∣ F - 2 ^ H := by
  have hF4 := h.four_dvd_finalCarry_of_criticalRows hRows hH
  have hM4 : 4 ∣ 2 ^ H := four_dvd_twoPow hH
  exact Nat.dvd_sub hF4 hM4

/--
critical rows で final wrap が起きたと仮定すると、overhang は正の 4 の倍数。

会話中の `U` を `F - 2^H` と置いたときの exact な Lean 版。
-/
theorem finalWrap_overhang_pos_and_four_dvd_of_criticalRows
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ criticalTwoDepth P) rows 0 digits F)
    (hRows : CriticalCarryRows P rows)
    (hP : 0 < P)
    (hFinalWrap : 2 ^ criticalTwoDepth P ≤ F) :
    0 < F - 2 ^ criticalTwoDepth P ∧
      4 ∣ F - 2 ^ criticalTwoDepth P := by
  have hStrict := h.final_wrap_strict_of_criticalRows hRows hFinalWrap
  have hH : 2 ≤ criticalTwoDepth P := two_le_criticalTwoDepth_of_pos hP
  refine ⟨by omega, ?_⟩
  exact h.four_dvd_finalOverhang_of_criticalRows hRows hH

/--
final wrap 中の overhang は canonical Ferrers binary shift と exact に一致する。

safe-state bound により `F < 2 * 2^H` なので、一回 modulus を引くだけでよい。
-/
theorem finalOverhang_eq_ferrersBinaryShift
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hRows : RowsInsideBitWidth H rows)
    (hFinalWrap : 2 ^ H ≤ F) :
    F - 2 ^ H = ferrersBinaryShift H rows := by
  have hSafe := h.final_below_or_small_wrap_of_insideBitWidth hRows
  have hOverBound : 4 * (F - 2 ^ H) < 2 ^ H := by
    rcases hSafe with hBelow | hWrapped
    · omega
    · exact hWrapped.2
  have hOverLt : F - 2 ^ H < 2 ^ H := by omega
  have hDecomp : F = (F - 2 ^ H) + 2 ^ H := by omega
  have hMod : F % 2 ^ H = F - 2 ^ H := by
    rw [hDecomp, Nat.add_mod]
    simp [Nat.mod_eq_of_lt hOverLt]
  have hShift := h.final_mod_eq_ferrersBinaryShift
  omega

/--
final wrap の global invariant を overhang で exact に展開する。

`D` を ternary complement value とすると

  S = 2^H * (D+1) + 3^P * (F-2^H).
-/
theorem finalDefect_eq_complement_add_overhang
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hFinalWrap : 2 ^ H ≤ F) :
    ferrersWeightedDefect rows =
      2 ^ H * (ternaryComplementValue digits + 1) +
        3 ^ rows.length * (F - 2 ^ H) := by
  let C := ternaryDigitsValue digits
  let D := ternaryComplementValue digits
  let S := ferrersWeightedDefect rows
  let P := rows.length
  have hInv : 2 ^ H * C + S = 3 ^ P * F := by
    simpa [C, S, P] using h.invariant_zero
  have hCompRaw := ternaryValue_add_complementValue h.digit_lt_three
  have hLen := h.digits_length_eq
  have hComp : C + D + 1 = 3 ^ P := by
    dsimp [C, D, P]
    rw [hLen] at hCompRaw
    have hPowPos : 0 < 3 ^ rows.length :=
      pow_pos (by decide : 0 < (3 : ℕ)) rows.length
    omega
  have hF : F = 2 ^ H + (F - 2 ^ H) := by omega
  have hEq :
      2 ^ H * C + S =
        2 ^ H * C +
          (2 ^ H * (D + 1) + 3 ^ P * (F - 2 ^ H)) := by
    calc
      2 ^ H * C + S = 3 ^ P * F := hInv
      _ = 3 ^ P * (2 ^ H + (F - 2 ^ H)) := by
        exact congrArg (fun x : ℕ => 3 ^ P * x) hF
      _ = 3 ^ P * 2 ^ H + 3 ^ P * (F - 2 ^ H) := by
        ring
      _ = 2 ^ H * (C + D + 1) + 3 ^ P * (F - 2 ^ H) := by
        rw [hComp]
        ring
      _ = 2 ^ H * C +
          (2 ^ H * (D + 1) + 3 ^ P * (F - 2 ^ H)) := by
        ring
  have hCancel := Nat.add_left_cancel hEq
  simpa [S, D, P] using hCancel

/--
overhang が 4 以上なら weighted defect は
`2^H + 4*3^P` 以上に強制される。
-/
theorem finalDefect_lowerBound_of_four_le_overhang
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hFinalWrap : 2 ^ H ≤ F)
    (hOverhang : 4 ≤ F - 2 ^ H) :
    2 ^ H + 4 * 3 ^ rows.length ≤ ferrersWeightedDefect rows := by
  have hEq := h.finalDefect_eq_complement_add_overhang hFinalWrap
  have hOne : 1 ≤ ternaryComplementValue digits + 1 := by omega
  have hMPart :
      2 ^ H ≤ 2 ^ H * (ternaryComplementValue digits + 1) := by
    simp only [Order.lt_two_iff, zero_le, pow_pos, le_mul_iff_one_le_right, le_add_iff_nonneg_left]
  have hUPart :
      4 * 3 ^ rows.length ≤ 3 ^ rows.length * (F - 2 ^ H) := by
    have hMul := Nat.mul_le_mul_left (3 ^ rows.length) hOverhang
    simpa [Nat.mul_comm] using hMul
  rw [hEq]
  exact Nat.add_le_add hMPart hUPart

/--
critical rows では final wrap を仮定すると overhang は positive な 4 の倍数。
従って defect lower bound `2^H + 4*3^P` が自動で出る。
-/
theorem finalWrap_defect_lowerBound_of_criticalRows
    {P : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ criticalTwoDepth P) rows 0 digits F)
    (hRows : CriticalCarryRows P rows)
    (hP : 0 < P)
    (hFinalWrap : 2 ^ criticalTwoDepth P ≤ F) :
    2 ^ criticalTwoDepth P + 4 * 3 ^ P ≤ ferrersWeightedDefect rows := by
  have hStrict := h.final_wrap_strict_of_criticalRows hRows hFinalWrap
  have hOverPos : 0 < F - 2 ^ criticalTwoDepth P := by omega
  have hH : 2 ≤ criticalTwoDepth P := two_le_criticalTwoDepth_of_pos hP
  have hFour : 4 ∣ F - 2 ^ criticalTwoDepth P :=
    h.four_dvd_finalOverhang_of_criticalRows hRows hH
  have hFourLe : 4 ≤ F - 2 ^ criticalTwoDepth P :=
    Nat.le_of_dvd hOverPos hFour
  have hLower := h.finalDefect_lowerBound_of_four_le_overhang hFinalWrap hFourLe
  rw [hRows.length_eq] at hLower
  exact hLower

end CarryRealizes
end CSTCarry
end Collatz3
