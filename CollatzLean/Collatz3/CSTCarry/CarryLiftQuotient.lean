import CollatzLean.Collatz3.CSTCarry.CarryBudget
import CollatzLean.Collatz3.CSTCarry.CarryResidueBridge
import CollatzLean.Collatz3.CSTCarry.WrapExceptions
import Mathlib.Tactic.IntervalCases

/-!
# Collatz3 CSTCarry: final carry の residue + quotient lift

binary residue だけでは `F` と `F + 2^H` を区別できない。
従って final boundedness を residue の「一周する/しない」だけで置き換えることはできない。

このファイルでは final carry を Euclidean decomposition

  F = U + 2^H * q

へ exact に分ける。

* `U = ferrersBinaryShift H rows` は既に証明済みの canonical residue。
* `q = F / 2^H` を carry lift quotient とする。

`RowsInsideBitWidth` の safe-state invariant を使うと `q` は `0` または `1` に限られる。
従って任意幅 final-wrap 問題は最終的に Boolean な `q = 0` の証明へ縮約される。
-/

namespace Collatz3
namespace CSTCarry

/-- H-bit modulus に対する carry の quotient lift。 -/
def carryLiftQuotient
    (H F : ℕ) : ℕ :=
  F / 2 ^ H

/-- quotient が 0 であることと modulus 未満であることは exact に同値。 -/
theorem carryLiftQuotient_eq_zero_iff_lt_modulus
    (H F : ℕ) :
    carryLiftQuotient H F = 0 ↔ F < 2 ^ H := by
  unfold carryLiftQuotient
  constructor
  · intro hZero
    by_contra hNot
    have hGe : 2 ^ H ≤ F := by omega
    have hM : 0 < 2 ^ H := pow_pos (by decide : 0 < (2 : ℕ)) H
    have hOne : 1 ≤ F / 2 ^ H := by
      apply (Nat.le_div_iff_mul_le hM).2
      simpa using hGe
    omega
  · intro hLt
    exact Nat.div_eq_of_lt hLt

namespace CarryRealizes

/--
## exact lifted decomposition

final carry は canonical binary shift と modulus quotient の和に exact に分解される。
-/
theorem final_eq_ferrersBinaryShift_add_modulus_mul_liftQuotient
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F) :
    F = ferrersBinaryShift H rows +
      2 ^ H * carryLiftQuotient H F := by
  have hDecomp := Nat.mod_add_div F (2 ^ H)
  have hMod := h.final_mod_eq_ferrersBinaryShift
  unfold carryLiftQuotient
  rw [hMod] at hDecomp
  exact hDecomp.symm

/-- final boundedness は lift quotient `0` と exact に同値。 -/
theorem final_lt_modulus_iff_liftQuotient_eq_zero
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (_h : CarryRealizes (2 ^ H) rows 0 digits F) :
    F < 2 ^ H ↔ carryLiftQuotient H F = 0 := by
  exact (carryLiftQuotient_eq_zero_iff_lt_modulus H F).symm

/-- complement budget も lift quotient `0` と exact に同値。 -/
theorem liftQuotient_eq_zero_iff_complementBudget
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F) :
    carryLiftQuotient H F = 0 ↔
      ComplementBudget (2 ^ H) rows digits := by
  rw [carryLiftQuotient_eq_zero_iff_lt_modulus]
  exact h.final_lt_modulus_iff_defect_lt_complementBudget

/--
inside-bit-width の safe-state から final carry は `2 * 2^H` 未満。
これは quotient が二値になるための integer bound。
-/
theorem final_lt_two_mul_modulus_of_insideBitWidth
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hRows : RowsInsideBitWidth H rows) :
    F < 2 * 2 ^ H := by
  have hSafe := h.final_below_or_small_wrap_of_insideBitWidth hRows
  rcases hSafe with hBelow | hWrapped
  · omega
  · have hOver : 4 * (F - 2 ^ H) < 2 ^ H := hWrapped.2
    have hDecomp : F = 2 ^ H + (F - 2 ^ H) := by omega
    have hOverLt : F - 2 ^ H < 2 ^ H := by omega
    omega

/-- inside-bit-width では lift quotient は `0` または `1`。 -/
theorem liftQuotient_eq_zero_or_one_of_insideBitWidth
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hRows : RowsInsideBitWidth H rows) :
    carryLiftQuotient H F = 0 ∨ carryLiftQuotient H F = 1 := by
  have hM : 0 < 2 ^ H := pow_pos (by decide : 0 < (2 : ℕ)) H
  have hFlt := h.final_lt_two_mul_modulus_of_insideBitWidth hRows
  have hQlt : F / 2 ^ H < 2 := by
    exact (Nat.div_lt_iff_lt_mul hM).2 (by simpa [Nat.mul_comm] using hFlt)
  unfold carryLiftQuotient
  have hQle : F / 2 ^ H ≤ 1 := by
    omega
  interval_cases hQ : F / 2 ^ H <;> simp

/-- inside-bit-width では final wrap と lift quotient `1` が exact に同値。 -/
theorem final_wrap_iff_liftQuotient_eq_one_of_insideBitWidth
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hRows : RowsInsideBitWidth H rows) :
    2 ^ H ≤ F ↔ carryLiftQuotient H F = 1 := by
  have hCases := h.liftQuotient_eq_zero_or_one_of_insideBitWidth hRows
  constructor
  · intro hWrap
    rcases hCases with hZero | hOne
    · have hLt := (carryLiftQuotient_eq_zero_iff_lt_modulus H F).1 hZero
      omega
    · exact hOne
  · intro hOne
    by_contra hNot
    have hLt : F < 2 ^ H := by omega
    have hZero := (carryLiftQuotient_eq_zero_iff_lt_modulus H F).2 hLt
    omega

/--
final wrap branch では lifted decomposition は exactly `F = U + 2^H`。
ここで `U` は canonical Ferrers binary shift。
-/
theorem final_eq_modulus_add_ferrersBinaryShift_of_wrap
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F)
    (hRows : RowsInsideBitWidth H rows)
    (hWrap : 2 ^ H ≤ F) :
    F = 2 ^ H + ferrersBinaryShift H rows := by
  have hQ : carryLiftQuotient H F = 1 :=
    (h.final_wrap_iff_liftQuotient_eq_one_of_insideBitWidth hRows).1 hWrap
  have hEq := h.final_eq_ferrersBinaryShift_add_modulus_mul_liftQuotient
  rw [hQ] at hEq
  simpa [Nat.add_comm] using hEq

end CarryRealizes
end CSTCarry
end Collatz3
