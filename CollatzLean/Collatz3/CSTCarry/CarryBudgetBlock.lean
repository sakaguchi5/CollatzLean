import CollatzLean.Collatz3.CSTCarry.CarryRealizesAppend
import Mathlib.Tactic.Linarith

/-!
# Collatz3 CSTCarry: block complement budget の exact carry characterization

前段の general initial-carry identity を、block proof で直接使う形へ特殊化する。

* initial carry `0` では strict budget と `F < M` が同値。
* initial carry `M` では weak budget と `F ≤ M` が同値。

これにより interior block と terminal block の目標を、最終 carry の大小だけへ変換できる。
-/

namespace Collatz3
namespace CSTCarry

namespace CarryRealizes

/-- terminal block 用: strict complement budget と strict final bound の exact 同値。 -/
theorem complementBudget_iff_final_lt_modulus
    {M : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes M rows 0 digits F) :
    ComplementBudget M rows digits ↔ F < M := by
  exact h.final_lt_modulus_iff_defect_lt_complementBudget.symm

/--
interior block 用の中心同値。

initial carry を modulus 自身 `M` に固定すると、

`WeakComplementBudget M rows digits ↔ F ≤ M`。
-/
theorem weakComplementBudget_iff_final_le_modulus
    {M : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes M rows M digits F) :
    WeakComplementBudget M rows digits ↔ F ≤ M := by
  unfold WeakComplementBudget
  have hBal := h.complement_balance_int_modulus
  have hPowPos :
      (0 : ℤ) < ((3 ^ rows.length : ℕ) : ℤ) := by
    positivity
  constructor
  · intro hBudget
    have hBudgetZ :
        (ferrersWeightedDefect rows : ℤ) ≤
          (M : ℤ) * (ternaryComplementValue digits : ℤ) := by
      exact_mod_cast hBudget
    have hLeftNonneg :
        0 ≤
          (M : ℤ) * (ternaryComplementValue digits : ℤ) -
            (ferrersWeightedDefect rows : ℤ) := by
      linarith
    rw [hBal] at hLeftNonneg
    have hDiffNonneg :
        0 ≤ (M : ℤ) - (F : ℤ) := by
      nlinarith
    have hFMZ : (F : ℤ) ≤ (M : ℤ) := by
      linarith
    exact_mod_cast hFMZ
  · intro hFM
    have hFMZ : (F : ℤ) ≤ (M : ℤ) := by
      exact_mod_cast hFM
    have hDiffNonneg :
        0 ≤ (M : ℤ) - (F : ℤ) := by
      linarith
    have hLeftNonneg :
        0 ≤
          (M : ℤ) * (ternaryComplementValue digits : ℤ) -
            (ferrersWeightedDefect rows : ℤ) := by
      rw [hBal]
      nlinarith
    have hBudgetZ :
        (ferrersWeightedDefect rows : ℤ) ≤
          (M : ℤ) * (ternaryComplementValue digits : ℤ) := by
      linarith
    exact_mod_cast hBudgetZ

end CarryRealizes

/-- strict budget は共通の正の scale を掛けても exact に保存される。 -/
theorem scaled_strictBudget_iff
    {scale M S D : ℕ}
    (hScale : 0 < scale) :
    scale * S < (scale * M) * (D + 1) ↔
      S < M * (D + 1) := by
  constructor
  · intro h
    have h' : scale * S < scale * (M * (D + 1)) := by
      simpa [mul_assoc] using h
    exact (Nat.mul_lt_mul_left hScale).1 h'
  · intro h
    have h' := (Nat.mul_lt_mul_left hScale).2 h
    simpa [mul_assoc] using h'

/-- weak budget も共通の正の scale を掛けても exact に保存される。 -/
theorem scaled_weakBudget_iff
    {scale M S D : ℕ}
    (hScale : 0 < scale) :
    scale * S ≤ (scale * M) * D ↔
      S ≤ M * D := by
  constructor
  · intro h
    have h' : scale * S ≤ scale * (M * D) := by
      simpa [mul_assoc] using h
    exact (Nat.le_of_mul_le_mul_left h') hScale
  · intro h
    have h' : scale * S ≤ scale * (M * D) :=
      Nat.mul_le_mul_left scale h
    simpa [mul_assoc] using h'

end CSTCarry
end Collatz3
