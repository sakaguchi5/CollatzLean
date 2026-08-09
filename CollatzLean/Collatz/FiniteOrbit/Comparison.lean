import CollatzLean.Collatz.FiniteOrbit.Runs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.LinearCombination

/-!
# 共通wordを走る二実現の比較
-/

namespace Collatz
namespace Word

/-- 同じwordの二実現では開始順序が終了順序へ保存される。 -/
theorem Realizes.finish_mono
    {w : Collatz.Word} {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : w.Realizes x₁ y₁)
    (h₂ : w.Realizes x₂ y₂)
    (hx : x₁ ≤ x₂) :
    y₁ ≤ y₂ := by
  unfold Realizes at h₁ h₂
  have hscaled : 2 ^ w.twoSteps * y₁ ≤ 2 ^ w.twoSteps * y₂ := by
    calc
      2 ^ w.twoSteps * y₁ = 3 ^ w.oddSteps * x₁ + w.affineConst := h₁
      _ ≤ 3 ^ w.oddSteps * x₂ + w.affineConst :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hx) _
      _ = 2 ^ w.twoSteps * y₂ := h₂.symm
  exact Nat.le_of_mul_le_mul_left hscaled (Nat.pow_pos (by omega : 0 < (2 : ℕ)))


/-- 同じwordの二実現に対するexact差分輸送。 -/
theorem Realizes.difference
    {w : Collatz.Word} {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : w.Realizes x₁ y₁)
    (h₂ : w.Realizes x₂ y₂)
    (hx : x₁ ≤ x₂) :
    2 ^ w.twoSteps * (y₂ - y₁) =
      3 ^ w.oddSteps * (x₂ - x₁) := by
  have hy := h₁.finish_mono h₂ hx
  unfold Realizes at h₁ h₂
  have hsubx : x₂ - x₁ + x₁ = x₂ :=
    Nat.sub_add_cancel hx
  have hsuby : y₂ - y₁ + y₁ = y₂ :=
    Nat.sub_add_cancel hy
  have hsum :
      2 ^ w.twoSteps * (y₂ - y₁) + 2 ^ w.twoSteps * y₁ =
        3 ^ w.oddSteps * (x₂ - x₁) + 2 ^ w.twoSteps * y₁ := by
    calc
      2 ^ w.twoSteps * (y₂ - y₁) + 2 ^ w.twoSteps * y₁
          = 2 ^ w.twoSteps * y₂ := by
              rw [← Nat.mul_add, hsuby]
      _ = 3 ^ w.oddSteps * x₂ + w.affineConst := h₂
      _ = 3 ^ w.oddSteps * (x₂ - x₁) +
            (3 ^ w.oddSteps * x₁ + w.affineConst) := by
              conv_lhs =>
                rw [← hsubx]
              rw [Nat.mul_add, Nat.add_assoc]
      _ = 3 ^ w.oddSteps * (x₂ - x₁) +
            2 ^ w.twoSteps * y₁ := by
              rw [← h₁]
  exact Nat.add_right_cancel hsum

/-- 共通wordの開始差は`2^H`で割り切れる。 -/
theorem Realizes.twoPow_dvd_startDifference
    {w : Collatz.Word} {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : w.Realizes x₁ y₁)
    (h₂ : w.Realizes x₂ y₂)
    (hx : x₁ ≤ x₂) :
    2 ^ w.twoSteps ∣ x₂ - x₁ := by
  have hDiff := h₁.difference h₂ hx
  have hProduct : 2 ^ w.twoSteps ∣ 3 ^ w.oddSteps * (x₂ - x₁) :=
    ⟨y₂ - y₁, hDiff.symm⟩
  have hCoprime : Nat.Coprime (2 ^ w.twoSteps) (3 ^ w.oddSteps) :=
    (by decide : Nat.Coprime 2 3).pow w.twoSteps w.oddSteps
  exact hCoprime.dvd_of_dvd_mul_left hProduct

/-- 整数上の共通word差分。 -/
theorem RealizesInt.difference
    {w : Collatz.Word} {x₁ x₂ y₁ y₂ : ℤ}
    (h₁ : w.RealizesInt x₁ y₁)
    (h₂ : w.RealizesInt x₂ y₂) :
    (2 : ℤ) ^ w.twoSteps * (y₂ - y₁) =
      (3 : ℤ) ^ w.oddSteps * (x₂ - x₁) := by
  unfold RealizesInt at h₁ h₂
  linear_combination h₂ - h₁

end Word
end Collatz
