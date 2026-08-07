import CollatzLean.CollatzFirstLayer.Affine
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.LinearCombination

/-!
# 共通指数語を走る二実現の差

同じ指数語を二つの自然数runが実現すると、affine定数は差で消える。
開始差と終了差の間のexact輸送式を得て、開始差が語の全2冪深さで
割り切れることを示す。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- 同じwordの二実現では開始順序が終了順序へ保存される。 -/
theorem realizes_common_word_finish_mono
    {w : ExpWord} {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : Realizes w x₁ y₁)
    (h₂ : Realizes w x₂ y₂)
    (hx : x₁ ≤ x₂) :
    y₁ ≤ y₂ := by
  unfold Realizes at h₁ h₂
  have hscaled :
      2 ^ twoSteps w * y₁ ≤
        2 ^ twoSteps w * y₂ := by
    calc
      2 ^ twoSteps w * y₁
          = 3 ^ oddSteps w * x₁ + affineConst w := h₁
      _ ≤ 3 ^ oddSteps w * x₂ + affineConst w :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left (3 ^ oddSteps w) hx)
          (affineConst w)
      _ = 2 ^ twoSteps w * y₂ := h₂.symm
  exact Nat.le_of_mul_le_mul_left hscaled
    (Nat.pow_pos (by omega : 0 < (2 : ℕ)))

/--
自然数の差を基点へ戻した積の恒等式。
-/
private theorem mul_sub_add_base_eq
    (a x y : ℕ)
    (hxy : x ≤ y) :
    a * (y - x) + a * x = a * y := by
  have hsub :
      y - x + x = y :=
    Nat.sub_add_cancel hxy
  calc
    a * (y - x) + a * x
        = a * ((y - x) + x) := by
            ring
    _ = a * y := by
            rw [hsub]


/--
affine式の入力差分を基点へ戻す恒等式。
-/
private theorem mul_sub_add_affine_eq
    (a b x₁ x₂ : ℕ)
    (hx : x₁ ≤ x₂) :
    a * (x₂ - x₁) + (a * x₁ + b) =
      a * x₂ + b := by
  have hsub :
      x₂ - x₁ + x₁ = x₂ :=
    Nat.sub_add_cancel hx
  calc
    a * (x₂ - x₁) + (a * x₁ + b)
        =
      a * ((x₂ - x₁) + x₁) + b := by
        ring
    _ = a * x₂ + b := by
        rw [hsub]

/--
同じ係数と定数項を持つ二つの自然数affine式に対する、
差のexact輸送式。
-/
private theorem common_affine_difference
    {A C B x₁ x₂ y₁ y₂ : ℕ}
    (h₁ :
      C * y₁ = A * x₁ + B)
    (h₂ :
      C * y₂ = A * x₂ + B)
    (hx : x₁ ≤ x₂)
    (hy : y₁ ≤ y₂) :
    C * (y₂ - y₁) =
      A * (x₂ - x₁) := by
  have hsum :
      C * (y₂ - y₁) + C * y₁ =
        A * (x₂ - x₁) + C * y₁ := by
    calc
      C * (y₂ - y₁) + C * y₁
          = C * y₂ := by
              exact mul_sub_add_base_eq C y₁ y₂ hy
      _ = A * x₂ + B := h₂
      _ =
          A * (x₂ - x₁) +
            (A * x₁ + B) := by
              exact
                (mul_sub_add_affine_eq
                  A B x₁ x₂ hx).symm
      _ =
          A * (x₂ - x₁) +
            C * y₁ := by
              rw [← h₁]
  exact Nat.add_right_cancel hsum


/--
同じwordの二実現に対する差のexact輸送式。
-/
theorem realizes_common_word_difference
    {w : ExpWord}
    {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : Realizes w x₁ y₁)
    (h₂ : Realizes w x₂ y₂)
    (hx : x₁ ≤ x₂) :
    2 ^ twoSteps w * (y₂ - y₁) =
      3 ^ oddSteps w * (x₂ - x₁) := by
  have hy :
      y₁ ≤ y₂ :=
    realizes_common_word_finish_mono h₁ h₂ hx
  unfold Realizes at h₁ h₂
  exact
    common_affine_difference
      h₁
      h₂
      hx
      hy

/--
同じwordを走る二自然数実現の開始差は、wordの全2冪深さで割り切れる。
-/
theorem twoPow_twoSteps_dvd_startDifference_of_common_word
    {w : ExpWord} {x₁ x₂ y₁ y₂ : ℕ}
    (h₁ : Realizes w x₁ y₁)
    (h₂ : Realizes w x₂ y₂)
    (hx : x₁ ≤ x₂) :
    2 ^ twoSteps w ∣ x₂ - x₁ := by
  have hDiff :=
    realizes_common_word_difference h₁ h₂ hx
  have hProduct :
      2 ^ twoSteps w ∣
        3 ^ oddSteps w * (x₂ - x₁) := by
    exact ⟨y₂ - y₁, hDiff.symm⟩
  have hBase :
      Nat.Coprime 2 3 := by
    decide
  have hCoprime :
      Nat.Coprime
        (2 ^ twoSteps w)
        (3 ^ oddSteps w) := by
    exact hBase.pow (twoSteps w) (oddSteps w)
  exact
    hCoprime.dvd_of_dvd_mul_left hProduct

/-- 整数上の共通affine式では定数項が差で消える。 -/
theorem signed_common_affine_difference
    {H L : ℕ} {C x₁ x₂ y₁ y₂ : ℤ}
    (h₁ : (2 : ℤ) ^ H * y₁ = (3 : ℤ) ^ L * x₁ + C)
    (h₂ : (2 : ℤ) ^ H * y₂ = (3 : ℤ) ^ L * x₂ + C) :
    (2 : ℤ) ^ H * (y₂ - y₁) =
      (3 : ℤ) ^ L * (x₂ - x₁) := by
  linear_combination h₂ - h₁

end ExpWord
end CollatzFirstLayer
