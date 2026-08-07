import CollatzLean.CollatzFirstLayer.CommonWordDifference
import CollatzLean.CollatzFirstLayer.CanonicalReplay

/-!
# 共通wordの整数実現と2進整除

既存の整数affine差分公式を`RealizesInt`へ包装する。
開始差・終了差が自然数offsetとして与えられる場合には、
2と3の互いに素性から開始offsetの全2進depth整除を得る。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- 同じwordの二つの整数実現に対する差のexact輸送式。 -/
theorem realizesInt_common_word_difference
    {w : ExpWord} {x₁ x₂ y₁ y₂ : ℤ}
    (h₁ : RealizesInt w x₁ y₁)
    (h₂ : RealizesInt w x₂ y₂) :
    (2 : ℤ) ^ twoSteps w * (y₂ - y₁) =
      (3 : ℤ) ^ oddSteps w * (x₂ - x₁) := by
  unfold RealizesInt at h₁ h₂
  exact signed_common_affine_difference h₁ h₂

/--
整数実現の開始差・終了差が自然数offsetとして与えられる場合、
開始offsetはwordの全2冪depthで割り切れる。
-/
theorem twoPow_twoSteps_dvd_nat_startOffset_of_common_signed_word
    {w : ExpWord} {x₁ x₂ y₁ y₂ : ℤ} {dx dy : ℕ}
    (h₁ : RealizesInt w x₁ y₁)
    (h₂ : RealizesInt w x₂ y₂)
    (hx : x₂ = x₁ + (dx : ℤ))
    (hy : y₂ = y₁ + (dy : ℤ)) :
    2 ^ twoSteps w ∣ dx := by
  have hDiff := realizesInt_common_word_difference h₁ h₂
  rw [hx, hy] at hDiff
  have hZ :
      (2 : ℤ) ^ twoSteps w * (dy : ℤ) =
        (3 : ℤ) ^ oddSteps w * (dx : ℤ) := by
    simpa using hDiff
  have hNat :
      2 ^ twoSteps w * dy =
        3 ^ oddSteps w * dx := by
    exact_mod_cast hZ
  have hProduct :
      2 ^ twoSteps w ∣ 3 ^ oddSteps w * dx :=
    ⟨dy, hNat.symm⟩
  have hCoprime :
      Nat.Coprime (2 ^ twoSteps w) (3 ^ oddSteps w) :=
    Nat.Coprime.pow
      (twoSteps w) (oddSteps w)
      (by decide : Nat.Coprime 2 3)
  exact Nat.Coprime.dvd_of_dvd_mul_left hCoprime hProduct

end ExpWord
end CollatzFirstLayer
