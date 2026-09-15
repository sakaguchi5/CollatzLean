import CollatzLean.Collatz3.Bridge.SurvivorActualCompletionHensel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: finite actual compatibility による completion grid separation

前段で得た finite exact compatibility

`theta + (3^m/4) upsilon ∈ Z`

だけを見る。

同じ actual residue fraction `theta` に対して二つの centered lift 候補が

* `2` 離れる場合、compatibility の差は `3^m/2`、
* `1` 離れる場合、compatibility の差は `3^m/4`

になる。しかし `3^m` は奇数なので、いずれも整数にはならない。

従って step-0 側の spacing `2`、step-1 側の spacing `1` の隣接 branch は、
同じ actual residue と同時には両立できない。

これは branch が実現することを主張する theorem ではない。
複数の algebraic candidate が finite actual compatibility を同時に満たすことを禁止するだけである。
-/

namespace Collatz3
namespace Bridge

/--
同じ `theta` に対する spacing `2` の二つの centered lift compatibility は両立しない。
-/
theorem not_both_centeredLiftCompatible_of_eq_add_two
    (m : ℕ)
    (theta upsilon₁ upsilon₂ : ℝ)
    (z₁ z₂ : ℤ)
    (h₁ :
      theta + ((3 : ℝ) ^ m / 4) * upsilon₁ = (z₁ : ℝ))
    (h₂ :
      theta + ((3 : ℝ) ^ m / 4) * upsilon₂ = (z₂ : ℝ))
    (hSpacing : upsilon₁ = upsilon₂ + 2) :
    False := by
  have hEvenR :
      (3 : ℝ) ^ m = 2 * ((z₁ - z₂ : ℤ) : ℝ) := by
    push_cast
    rw [hSpacing] at h₁
    nlinarith [h₁, h₂]
  rcases threePow_odd_nat m with ⟨q, hq⟩
  have hOddR : (3 : ℝ) ^ m = 2 * (q : ℝ) + 1 := by
    exact_mod_cast hq
  have hBadR :
      2 * (q : ℝ) + 1 = 2 * ((z₁ - z₂ : ℤ) : ℝ) := by
    linarith
  have hBadZ :
      2 * (q : ℤ) + 1 = 2 * (z₁ - z₂) := by
    exact_mod_cast hBadR
  omega

/-- spacing `2` の反対向きも同様に不可能。 -/
theorem not_both_centeredLiftCompatible_of_eq_sub_two
    (m : ℕ)
    (theta upsilon₁ upsilon₂ : ℝ)
    (z₁ z₂ : ℤ)
    (h₁ :
      theta + ((3 : ℝ) ^ m / 4) * upsilon₁ = (z₁ : ℝ))
    (h₂ :
      theta + ((3 : ℝ) ^ m / 4) * upsilon₂ = (z₂ : ℝ))
    (hSpacing : upsilon₁ = upsilon₂ - 2) :
    False := by
  have hRev : upsilon₂ = upsilon₁ + 2 := by linarith
  exact
    not_both_centeredLiftCompatible_of_eq_add_two
      m theta upsilon₂ upsilon₁ z₂ z₁ h₂ h₁ hRev

/--
同じ `theta` に対する spacing `1` の二つの centered lift compatibility は両立しない。
-/
theorem not_both_centeredLiftCompatible_of_eq_add_one
    (m : ℕ)
    (theta upsilon₁ upsilon₂ : ℝ)
    (z₁ z₂ : ℤ)
    (h₁ :
      theta + ((3 : ℝ) ^ m / 4) * upsilon₁ = (z₁ : ℝ))
    (h₂ :
      theta + ((3 : ℝ) ^ m / 4) * upsilon₂ = (z₂ : ℝ))
    (hSpacing : upsilon₁ = upsilon₂ + 1) :
    False := by
  have hFourR :
      (3 : ℝ) ^ m = 4 * ((z₁ - z₂ : ℤ) : ℝ) := by
    push_cast
    rw [hSpacing] at h₁
    nlinarith [h₁, h₂]
  rcases threePow_odd_nat m with ⟨q, hq⟩
  have hOddR : (3 : ℝ) ^ m = 2 * (q : ℝ) + 1 := by
    exact_mod_cast hq
  have hBadR :
      2 * (q : ℝ) + 1 = 4 * ((z₁ - z₂ : ℤ) : ℝ) := by
    linarith
  have hBadZ :
      2 * (q : ℤ) + 1 = 4 * (z₁ - z₂) := by
    exact_mod_cast hBadR
  omega

/-- spacing `1` の反対向きも同様に不可能。 -/
theorem not_both_centeredLiftCompatible_of_eq_sub_one
    (m : ℕ)
    (theta upsilon₁ upsilon₂ : ℝ)
    (z₁ z₂ : ℤ)
    (h₁ :
      theta + ((3 : ℝ) ^ m / 4) * upsilon₁ = (z₁ : ℝ))
    (h₂ :
      theta + ((3 : ℝ) ^ m / 4) * upsilon₂ = (z₂ : ℝ))
    (hSpacing : upsilon₁ = upsilon₂ - 1) :
    False := by
  have hRev : upsilon₂ = upsilon₁ + 1 := by linarith
  exact
    not_both_centeredLiftCompatible_of_eq_add_one
      m theta upsilon₂ upsilon₁ z₂ z₁ h₂ h₁ hRev

end Bridge
end Collatz3
