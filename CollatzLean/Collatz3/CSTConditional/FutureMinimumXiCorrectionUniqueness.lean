import CollatzLean.Collatz3.CSTConditional.FutureMinimumCompletionBranchSelector
import CollatzLean.Collatz3.CSTConditional.ACSturmianRefinement
import Mathlib.Tactic.Linarith

/-!
# Collatz3 CSTConditional: A transition の dyadic correction 一意性

既存 dyadic state

`xi = (upsilon + 3 sigma)/4`

は exponent `1` の一歩で

`xi_(m+1) = (xi_m + g + 2h) / 2^(1+s_m)`

という exact skew-product を持つ。

Global CST の `A` transition では future minimum の開始 exponent が `1`、
さらに開始 Sturmian step は `1` なので、

`xi_(i+1) = (xi_i + d_i)/4`

という形になる。ここで `d_i = g+2h` だが、`g,h` を新しい primitive data として
保存せず、**この等式を満たす整数 `d_i` が存在一意**であることだけを derived theorem にする。

これにより A の最初の dyadic step は「任意の整数 correction を選べる」形ではなく、
current/next canonical completion が固定されれば一つの整数 correction に決まる。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
Global CST の `A` next-future-minimum transition では、開始一歩の dyadic correction

`xi_(i+1) = (xi_i + d)/4`

を満たす整数 `d` が存在一意。

新しい correction 関数は定義しない。
-/
theorem exists_unique_symbol_A_dyadicStateCorrection_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i j t u : ℕ}
    (hi : 0 < i)
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hA : O.transitionSymbol i j = .A)
    (hStartI :
      O.endpointCompletionStart SInf hi =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent i * t)
    (hStartSucc :
      O.endpointCompletionStart SInf (by omega : 0 < i + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (i + 1) * u) :
    ∃! d : ℤ,
      O.normalizedCompletionDyadicState (i + 1) u =
        (O.normalizedCompletionDyadicState i t + (d : ℝ)) / 4 := by
  have he : O.exponent i = 1 :=
    O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor
      SInf hStart
  have hs : survivorSturmianStep i = 1 :=
    O.nextFutureMinimum_symbol_A_sturmianStep_eq_one_of_globalCST
      G SInf hStart hNext hA
  rcases
      O.exists_normalizedCompletionDyadicState_transition_digits_of_exponent_eq_one
        SInf hi he hStartI hStartSucc with ⟨g, h, hXi⟩
  have hExist :
      O.normalizedCompletionDyadicState (i + 1) u =
        (O.normalizedCompletionDyadicState i t + ((g + 2 * h : ℤ) : ℝ)) / 4 := by
    rw [hs] at hXi
    norm_num at hXi
    push_cast at hXi ⊢
    simpa [add_assoc] using hXi
  refine ⟨g + 2 * h, hExist, ?_⟩
  intro d hd
  have hEqR :
      (d : ℝ) = ((g + 2 * h : ℤ) : ℝ) := by
    nlinarith [hd, hExist]
  exact_mod_cast hEqR

/--
A transition の dyadic correction の一意性を equality elimination 用にした形。

同じ current/next dyadic state に対して二つの整数 correction が書けたなら一致する。
-/
theorem symbol_A_dyadicStateCorrection_unique
    (O : Collatz3.OddOrbit)
    {i t u : ℕ}
    (d₁ d₂ : ℤ)
    (h₁ :
      O.normalizedCompletionDyadicState (i + 1) u =
        (O.normalizedCompletionDyadicState i t + (d₁ : ℝ)) / 4)
    (h₂ :
      O.normalizedCompletionDyadicState (i + 1) u =
        (O.normalizedCompletionDyadicState i t + (d₂ : ℝ)) / 4) :
    d₁ = d₂ := by
  have hEqR : (d₁ : ℝ) = (d₂ : ℝ) := by
    nlinarith [h₁, h₂]
  exact_mod_cast hEqR

end OddOrbit
end Collatz3
