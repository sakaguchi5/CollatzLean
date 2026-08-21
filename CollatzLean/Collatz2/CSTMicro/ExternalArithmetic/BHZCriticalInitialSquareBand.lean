import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyLocalSquares
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPrefixOstrowski

/-!
# BHZ / Ostrowski initial-square band interface

Berthé--Holton--Zamboni の initial-power description を、
この project が実際に必要とする一つの pure Sturmian corollary に切り出す。

actual critical continued-fraction の odd-column denominator を `P_j` とする。
threshold `N` が consecutive band

  P_j <= N < P_(j+1)

にあるとき、任意 phase `s` から始まる critical Sturmian suffix は

  N <= r <= C_BHZ * P_(j+1)

を満たす square prefix root `r` を持つ、という statement だけを外部入力にする。

重要:
* ここには exponent 14 は入れない。
* Collatz / Pure B / state / y は一切入れない。
* degree 14 は別ファイルで Rhin denominator growth から Lean 内で導く。

BHZ の standard / semistandard initial powers と Ostrowski carry case analysis を
formalize するとき、この structure の inhabitant を構成すればよい。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
BHZ initial-power theory の project-facing corollary。

`bandConstant` は absolute constant であり、値の最適化は要求しない。
-/
structure BHZCriticalInitialSquareBand where
  bandConstant : ℕ
  bandConstant_pos : 0 < bandConstant
  exists_square_in_band :
    ∀ s N j : ℕ,
      2 ≤ j →
      criticalPowerP j ≤ N →
      N < criticalPowerP (j + 1) →
      ∃ r : ℕ,
        N ≤ r ∧
        r ≤ bandConstant * criticalPowerP (j + 1) ∧
        CriticalBeattySquareAt s r

namespace BHZCriticalInitialSquareBand

/-- band theorem が返す square root は自動的に positive。 -/
theorem exists_square_in_band_pos
    (B : BHZCriticalInitialSquareBand)
    (s N j : ℕ)
    (hj : 2 ≤ j)
    (hLower : criticalPowerP j ≤ N)
    (hUpper : N < criticalPowerP (j + 1))
    (hNPos : 0 < N) :
    ∃ r : ℕ,
      0 < r ∧
      N ≤ r ∧
      r ≤ B.bandConstant * criticalPowerP (j + 1) ∧
      CriticalBeattySquareAt s r := by
  rcases B.exists_square_in_band s N j hj hLower hUpper with
    ⟨r, hNr, hrUpper, hSquare⟩
  exact ⟨r, lt_of_lt_of_le hNPos hNr, hNr, hrUpper, hSquare⟩

end BHZCriticalInitialSquareBand

end ExternalArithmetic
end CSTMicro
end Collatz2
