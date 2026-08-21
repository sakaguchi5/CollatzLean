import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyLocalSquares

/-!
# Quantitative initial-square interface for the critical Sturmian shift

ここは pure B / Collatz とは独立な Sturmian combinatorics の唯一の quantitative port。

既知の initial-power / Ostrowski theory と、critical slope の denominator growth
`q_(j+1) <= 2 q_j^14` を組み合わせて最終的に discharge することを想定する。

このファイルでは、任意 phase `s` と threshold `N>=2` に対して

  N <= r <= C (N+1)^14

の square prefix root `r` が存在する、という exact interface だけを宣言する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
critical Sturmian shift の phase-uniform initial square window, degree 14。

`constant` は absolute constant。後段では値の最適化を要求しない。
-/
structure CriticalSturmianSquareWindow14 where
  constant : ℕ
  constant_pos : 0 < constant
  exists_square :
    ∀ s N : ℕ,
      2 ≤ N →
      ∃ r : ℕ,
        N ≤ r ∧
        r ≤ constant * (N + 1) ^ 14 ∧
        CriticalBeattySquareAt s r

namespace CriticalSturmianSquareWindow14

/-- interface が返す root は自動的に positive。 -/
theorem exists_square_pos
    (W : CriticalSturmianSquareWindow14)
    (s N : ℕ)
    (hN : 2 ≤ N) :
    ∃ r : ℕ,
      0 < r ∧
      N ≤ r ∧
      r ≤ W.constant * (N + 1) ^ 14 ∧
      CriticalBeattySquareAt s r := by
  rcases W.exists_square s N hN with ⟨r, hNr, hrC, hSq⟩
  exact ⟨r, by omega, hNr, hrC, hSq⟩

end CriticalSturmianSquareWindow14

end ExternalArithmetic
end CSTMicro
end Collatz2
