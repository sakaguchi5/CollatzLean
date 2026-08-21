import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyOneShortSquares

/-!
# degree parameter 付き one-short square window

完全 square 用の `CriticalSturmianSquareWindowD` と分離して、
一文字だけ短い periodic prefix 用の quantitative interface を置く。

後段の Pure B rigidity はこの弱い interface で十分であり、
BHZ selector の denominator level gap を一段縮められる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

structure CriticalSturmianOneShortSquareWindowD (D : ℕ) where
  constant : ℕ
  constant_pos : 0 < constant
  exists_oneShort :
    ∀ s N : ℕ,
      2 ≤ N →
      ∃ r : ℕ,
        N ≤ r ∧
        r ≤ constant * (N + 1) ^ D ∧
        CriticalBeattyOneShortSquareAt s r

namespace CriticalSturmianOneShortSquareWindowD

/-- window が返す root は自動的に正。 -/
theorem exists_oneShort_pos
    {D : ℕ}
    (W : CriticalSturmianOneShortSquareWindowD D)
    (s N : ℕ)
    (hN : 2 ≤ N) :
    ∃ r : ℕ,
      0 < r ∧
      N ≤ r ∧
      r ≤ W.constant * (N + 1) ^ D ∧
      CriticalBeattyOneShortSquareAt s r := by
  rcases W.exists_oneShort s N hN with ⟨r, hNr, hrC, hSq⟩
  exact ⟨r, by omega, hNr, hrC, hSq⟩

end CriticalSturmianOneShortSquareWindowD

abbrev CriticalSturmianOneShortSquareWindow196 :=
  CriticalSturmianOneShortSquareWindowD 196

end ExternalArithmetic
end CSTMicro
end Collatz2
