import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalBeattyLocalSquares

/-!
# Degree-parameterized critical Sturmian square window

旧 interface は exponent 14 を型名に固定していた。
BHZ exact selector の quantitative cost を正直に追えるよう、exponent `D` を parameter 化する。

既存 `CriticalSturmianSquareWindow14` は変更しない。
この新 interface は quantitative source を検証するための parallel layer。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

structure CriticalSturmianSquareWindowD (D : ℕ) where
  constant : ℕ
  constant_pos : 0 < constant
  exists_square :
    ∀ s N : ℕ,
      2 ≤ N →
      ∃ r : ℕ,
        N ≤ r ∧
        r ≤ constant * (N + 1) ^ D ∧
        CriticalBeattySquareAt s r

namespace CriticalSturmianSquareWindowD

/-- returned root is automatically positive. -/
theorem exists_square_pos
    {D : ℕ}
    (W : CriticalSturmianSquareWindowD D)
    (s N : ℕ)
    (hN : 2 ≤ N) :
    ∃ r : ℕ,
      0 < r ∧
      N ≤ r ∧
      r ≤ W.constant * (N + 1) ^ D ∧
      CriticalBeattySquareAt s r := by
  rcases W.exists_square s N hN with ⟨r, hNr, hrC, hSq⟩
  exact ⟨r, by omega, hNr, hrC, hSq⟩

end CriticalSturmianSquareWindowD

abbrev CriticalSturmianSquareWindow2744 :=
  CriticalSturmianSquareWindowD 2744

end ExternalArithmetic
end CSTMicro
end Collatz2
