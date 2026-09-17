import CollatzLean.Collatz3.Mersenne.OneZeroRegions
import CollatzLean.Collatz3.Binary.SparseComplement
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: one-zero exit の sparse-complement equation

bounded target defect を、Mersenne macro equation と直接合成する。

`missingBits` は target の zero positions を 1 にした sparse word で、

`y + value(missingBits) + 1 = 2^L`

を満たす。これを

`2^r*y + 1 = 3^k*(2^n-1)`

と合わせると、外部 S-unit / Baker 型議論へ渡しやすい減算なしの exact equation が得られる。
-/

namespace Collatz3
namespace Mersenne

namespace OneZeroExit

/--
bounded target defect から sparse complement を伴う exact Diophantine equation を得る。
-/
theorem exists_sparseComplementEquation
    {k n y B : ℕ}
    (hExit : OneZeroExit k n y)
    (hDefect : Binary.HasZeroDefectAtMost y B) :
    ∃ r length : ℕ,
      ∃ missingBits : List Bool,
        0 < r ∧
          Odd y ∧
          missingBits.length = length ∧
          Binary.oneCount missingBits ≤ B ∧
          3 ^ k * (2 ^ n - 1) +
              2 ^ r * Binary.valueLSB missingBits + 2 ^ r =
            2 ^ (length + r) + 1 := by
  rcases hExit.exists_exitDepth_equation with
    ⟨r, hr, hy, hMacro⟩
  rcases hDefect.exists_sparseComplement with
    ⟨length, missingBits, hLen, hCount, hComplement⟩
  have hScaled :
      2 ^ r * y +
          2 ^ r * Binary.valueLSB missingBits + 2 ^ r =
        2 ^ (length + r) := by
    calc
      2 ^ r * y +
            2 ^ r * Binary.valueLSB missingBits + 2 ^ r
          = 2 ^ r *
              (y + Binary.valueLSB missingBits + 1) := by ring
      _ = 2 ^ r * 2 ^ length := by rw [hComplement]
      _ = 2 ^ (r + length) := by rw [pow_add]
      _ = 2 ^ (length + r) := by rw [Nat.add_comm]
  refine ⟨r, length, missingBits, hr, hy, hLen, hCount, ?_⟩
  calc
    3 ^ k * (2 ^ n - 1) +
          2 ^ r * Binary.valueLSB missingBits + 2 ^ r
        = (2 ^ r * y + 1) +
            2 ^ r * Binary.valueLSB missingBits + 2 ^ r := by
              rw [← hMacro]
    _ =
        (2 ^ r * y +
            2 ^ r * Binary.valueLSB missingBits + 2 ^ r) + 1 := by
          ring
    _ = 2 ^ (length + r) + 1 := by rw [hScaled]

end OneZeroExit

end Mersenne
end Collatz3
