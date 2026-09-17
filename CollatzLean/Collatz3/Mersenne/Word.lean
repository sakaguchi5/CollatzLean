import CollatzLean.Collatz3.Core.Word

import Mathlib.Tactic.NormNum

/-!
# Collatz3 Mersenne: exponent word of one Mersenne block

Mersenne block の actual exponent word を薄く定義する。

block depth `d` のうち最初の `d-1` steps は exponent `1`、
最後だけ exponent `r+1` である。
actual realization は Bridge 層で証明する。
-/

namespace Collatz3
namespace Mersenne

/-- Mersenne block の exponent word `[1,...,1,r+1]`。 -/
def blockWord (d r : ℕ) : Word :=
  List.replicate (d - 1) 1 ++ [r + 1]

/-- 正の block depth では odd step 数は `d`。 -/
theorem blockWord_oddSteps
    {d r : ℕ}
    (hd : 0 < d) :
    Word.oddSteps (blockWord d r) = d := by
  simp [blockWord, Word.oddSteps]
  omega

/-- 正の block depth では total 2-depth は `d+r`。 -/
theorem blockWord_twoSteps
    {d r : ℕ}
    (hd : 0 < d) :
    Word.twoSteps (blockWord d r) = d + r := by
  simp [blockWord, Word.twoSteps]
  omega

/-- `r>0` なら block word は valid。 -/
theorem blockWord_valid
    {d r : ℕ}
    (hr : 0 < r) :
    Word.Valid (blockWord d r) := by
  intro e he
  simp [blockWord] at he
  omega

end Mersenne
end Collatz3
