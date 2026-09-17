import CollatzLean.Collatz3.Binary.Defect
import CollatzLean.Collatz3.Arithmetic.Pow23

import Mathlib.Tactic.Ring

/-!
# Collatz3 Binary: trailing-one prefix の算術的剥離

`value(bits) + 1 = 2^k * u` という exact equation だけから、
LSB-first word `bits` の先頭 `k` bit がすべて `1` であることを導く。

Collatz / Mersenne の意味論はここへ入れない。
後段では `BlockData.startEquation` から coefficient `u` の binary word を復元するために使う。
-/

namespace Collatz3
namespace Binary

/--
`valueLSB bits + 1 = 2^k * u` なら、`bits` は `k` 個の trailing `1` を持ち、
それを剥がした残り `tail` は `valueLSB tail + 1 = u` を満たす。
-/
theorem exists_truePrefix_of_valueLSB_add_one_eq_twoPow_mul
    (bits : List Bool)
    (k u : ℕ)
    (hEq : valueLSB bits + 1 = 2 ^ k * u) :
    ∃ tail : List Bool,
      bits = List.replicate k true ++ tail ∧
      valueLSB tail + 1 = u := by
  induction k generalizing bits with
  | zero =>
      refine ⟨bits, ?_, ?_⟩
      · simp
      · simpa using hEq
  | succ k ih =>
      have hEvenRhs :
          2 ^ (k + 1) * u = 2 * (2 ^ k * u) := by
        rw [pow_succ]
        ring
      cases bits with
      | nil =>
          simp only [valueLSB_nil, zero_add] at hEq
          rw [hEvenRhs] at hEq
          omega
      | cons b bs =>
          cases b with
          | false =>
              simp only [valueLSB_cons, bitValue_false, zero_add] at hEq
              rw [hEvenRhs] at hEq
              omega
          | true =>
              simp only [valueLSB_cons, bitValue_true] at hEq
              rw [hEvenRhs] at hEq
              have hTailEq :
                  valueLSB bs + 1 = 2 ^ k * u := by
                omega
              rcases ih bs hTailEq with ⟨tail, hBits, hValue⟩
              refine ⟨tail, ?_, hValue⟩
              simp [List.replicate_succ, hBits]

end Binary
end Collatz3
