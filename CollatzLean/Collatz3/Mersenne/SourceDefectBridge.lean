import CollatzLean.Collatz3.Mersenne.Basic
import CollatzLean.Collatz3.Binary.BoundedDefect
import CollatzLean.Collatz3.Binary.TrailingOnes

import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: source defect から block coefficient defect への bridge

一般 `BlockData`

`x + 1 = 2^k * u`
`2^r * y + 1 = 3^k * u`

について、source `x` の binary zero defect を coefficient `u` へ移す。

中心は `x+1=2^k*u` から source word の先頭 `k` 個の `1` を剥がす pure binary lemma。
残り word が空なら `u=1`、空でなければ endpoint equation の parity により
その先頭は `0` でなければならず、それを `1` に置き換えると `u` の word になる。

bounded 版では defect は増えない。
さらに exact source defect が正なら、境界の `0` が一つ `1` に変わるため
coefficient defect は exact に一つ減る。
-/

namespace Collatz3
namespace Mersenne

/--
exact source defect から coefficient `u` の defect を構成し、その defect が source defect 以下と示す。
-/
theorem BlockData.exists_coefficient_zeroDefect_le
    {k r u x y defect length : ℕ}
    (hBlock : BlockData k r u x y)
    (hSource : Binary.HasZeroDefect x defect length) :
    ∃ coefficientDefect coefficientLength : ℕ,
      Binary.HasZeroDefect u coefficientDefect coefficientLength ∧
      coefficientDefect ≤ defect := by
  rcases hSource with ⟨bits, hRep, hZero⟩
  have hValueEq :
      Binary.valueLSB bits + 1 = 2 ^ k * u := by
    calc
      Binary.valueLSB bits + 1 = x + 1 := by rw [hRep.value]
      _ = 2 ^ k * u := hBlock.startEquation
  rcases Binary.exists_truePrefix_of_valueLSB_add_one_eq_twoPow_mul
      bits k u hValueEq with
    ⟨tail, hBits, hTailEq⟩
  have hZeroTail : Binary.zeroCount tail = defect := by
    rw [hBits, Binary.zeroCount_append,
      Binary.zeroCount_replicate_true, zero_add] at hZero
    exact hZero
  cases tail with
  | nil =>
      have hu : u = 1 := by
        simpa using hTailEq.symm
      subst u
      refine ⟨0, 1, ?_, by omega⟩
      refine ⟨[true], ?_, ?_⟩
      · constructor <;> simp [Binary.valueLSB]
      · simp [Binary.zeroCount]
  | cons b bs =>
      cases b with
      | false =>
          let coefficientBits : List Bool := true :: bs
          have hRepU :
              Binary.RepresentsAtLength
                coefficientBits u (bs.length + 1) := by
            constructor
            · simp [coefficientBits]
            · simp only [coefficientBits, Binary.valueLSB_cons,
                Binary.bitValue_true, Binary.bitValue_false] at hTailEq ⊢
              omega
          have hCountLe :
              Binary.zeroCount coefficientBits ≤ defect := by
            have hSourceCount :
                Binary.zeroCount (false :: bs) = defect := hZeroTail
            simp [coefficientBits, Binary.zeroCount] at hSourceCount ⊢
            omega
          refine ⟨Binary.zeroCount coefficientBits, bs.length + 1, ?_, hCountLe⟩
          exact ⟨coefficientBits, hRepU, rfl⟩
      | true =>
          exfalso
          have huEven :
              u = 2 * (Binary.valueLSB bs + 1) := by
            simp only [Binary.valueLSB_cons, Binary.bitValue_true] at hTailEq
            omega
          have hEnd := hBlock.endEquation
          rw [huEven] at hEnd
          obtain ⟨s, hrEq⟩ :=
            Nat.exists_eq_succ_of_ne_zero
              (Nat.ne_of_gt hBlock.exitDepth_pos)
          rw [hrEq] at hEnd
          have hParity :
              2 * (2 ^ s * y) + 1 =
                2 * (3 ^ k * (Binary.valueLSB bs + 1)) := by
            calc
              2 * (2 ^ s * y) + 1
                  = 2 ^ (s + 1) * y + 1 := by
                      rw [pow_succ]
                      ring
              _ = 3 ^ k * (2 * (Binary.valueLSB bs + 1)) := hEnd
              _ = 2 * (3 ^ k * (Binary.valueLSB bs + 1)) := by ring
          omega

/--
source defect が正なら、coefficient へ移る際に defect は exact に一つ減る。

source word の `k` 個の trailing `1` を剥がした直後の bit は必ず `0`。
coefficient word ではその bit が `1` に変わるので、zero-count が一つだけ減る。
-/
theorem BlockData.exists_coefficient_zeroDefect_eq_pred
    {k r u x y defect length : ℕ}
    (hBlock : BlockData k r u x y)
    (hSource : Binary.HasZeroDefect x defect length)
    (hDefectPos : 0 < defect) :
    ∃ coefficientLength : ℕ,
      Binary.HasZeroDefect u (defect - 1) coefficientLength := by
  rcases hSource with ⟨bits, hRep, hZero⟩
  have hValueEq :
      Binary.valueLSB bits + 1 = 2 ^ k * u := by
    calc
      Binary.valueLSB bits + 1 = x + 1 := by rw [hRep.value]
      _ = 2 ^ k * u := hBlock.startEquation
  rcases Binary.exists_truePrefix_of_valueLSB_add_one_eq_twoPow_mul
      bits k u hValueEq with
    ⟨tail, hBits, hTailEq⟩
  have hZeroTail : Binary.zeroCount tail = defect := by
    rw [hBits, Binary.zeroCount_append,
      Binary.zeroCount_replicate_true, zero_add] at hZero
    exact hZero
  cases tail with
  | nil =>
      simp at hZeroTail
      omega
  | cons b bs =>
      cases b with
      | false =>
          let coefficientBits : List Bool := true :: bs
          have hRepU :
              Binary.RepresentsAtLength
                coefficientBits u (bs.length + 1) := by
            constructor
            · simp [coefficientBits]
            · simp only [coefficientBits, Binary.valueLSB_cons,
                Binary.bitValue_true, Binary.bitValue_false] at hTailEq ⊢
              omega
          have hCountEq :
              Binary.zeroCount coefficientBits = defect - 1 := by
            have hSourceCount :
                Binary.zeroCount (false :: bs) = defect := hZeroTail
            simp [coefficientBits, Binary.zeroCount] at hSourceCount ⊢
            omega
          refine ⟨bs.length + 1, ?_⟩
          exact ⟨coefficientBits, hRepU, hCountEq⟩
      | true =>
          exfalso
          have huEven :
              u = 2 * (Binary.valueLSB bs + 1) := by
            simp only [Binary.valueLSB_cons, Binary.bitValue_true] at hTailEq
            omega
          have hEnd := hBlock.endEquation
          rw [huEven] at hEnd
          obtain ⟨s, hrEq⟩ :=
            Nat.exists_eq_succ_of_ne_zero
              (Nat.ne_of_gt hBlock.exitDepth_pos)
          rw [hrEq] at hEnd
          have hParity :
              2 * (2 ^ s * y) + 1 =
                2 * (3 ^ k * (Binary.valueLSB bs + 1)) := by
            calc
              2 * (2 ^ s * y) + 1
                  = 2 ^ (s + 1) * y + 1 := by
                      rw [pow_succ]
                      ring
              _ = 3 ^ k * (2 * (Binary.valueLSB bs + 1)) := hEnd
              _ = 2 * (3 ^ k * (Binary.valueLSB bs + 1)) := by ring
          omega

/--
source `x` の bounded zero defect は、そのまま block coefficient `u` の bounded defect へ移る。
-/
theorem BlockData.coefficient_hasZeroDefectAtMost
    {k r u x y bound : ℕ}
    (hBlock : BlockData k r u x y)
    (hSource : Binary.HasZeroDefectAtMost x bound) :
    Binary.HasZeroDefectAtMost u bound := by
  rcases hSource with ⟨defect, length, hExact, hLe⟩
  rcases hBlock.exists_coefficient_zeroDefect_le hExact with
    ⟨coefficientDefect, coefficientLength, hCoefficient, hCoefficientLe⟩
  exact ⟨
    coefficientDefect,
    coefficientLength,
    hCoefficient,
    le_trans hCoefficientLe hLe
  ⟩

end Mersenne
end Collatz3
