import CollatzLean.Collatz3.CSTCarry.CarryBudgetAppend
import Mathlib.Tactic.LinearCombination


/-!
# Collatz3 CSTCarry: general initial carry の complement balance

初期 carry `E` を 0 に固定せず、一般の realization

`E + M*C + S = 3^P*F`

を complement value `D` で書き直す。

valid digits では

`C + D + 1 = 3^P`

なので、自然数上の subtraction-free な正本は

`3^P*F + M(D+1) = E + M*3^P + S`。

整数へ移せば会話中の差分形

`M(D+1) - S = 3^P(M-F) + E`

を exact に得る。
-/

namespace Collatz3
namespace CSTCarry

namespace CarryRealizes

/--
general initial carry の subtraction-free complement balance。

`Nat` 上ではこの加法等式を正本とする。
-/
theorem complement_balance_nat
    {M : ℕ}
    {rows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows E digits F) :
    3 ^ rows.length * F +
        M * (ternaryComplementValue digits + 1) =
      E + M * 3 ^ rows.length + ferrersWeightedDefect rows := by
  have hInv := h.invariant
  have hCompRaw := ternaryValue_add_complementValue h.digit_lt_three
  have hLen := h.digits_length_eq
  have hComp :
      ternaryDigitsValue digits +
          ternaryComplementValue digits + 1 =
        3 ^ rows.length := by
    rw [hLen] at hCompRaw
    have hPowPos : 0 < 3 ^ rows.length :=
      pow_pos (by decide : 0 < (3 : ℕ)) rows.length
    omega
  calc
    3 ^ rows.length * F +
          M * (ternaryComplementValue digits + 1)
        = (E + M * ternaryDigitsValue digits +
            ferrersWeightedDefect rows) +
            M * (ternaryComplementValue digits + 1) := by
              rw [← hInv]
    _ = E +
          M * (ternaryDigitsValue digits +
            ternaryComplementValue digits + 1) +
          ferrersWeightedDefect rows := by
            ring
    _ = E + M * 3 ^ rows.length + ferrersWeightedDefect rows := by
          rw [hComp]

/--
一般 initial carry 版の整数差分 identity。

`M(D+1) - S = 3^P(M-F) + E`。

`Nat` subtraction の切り捨てを避けるため `ℤ` で述べる。
-/
theorem complement_balance_int
    {M : ℕ}
    {rows : List FerrersRow}
    {E F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows E digits F) :
    (M : ℤ) * ((ternaryComplementValue digits : ℤ) + 1) -
        (ferrersWeightedDefect rows : ℤ) =
      ((3 ^ rows.length : ℕ) : ℤ) * ((M : ℤ) - (F : ℤ)) +
        (E : ℤ) := by
  have hNat := h.complement_balance_nat
  have hInt := congrArg (fun n : ℕ => (n : ℤ)) hNat
  push_cast at hInt
  have hPow :
      (((3 ^ rows.length : ℕ) : ℤ)) =
        (3 : ℤ) ^ rows.length := by
    norm_num
  rw [hPow]
  linear_combination hInt


/--
初期 carry `0` 版。

`M(D+1) - S = 3^P(M-F)`。
-/
theorem complement_balance_int_zero
    {M : ℕ}
    {rows : List FerrersRow}
    {F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows 0 digits F) :
    (M : ℤ) * ((ternaryComplementValue digits : ℤ) + 1) -
        (ferrersWeightedDefect rows : ℤ) =
      ((3 ^ rows.length : ℕ) : ℤ) * ((M : ℤ) - (F : ℤ)) := by
  simpa using h.complement_balance_int

/--
初期 carry が modulus 自身 `E=M` の場合。

`M*D - S = 3^P(M-F)`。

これは interior block の weak budget
`S ≤ M*D`
を final carry bound `F ≤ M` と結びつける形である。
-/
theorem complement_balance_int_modulus
    {M : ℕ}
    {rows : List FerrersRow}
    {F : ℕ}
    {digits : List ℕ}
    (h : CarryRealizes M rows M digits F) :
    (M : ℤ) * (ternaryComplementValue digits : ℤ) -
        (ferrersWeightedDefect rows : ℤ) =
      ((3 ^ rows.length : ℕ) : ℤ) * ((M : ℤ) - (F : ℤ)) := by
  have hMain := h.complement_balance_int
  calc
    (M : ℤ) * (ternaryComplementValue digits : ℤ) -
          (ferrersWeightedDefect rows : ℤ)
        = ((M : ℤ) * ((ternaryComplementValue digits : ℤ) + 1) -
            (ferrersWeightedDefect rows : ℤ)) - (M : ℤ) := by
              ring
    _ = (((3 ^ rows.length : ℕ) : ℤ) * ((M : ℤ) - (F : ℤ)) +
            (M : ℤ)) - (M : ℤ) := by
          rw [hMain]
    _ = ((3 ^ rows.length : ℕ) : ℤ) * ((M : ℤ) - (F : ℤ)) := by
          ring

end CarryRealizes

end CSTCarry
end Collatz3
