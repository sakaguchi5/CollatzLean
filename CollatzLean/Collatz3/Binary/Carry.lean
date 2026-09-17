import CollatzLean.Collatz3.Binary.Basic
import Mathlib.Tactic.Ring


/-!
# Collatz3 Binary: bitwise carry for `3*x + carry`

1 bit を読む局所 carry transducer を自然数だけで定義する。
output digit は Bool に戻さず `0` / `1` の自然数として保持し、
exact division identity を primitive theorem とする。

この層は Collatz の odd-step semantics を import しない。
-/

namespace Collatz3
namespace Binary

/-- 1 bit を読んだときの局所整数。 -/
def carryInput (carry : ℕ) (b : Bool) : ℕ :=
  3 * bitValue b + carry

/-- 局所 output bit (`0` または `1`)。 -/
def carryOutput (carry : ℕ) (b : Bool) : ℕ :=
  carryInput carry b % 2

/-- 次 bit へ渡す carry。 -/
def carryNext (carry : ℕ) (b : Bool) : ℕ :=
  carryInput carry b / 2

/-- output と next carry を一組で読む。 -/
def carryStep (carry : ℕ) (b : Bool) : ℕ × ℕ :=
  (carryOutput carry b, carryNext carry b)

/-- output digit は必ず `2` 未満。 -/
theorem carryOutput_lt_two (carry : ℕ) (b : Bool) :
    carryOutput carry b < 2 := by
  unfold carryOutput
  exact Nat.mod_lt _ (by decide)

/-- 1 bit carry step の exact decomposition。 -/
theorem carryStep_decompose (carry : ℕ) (b : Bool) :
    carryOutput carry b + 2 * carryNext carry b =
      3 * bitValue b + carry := by
  unfold carryOutput carryNext carryInput
  exact Nat.mod_add_div (3 * bitValue b + carry) 2

/-- `0/1` 自然数 digit 列の LSB-first value。 -/
def digitValueLSB : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 2 * digitValueLSB ds

/--
有限 binary word 全体へ carry transducer を走らせる。
返り値は `(output digits, final carry)`。
-/
def carryScan (carry : ℕ) : List Bool → List ℕ × ℕ
  | [] => ([], carry)
  | b :: bs =>
      let next := carryNext carry b
      let tail := carryScan next bs
      (carryOutput carry b :: tail.1, tail.2)

@[simp] theorem carryScan_nil (carry : ℕ) :
    carryScan carry [] = ([], carry) := rfl

/--
carry scan の exact value invariant。

`bits` が値 `x` を持つとき、有限 output と final carry を合わせた値は
`3*x + initialCarry` に一致する。
-/
theorem carryScan_value (carry : ℕ) (bits : List Bool) :
    digitValueLSB (carryScan carry bits).1 +
        2 ^ bits.length * (carryScan carry bits).2 =
      3 * valueLSB bits + carry := by
  induction bits generalizing carry with
  | nil =>
      simp [carryScan, digitValueLSB]
  | cons b bs ih =>
      change
        carryOutput carry b +
              2 * digitValueLSB (carryScan (carryNext carry b) bs).1 +
              2 ^ (bs.length + 1) *
                (carryScan (carryNext carry b) bs).2 =
          3 * (bitValue b + 2 * valueLSB bs) + carry
      calc
        carryOutput carry b +
              2 * digitValueLSB (carryScan (carryNext carry b) bs).1 +
              2 ^ (bs.length + 1) *
                (carryScan (carryNext carry b) bs).2
            =
            carryOutput carry b +
              2 *
                (digitValueLSB (carryScan (carryNext carry b) bs).1 +
                  2 ^ bs.length *
                    (carryScan (carryNext carry b) bs).2) := by
                rw [pow_succ]
                ring
        _ =
            carryOutput carry b +
              2 * (3 * valueLSB bs + carryNext carry b) := by
                rw [ih (carryNext carry b)]
        _ = 3 * (bitValue b + 2 * valueLSB bs) + carry := by
                have hLocal := carryStep_decompose carry b
                omega

/-- 初期 carry `1` は finite word 上の `3*x+1` を exact に計算する。 -/
theorem carryScan_three_mul_add_one (bits : List Bool) :
    digitValueLSB (carryScan 1 bits).1 +
        2 ^ bits.length * (carryScan 1 bits).2 =
      3 * valueLSB bits + 1 :=
  carryScan_value 1 bits

end Binary
end Collatz3
