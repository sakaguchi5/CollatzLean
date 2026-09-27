import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTCarry: binary half-threshold と ternary midpoint の双対

一般の odd numerator `A = 2a+1` と even denominator `2m` について、
`m < A` だけから quotient の midpoint threshold が決まる。

first coefficient crossing では

  2^(H-1) < 3^P < 2^H

となるが、midpoint duality 自体に必要なのは下側の不等式

  2^(H-1) < 3^P

だけである。

三進 midpoint は recursive に

  0,
  1_3,
  11_3,
  111_3, ...

を表す。
-/

namespace Collatz3
namespace CSTCarry

/-- P 桁の三進数 `111...111₃`。 -/
def threeMidpoint : ℕ → ℕ
  | 0 => 0
  | p + 1 => 3 * threeMidpoint p + 1

@[simp] theorem threeMidpoint_zero :
    threeMidpoint 0 = 0 := rfl

@[simp] theorem threeMidpoint_succ (p : ℕ) :
    threeMidpoint (p + 1) = 3 * threeMidpoint p + 1 := rfl

/-- `3^P = 2 * 111...111₃ + 1`。 -/
theorem threePow_eq_two_mul_threeMidpoint_add_one (P : ℕ) :
    3 ^ P = 2 * threeMidpoint P + 1 := by
  induction P with
  | zero => simp
  | succ P ih =>
      rw [pow_succ, ih]
      simp only [threeMidpoint_succ]
      ring

/--
一般の odd numerator `A = 2a+1` / even denominator `2m` に対する
quotient threshold lemma。

`0 < m` かつ `m < A` なら、任意の `U : ℕ` に対して

  U ≥ m  <->  floor(AU/(2m)) ≥ a.

`A < 2m` や `U < 2m` はこの同値自体には不要。
-/
theorem quotient_midpoint_iff
    {a m U : ℕ}
    (hm : 0 < m)
    (hLower : m < 2 * a + 1) :
    m ≤ U ↔
      a ≤ ((2 * a + 1) * U) / (2 * m) := by
  have hMpos : 0 < 2 * m := by omega
  constructor
  · intro hHalf
    apply (Nat.le_div_iff_mul_le hMpos).2
    have hLeft : a * (2 * m) ≤ (2 * a + 1) * m := by
      nlinarith
    have hRight : (2 * a + 1) * m ≤ (2 * a + 1) * U :=
      Nat.mul_le_mul_left (2 * a + 1) hHalf
    exact le_trans hLeft hRight
  · intro hQ
    by_contra hNot
    have hUlt : U < m := by omega
    have hDivLt :
        ((2 * a + 1) * U) / (2 * m) < a := by
      apply (Nat.div_lt_iff_lt_mul hMpos).2
      let t := m - 1
      have hmEq : m = t + 1 := by
        dsimp [t]
        omega
      have hUle : U ≤ t := by
        dsimp [t]
        omega
      have hBound :
          (2 * a + 1) * U ≤ (2 * a + 1) * t :=
        Nat.mul_le_mul_left (2 * a + 1) hUle
      have ht : t < 2 * a := by
        rw [hmEq] at hLower
        omega
      have hStrict :
          (2 * a + 1) * t < a * (2 * m) := by
        rw [hmEq]
        nlinarith
      exact lt_of_le_of_lt hBound hStrict
    omega

/--
`A = 3^P`, `M = 2^H` への特殊化。

`0 < H` かつ

  2^(H-1) < 3^P

なら、任意の `U : ℕ` に対して

  U ≥ 2^(H-1)

と

  floor(3^P U / 2^H) ≥ 111...111_3

は exact に同値。

上側 first-crossing 条件 `3^P < 2^H` と `U < 2^H` は
この threshold equivalence 自体には不要。
-/
theorem power_midpoint_duality
    {P H U : ℕ}
    (hH : 0 < H)
    (hLower : 2 ^ (H - 1) < 3 ^ P) :
    2 ^ (H - 1) ≤ U ↔
      threeMidpoint P ≤ (3 ^ P * U) / 2 ^ H := by
  have hHs : H = (H - 1) + 1 := by omega
  have hM : 2 ^ H = 2 * 2 ^ (H - 1) := by
    rw [hHs, pow_succ]
    ring_nf
    simp
  have hA := threePow_eq_two_mul_threeMidpoint_add_one P
  have hBase := quotient_midpoint_iff
    (a := threeMidpoint P)
    (m := 2 ^ (H - 1))
    (U := U)
    (by positivity)
    (by simpa [hA] using hLower)
  simpa [hA, hM] using hBase

end CSTCarry
end Collatz3
