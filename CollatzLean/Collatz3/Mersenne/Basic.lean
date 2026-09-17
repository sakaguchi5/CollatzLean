import CollatzLean.Collatz3.Arithmetic.Pow23
import Mathlib.Tactic.Ring


/-!
# Collatz3 Mersenne: block arithmetic kernel

trailing-one Mersenne block を、actual orbit を使わない exact 整数関係として保存する。

primitive data は

`x + 1 = 2^d * u`
`2^r * y + 1 = 3^d * u`

と、正の depth、正の exit depth、終点 `y` の奇数性だけ。
actual `Runs` への接続は Bridge 層で導く。
-/

namespace Collatz3
namespace Mersenne

/--
Mersenne block の exact arithmetic data。

`d` は trailing-one block の長さ、`r` は最後の step に追加される 2-depth。
-/
def BlockData
    (d r u x y : ℕ) : Prop :=
  0 < d ∧
    0 < r ∧
    Odd y ∧
    x + 1 = 2 ^ d * u ∧
    2 ^ r * y + 1 = 3 ^ d * u

namespace BlockData

/-- block depth は正。 -/
theorem depth_pos
    {d r u x y : ℕ}
    (h : BlockData d r u x y) :
    0 < d := h.1

/-- exit depth は正。 -/
theorem exitDepth_pos
    {d r u x y : ℕ}
    (h : BlockData d r u x y) :
    0 < r := h.2.1

/-- macro endpoint は奇数。 -/
theorem end_odd
    {d r u x y : ℕ}
    (h : BlockData d r u x y) :
    Odd y := h.2.2.1

/-- source の exact trailing-one equation。 -/
theorem startEquation
    {d r u x y : ℕ}
    (h : BlockData d r u x y) :
    x + 1 = 2 ^ d * u := h.2.2.2.1

/-- endpoint の exact Mersenne macro equation。 -/
theorem endEquation
    {d r u x y : ℕ}
    (h : BlockData d r u x y) :
    2 ^ r * y + 1 = 3 ^ d * u := h.2.2.2.2

end BlockData

/-- `x+1=2q` なら `x` は奇数。 -/
theorem odd_of_add_one_eq_two_mul
    {x q : ℕ}
    (h : x + 1 = 2 * q) :
    Odd x := by
  have hq : 0 < q := by omega
  obtain ⟨t, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  refine ⟨t, ?_⟩
  omega

/-- BlockData の source は primitive field に置かなくても奇数と分かる。 -/
theorem BlockData.start_odd
    {d r u x y : ℕ}
    (h : BlockData d r u x y) :
    Odd x := by
  obtain ⟨e, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h.depth_pos)
  have hEq : x + 1 = 2 * (2 ^ e * u) := by
    calc
      x + 1 = 2 ^ (e + 1) * u := h.startEquation
      _ = 2 * (2 ^ e * u) := by
        rw [pow_succ]
        ring
  exact odd_of_add_one_eq_two_mul hEq

end Mersenne
end Collatz3
