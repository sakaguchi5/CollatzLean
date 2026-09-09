import CollatzLean.Collatz3.Arithmetic.Pow23
import CollatzLean.Collatz3.Core.Word
import Mathlib.Tactic.Ring


/-!
# Collatz3: actual odd-only Collatz 1 step

primitive data は正の指数、exact affine equation、正規化後 endpoint の奇数性だけ。
始点の奇数性はこれらから導く。
-/

namespace Collatz3

/-- exact odd-only Collatz step。 -/
def OddStep (e x y : ℕ) : Prop :=
  0 < e ∧ 2 ^ e * y = 3 * x + 1 ∧ Odd y

namespace OddStep

/-- actual step の指数は正。 -/
theorem exponent_pos {e x y : ℕ} (h : OddStep e x y) : 0 < e :=
  h.1

/-- actual step の exact affine equation。 -/
theorem equation {e x y : ℕ} (h : OddStep e x y) :
    2 ^ e * y = 3 * x + 1 :=
  h.2.1

/-- actual step の終点は奇数。 -/
theorem end_odd {e x y : ℕ} (h : OddStep e x y) : Odd y :=
  h.2.2

/-- 始点の奇数性は正の指数と exact equation から従う。 -/
theorem start_odd {e x y : ℕ} (h : OddStep e x y) : Odd x := by
  obtain ⟨k, hEven | hOdd⟩ := x.even_or_odd'
  · cases e with
    | zero => exact False.elim h.1.false
    | succ e =>
        have hEq : 2 * (2 ^ e * y) = 6 * k + 1 := by
          calc
            2 * (2 ^ e * y) = 2 ^ (e + 1) * y := by
              rw [pow_succ]
              ring
            _ = 3 * x + 1 := h.equation
            _ = 6 * k + 1 := by rw [hEven]; ring
        omega
  · exact ⟨k, by omega⟩

/--
同じ始点からの exact odd-only step は、2 除算指数も終点も一意。

証明では `2^e * y = 2^f * z` を比較する。
仮に `e < f` なら、奇数 `y` が正の 2 の冪で割り切れることになり矛盾する。
`f < e` も対称である。
-/
theorem deterministic
    {e f x y z : ℕ}
    (hy : OddStep e x y)
    (hz : OddStep f x z) :
    e = f ∧ y = z := by
  have hEq : 2 ^ e * y = 2 ^ f * z := by
    calc
      2 ^ e * y = 3 * x + 1 := hy.equation
      _ = 2 ^ f * z := hz.equation.symm
  have hef : e = f := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hef | hfe
    · have hle : e ≤ f := Nat.le_of_lt hef
      have hPow : 2 ^ f = 2 ^ e * 2 ^ (f - e) := by
        calc
          2 ^ f = 2 ^ (e + (f - e)) := by
            rw [Nat.add_sub_of_le hle]
          _ = 2 ^ e * 2 ^ (f - e) := by
            rw [pow_add]
      have hEq' : 2 ^ e * y = 2 ^ e * (2 ^ (f - e) * z) := by
        calc
          2 ^ e * y = 2 ^ f * z := hEq
          _ = (2 ^ e * 2 ^ (f - e)) * z := by rw [hPow]
          _ = 2 ^ e * (2 ^ (f - e) * z) := by ring
      have hyFactor : y = 2 ^ (f - e) * z :=
        Nat.mul_left_cancel (Arithmetic.twoPow_pos e) hEq'
      have hdPos : 0 < f - e := Nat.sub_pos_of_lt hef
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdPos)
      have hyEven : ∃ q : ℕ, y = 2 * q := by
        refine ⟨2 ^ d * z, ?_⟩
        rw [hyFactor, hd, pow_succ]
        ring
      rcases hy.end_odd with ⟨k, hk⟩
      rcases hyEven with ⟨q, hq⟩
      omega
    · have hle : f ≤ e := Nat.le_of_lt hfe
      have hPow : 2 ^ e = 2 ^ f * 2 ^ (e - f) := by
        calc
          2 ^ e = 2 ^ (f + (e - f)) := by
            rw [Nat.add_sub_of_le hle]
          _ = 2 ^ f * 2 ^ (e - f) := by
            rw [pow_add]
      have hEq' : 2 ^ f * z = 2 ^ f * (2 ^ (e - f) * y) := by
        calc
          2 ^ f * z = 2 ^ e * y := hEq.symm
          _ = (2 ^ f * 2 ^ (e - f)) * y := by rw [hPow]
          _ = 2 ^ f * (2 ^ (e - f) * y) := by ring
      have hzFactor : z = 2 ^ (e - f) * y :=
        Nat.mul_left_cancel (Arithmetic.twoPow_pos f) hEq'
      have hdPos : 0 < e - f := Nat.sub_pos_of_lt hfe
      obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdPos)
      have hzEven : ∃ q : ℕ, z = 2 * q := by
        refine ⟨2 ^ d * y, ?_⟩
        rw [hzFactor, hd, pow_succ]
        ring
      rcases hz.end_odd with ⟨k, hk⟩
      rcases hzEven with ⟨q, hq⟩
      omega
  subst f
  refine ⟨rfl, ?_⟩
  exact Nat.mul_left_cancel (Arithmetic.twoPow_pos e) hEq

/-- `1` の odd-only step は指数 `2` で `1` 自身へ戻る。 -/
theorem one_self : OddStep 2 1 1 := by
  refine ⟨by decide, by decide, ?_⟩
  exact ⟨0, by decide⟩

/-- 始点が `1` の exact odd-only step は必ず終点も `1`。 -/
theorem end_eq_one_of_start_eq_one
    {e y : ℕ}
    (h : OddStep e 1 y) :
    y = 1 :=
  (deterministic h one_self).2

/-- 始点が `1` の exact odd-only step の指数は必ず `2`。 -/
theorem exponent_eq_two_of_start_eq_one
    {e y : ℕ}
    (h : OddStep e 1 y) :
    e = 2 :=
  (deterministic h one_self).1

end OddStep
end Collatz3
