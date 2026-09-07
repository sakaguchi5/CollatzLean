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

end OddStep
end Collatz3
