import CollatzLean.Collatz.FiniteOrbit.Runs
import CollatzLean.Collatz.TwoAdic.Factorization

/-!
# odd-only actual run の決定性

同じ odd start から actual `Runs` を始めると、各 step の exponent は
`3*x+1` の exact 2進指数として一意である。
従って同じ start と同じ word length を持つ二つの actual run は
word も endpoint も一致する。
-/

namespace Collatz
namespace Word
namespace Runs

/-- actual one-step equation は exact 2進分解を与える。 -/
theorem step_exactFactor
    {x y e : ℕ}
    (hstep : 2 ^ e * y = 3 * x + 1)
    (hy : Odd y) :
    Collatz.TwoAdic.ExactFactor (3 * x + 1) e y := by
  exact ⟨hstep.symm, hy⟩

/-- 同じ start からの二つの actual one-step は exponent と next value が一致する。 -/
theorem oneStep_unique
    {x y z e f : ℕ}
    (hstepE : 2 ^ e * y = 3 * x + 1)
    (hy : Odd y)
    (hstepF : 2 ^ f * z = 3 * x + 1)
    (hz : Odd z) :
    e = f ∧ y = z := by
  have hE := step_exactFactor hstepE hy
  have hF := step_exactFactor hstepF hz
  have hef := Collatz.TwoAdic.exponent_unique hE hF
  subst f
  have hscaled : 2 ^ e * y = 2 ^ e * z :=
    hstepE.trans hstepF.symm
  have hyz : y = z :=
    Nat.mul_left_cancel
      (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hscaled
  exact ⟨rfl, hyz⟩

/--
同じ start と同じ length を持つ actual run は word と endpoint が一意。
-/
theorem unique_of_same_start_same_length
    {u v : Collatz.Word} {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v x z)
    (hlen : u.length = v.length) :
    u = v ∧ y = z := by
  induction hu generalizing v z with
  | nil x =>
      cases hv with
      | nil => exact ⟨rfl, rfl⟩
      | cons => simp at hlen
  | @cons e u x y₁ y he hstepE hy₁ htail ih =>
      cases hv with
      | nil => simp at hlen
      | @cons f v _ z₁ z hf hstepF hz₁ htailV =>
          have hhead := oneStep_unique hstepE hy₁ hstepF hz₁
          rcases hhead with ⟨hef, hyz⟩
          subst f
          subst z₁
          have htailLen : u.length = v.length := by
            simpa using hlen
          have htailUnique := ih htailV htailLen
          rcases htailUnique with ⟨huv, hyzEnd⟩
          subst v
          exact ⟨rfl, hyzEnd⟩

/-- 同じ start・length の actual run は endpoint が一致する。 -/
theorem end_unique_of_same_start_same_length
    {u v : Collatz.Word} {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v x z)
    (hlen : u.length = v.length) :
    y = z :=
  (hu.unique_of_same_start_same_length hv hlen).2

/-- 同じ start・length の actual run は exponent word が一致する。 -/
theorem word_unique_of_same_start_same_length
    {u v : Collatz.Word} {x y z : ℕ}
    (hu : Runs u x y)
    (hv : Runs v x z)
    (hlen : u.length = v.length) :
    u = v :=
  (hu.unique_of_same_start_same_length hv hlen).1

end Runs
end Word
end Collatz
