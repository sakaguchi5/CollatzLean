import CollatzLean.Collatz3.Arithmetic.ModTwoPow
import CollatzLean.Collatz3.Core.EndpointEquation
import Mathlib.Tactic.Ring

/-!
# Collatz3: 奇数 endpoint を持つ start の 2進合同類

canonical start を primitive data にしない。
まず odd endpoint を持つすべての affine solution が属する一意な
`2^(H+1)` 合同類を lossless endpoint equation から導く。
-/

namespace Collatz3
namespace Word

/-- 奇数 endpoint を分類する法 `2^(H+1)`。 -/
def oddEndpointModulus (w : Word) : ℕ :=
  Arithmetic.twoPowModulus (twoSteps w + 1)

@[simp] theorem oddEndpointModulus_eq (w : Word) :
    oddEndpointModulus w = 2 ^ (twoSteps w + 1) := by
  rfl

@[simp] theorem oddEndpointModulus_pos (w : Word) :
    0 < oddEndpointModulus w := by
  simp [oddEndpointModulus, Arithmetic.twoPowModulus]

/--
奇数 endpoint を持つ affine solution の start が属する一意な合同類。
`3^p * R + A = 2^H (mod 2^(H+1))` を解く。
-/
def oddStartClass (w : Word) : ZMod (oddEndpointModulus w) :=
  Arithmetic.solveThreePow
    (oddSteps w)
    (twoSteps w + 1)
    ((((2 ^ twoSteps w : ℕ) : ZMod (oddEndpointModulus w))) -
      ((affineConst w : ℕ) : ZMod (oddEndpointModulus w)))

/-- odd-start class は defining congruence を満たす。 -/
theorem oddStartClass_spec (w : Word) :
    (((3 ^ oddSteps w : ℕ) : ZMod (oddEndpointModulus w)) * oddStartClass w) +
      ((affineConst w : ℕ) : ZMod (oddEndpointModulus w)) =
      ((2 ^ twoSteps w : ℕ) : ZMod (oddEndpointModulus w)) := by
  have h := Arithmetic.threePow_mul_solveThreePow
    (oddSteps w)
    (twoSteps w + 1)
    ((((2 ^ twoSteps w : ℕ) : ZMod (oddEndpointModulus w))) -
      ((affineConst w : ℕ) : ZMod (oddEndpointModulus w)))
  unfold oddStartClass
  exact (eq_sub_iff_add_eq).mp h

/-- defining congruence の解は odd-start class に一意。 -/
theorem oddStartClass_unique
    (w : Word)
    (x : ZMod (oddEndpointModulus w))
    (hx :
      (((3 ^ oddSteps w : ℕ) : ZMod (oddEndpointModulus w)) * x) +
        ((affineConst w : ℕ) : ZMod (oddEndpointModulus w)) =
        ((2 ^ twoSteps w : ℕ) : ZMod (oddEndpointModulus w))) :
    x = oddStartClass w := by
  apply Arithmetic.solveThreePow_unique
    (p := oddSteps w)
    (H := twoSteps w + 1)
    (rhs :=
      (((2 ^ twoSteps w : ℕ) : ZMod (oddEndpointModulus w)) -
        ((affineConst w : ℕ) : ZMod (oddEndpointModulus w))))
  exact (eq_sub_iff_add_eq).mpr hx

/-- odd endpoint を持つ endpoint equation の start は必ず odd-start class に属する。 -/
theorem EndpointEquation.start_has_oddStartClass
    {w : Word} {x y : ℕ}
    (h : w.EndpointEquation x y)
    (hy : Odd y) :
    ((x : ℕ) : ZMod (oddEndpointModulus w)) = oddStartClass w := by
  apply oddStartClass_unique
  have hEq := (endpointEquation_iff w x y).1 h
  have hcast := congrArg
    (fun n : ℕ => (n : ZMod (oddEndpointModulus w))) hEq
  rcases hy with ⟨k, rfl⟩
  have hid :
      2 ^ twoSteps w * (2 * k + 1) =
        2 ^ twoSteps w + oddEndpointModulus w * k := by
    unfold oddEndpointModulus Arithmetic.twoPowModulus
    rw [pow_succ]
    ring
  calc
    (((3 ^ oddSteps w : ℕ) : ZMod (oddEndpointModulus w)) *
          ((x : ℕ) : ZMod (oddEndpointModulus w))) +
        ((affineConst w : ℕ) : ZMod (oddEndpointModulus w))
        =
        (((2 ^ twoSteps w * (2 * k + 1) : ℕ) :
          ZMod (oddEndpointModulus w))) := by
            simpa using hcast.symm
    _ =
        (((2 ^ twoSteps w + oddEndpointModulus w * k : ℕ) :
          ZMod (oddEndpointModulus w))) := by rw [hid]
    _ = ((2 ^ twoSteps w : ℕ) : ZMod (oddEndpointModulus w)) := by
      simp only [
        Nat.cast_add,
        Nat.cast_mul,
        ZMod.natCast_self,
        zero_mul,
        add_zero
      ]

end Word
end Collatz3
