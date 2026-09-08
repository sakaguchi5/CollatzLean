import CollatzLean.Collatz3.Canonical.AffineDataResidue
import CollatzLean.Collatz3.Core.EndpointEquation

import Mathlib.Tactic.Ring

/-!
# Collatz3: Word の odd-endpoint residue wrapper

canonical residue の数学的正本は `AffineDataResidue` に置く。
このファイルは Word の affine data

`(oddSteps w, twoSteps w, affineConst w)`

を共有核へ渡す薄い specialization と、
actual endpoint equation から residue class へ降ろす bridge だけを持つ。
-/

namespace Collatz3
namespace Word

/-- 奇数 endpoint を分類する法 `2^(H+1)`。 -/
def oddEndpointModulus (w : Word) : ℕ :=
  oddEndpointModulusOfAffineData (twoSteps w)

@[simp] theorem oddEndpointModulus_eq (w : Word) :
    oddEndpointModulus w = 2 ^ (twoSteps w + 1) := by
  rfl

@[simp] theorem oddEndpointModulus_pos (w : Word) :
    0 < oddEndpointModulus w := by
  exact oddEndpointModulusOfAffineData_pos (twoSteps w)

/-- Word の affine data が決める odd-start residue class。 -/
def oddStartClass (w : Word) :
    ZMod (oddEndpointModulus w) :=
  oddStartClassOfAffineData
    (oddSteps w)
    (twoSteps w)
    (affineConst w)

@[simp] theorem oddStartClass_eq_affineData (w : Word) :
    oddStartClass w =
      oddStartClassOfAffineData
        (oddSteps w)
        (twoSteps w)
        (affineConst w) := by
  rfl

/-- Word の odd-start class は defining congruence を満たす。 -/
theorem oddStartClass_spec (w : Word) :
    (((3 ^ oddSteps w : ℕ) :
        ZMod (oddEndpointModulus w)) *
      oddStartClass w) +
        ((affineConst w : ℕ) :
          ZMod (oddEndpointModulus w)) =
      ((2 ^ twoSteps w : ℕ) :
        ZMod (oddEndpointModulus w)) := by
  change
    (((3 ^ oddSteps w : ℕ) :
        ZMod (oddEndpointModulusOfAffineData (twoSteps w))) *
      oddStartClassOfAffineData
        (oddSteps w)
        (twoSteps w)
        (affineConst w)) +
      ((affineConst w : ℕ) :
        ZMod (oddEndpointModulusOfAffineData (twoSteps w))) =
    ((2 ^ twoSteps w : ℕ) :
      ZMod (oddEndpointModulusOfAffineData (twoSteps w)))
  exact
    oddStartClassOfAffineData_spec
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- defining congruence の解は Word odd-start class に一意。 -/
theorem oddStartClass_unique
    (w : Word)
    (x : ZMod (oddEndpointModulus w))
    (hx :
      (((3 ^ oddSteps w : ℕ) :
          ZMod (oddEndpointModulus w)) * x) +
        ((affineConst w : ℕ) :
          ZMod (oddEndpointModulus w)) =
        ((2 ^ twoSteps w : ℕ) :
          ZMod (oddEndpointModulus w))) :
    x = oddStartClass w := by
  exact
    oddStartClassOfAffineData_unique
      (oddSteps w)
      (twoSteps w)
      (affineConst w)
      x
      hx

/-- Word canonical start `R`。 -/
def canonicalStart (w : Word) : ℕ :=
  canonicalStartOfAffineData
    (oddSteps w)
    (twoSteps w)
    (affineConst w)

theorem canonicalStart_eq_oddStartClass_val
    (w : Word) :
    canonicalStart w = (oddStartClass w).val := by
  rfl

/--
odd endpoint を持つ endpoint equation の start は
必ず Word odd-start class に属する。
-/
theorem EndpointEquation.start_has_oddStartClass
    {w : Word} {x y : ℕ}
    (h : w.EndpointEquation x y)
    (hy : Odd y) :
    ((x : ℕ) : ZMod (oddEndpointModulus w)) =
      oddStartClass w := by
  apply oddStartClass_unique
  have hEq := (endpointEquation_iff w x y).1 h
  have hcast :=
    congrArg
      (fun n : ℕ =>
        (n : ZMod (oddEndpointModulus w))) hEq
  rcases hy with ⟨k, rfl⟩
  have hid :
      2 ^ twoSteps w * (2 * k + 1) =
        2 ^ twoSteps w +
          oddEndpointModulus w * k := by
    unfold oddEndpointModulus
      oddEndpointModulusOfAffineData
      Arithmetic.twoPowModulus
    rw [pow_succ]
    ring
  calc
    (((3 ^ oddSteps w : ℕ) :
          ZMod (oddEndpointModulus w)) *
        ((x : ℕ) :
          ZMod (oddEndpointModulus w))) +
      ((affineConst w : ℕ) :
        ZMod (oddEndpointModulus w))
        =
      (((2 ^ twoSteps w * (2 * k + 1) : ℕ) :
        ZMod (oddEndpointModulus w))) := by
          simpa using hcast.symm
    _ =
      (((2 ^ twoSteps w +
          oddEndpointModulus w * k : ℕ) :
        ZMod (oddEndpointModulus w))) := by
          rw [hid]
    _ =
      ((2 ^ twoSteps w : ℕ) :
        ZMod (oddEndpointModulus w)) := by
          simp only [
            Nat.cast_add,
            Nat.cast_mul,
            ZMod.natCast_self,
            zero_mul,
            add_zero
          ]

end Word
end Collatz3
