import CollatzLean.Collatz3.Arithmetic.ModTwoPow
import CollatzLean.Collatz3.Core.EndpointEquation

import Mathlib.Tactic.Ring

/-!
# Collatz3: 奇数 endpoint を持つ start の 2進合同類

canonical start を primitive data にしない。

まず affine data `(p,H,B)` だけから、
odd endpoint を持つすべての affine solution が属する一意な
`2^(H+1)` 合同類を導く。

その最小非負代表として canonical start を定義する。

Word 側の定義は、この affine-data API の薄い wrapper とする。

基本となる合同式は

`3^p * R + B = 2^H (mod 2^(H+1))`

である。
-/

namespace Collatz3

/-!
## affine data `(p,H,B)` に対する共有核

ここには Word や Profile の構造を持ち込まない。
`p`, `H`, `B` だけから odd-start class と canonical start を決める。
-/

/--
affine data `(p,H,B)` から決まる odd-start class。

`3^p * R + B = 2^H (mod 2^(H+1))`

の一意解。
-/
def oddStartClassOfAffineData
    (p H B : ℕ) :
    ZMod (Arithmetic.twoPowModulus (H + 1)) :=
  Arithmetic.solveThreePow
    p
    (H + 1)
    ((((2 ^ H : ℕ) :
        ZMod (Arithmetic.twoPowModulus (H + 1))) -
      ((B : ℕ) :
        ZMod (Arithmetic.twoPowModulus (H + 1)))))

/--
affine data の odd-start class は defining congruence

`3^p * R + B = 2^H (mod 2^(H+1))`

を満たす。
-/
theorem oddStartClassOfAffineData_spec
    (p H B : ℕ) :
    (((3 ^ p : ℕ) :
        ZMod (Arithmetic.twoPowModulus (H + 1))) *
      oddStartClassOfAffineData p H B) +
        ((B : ℕ) :
          ZMod (Arithmetic.twoPowModulus (H + 1))) =
      ((2 ^ H : ℕ) :
        ZMod (Arithmetic.twoPowModulus (H + 1)) ) := by
  have h :=
    Arithmetic.threePow_mul_solveThreePow
      p
      (H + 1)
      ((((2 ^ H : ℕ) :
          ZMod (Arithmetic.twoPowModulus (H + 1))) -
        ((B : ℕ) :
          ZMod (Arithmetic.twoPowModulus (H + 1)))))
  unfold oddStartClassOfAffineData
  exact (eq_sub_iff_add_eq).mp h

/--
affine data の defining congruence の解は
`oddStartClassOfAffineData` に一意。
-/
theorem oddStartClassOfAffineData_unique
    (p H B : ℕ)
    (x : ZMod (Arithmetic.twoPowModulus (H + 1)))
    (hx :
      (((3 ^ p : ℕ) :
          ZMod (Arithmetic.twoPowModulus (H + 1))) * x) +
        ((B : ℕ) :
          ZMod (Arithmetic.twoPowModulus (H + 1))) =
        ((2 ^ H : ℕ) :
          ZMod (Arithmetic.twoPowModulus (H + 1)))) :
    x = oddStartClassOfAffineData p H B := by
  apply Arithmetic.solveThreePow_unique
    (p := p)
    (H := H + 1)
    (rhs :=
      (((2 ^ H : ℕ) :
          ZMod (Arithmetic.twoPowModulus (H + 1))) -
        ((B : ℕ) :
          ZMod (Arithmetic.twoPowModulus (H + 1)))))
  exact (eq_sub_iff_add_eq).mpr hx

/--
affine data `(p,H,B)` から決まる canonical start。

odd-start class の最小非負代表。
-/
def canonicalStartOfAffineData
    (p H B : ℕ) : ℕ :=
  (oddStartClassOfAffineData p H B).val

/--
affine-data canonical start は法 `2^(H+1)` 未満。
-/
theorem canonicalStartOfAffineData_lt_modulus
    (p H B : ℕ) :
    canonicalStartOfAffineData p H B <
      Arithmetic.twoPowModulus (H + 1) := by
  have : NeZero (Arithmetic.twoPowModulus (H + 1)) :=
    ⟨Nat.ne_of_gt (Arithmetic.twoPowModulus_pos (H + 1))⟩
  exact ZMod.val_lt (oddStartClassOfAffineData p H B)

/--
canonical start を `ZMod` に戻すと元の odd-start class。
-/
theorem canonicalStartOfAffineData_cast
    (p H B : ℕ) :
    ((canonicalStartOfAffineData p H B : ℕ) :
        ZMod (Arithmetic.twoPowModulus (H + 1))) =
      oddStartClassOfAffineData p H B := by
  have : NeZero (Arithmetic.twoPowModulus (H + 1)) :=
    ⟨Nat.ne_of_gt (Arithmetic.twoPowModulus_pos (H + 1))⟩
  exact ZMod.natCast_zmod_val
    (oddStartClassOfAffineData p H B)

/-!
## Word への specialization

Word 固有の情報は

- `p = oddSteps w`
- `H = twoSteps w`
- `B = affineConst w`

を affine-data API に渡すだけにする。
-/

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

これは affine data

`(oddSteps w, twoSteps w, affineConst w)`

から得られる class の薄い wrapper。
-/
def oddStartClass (w : Word) :
    ZMod (oddEndpointModulus w) :=
  oddStartClassOfAffineData
    (oddSteps w)
    (twoSteps w)
    (affineConst w)

/--
Word の odd-start class は affine-data class そのもの。
-/
@[simp] theorem oddStartClass_eq_affineData (w : Word) :
    oddStartClass w =
      oddStartClassOfAffineData
        (oddSteps w)
        (twoSteps w)
        (affineConst w) := by
  rfl

/-- odd-start class は defining congruence を満たす。 -/
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
        ZMod (Arithmetic.twoPowModulus (twoSteps w + 1))) *
      oddStartClassOfAffineData
        (oddSteps w)
        (twoSteps w)
        (affineConst w)) +
      ((affineConst w : ℕ) :
        ZMod (Arithmetic.twoPowModulus (twoSteps w + 1))) =
    ((2 ^ twoSteps w : ℕ) :
      ZMod (Arithmetic.twoPowModulus (twoSteps w + 1)))
  exact
    oddStartClassOfAffineData_spec
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- defining congruence の解は odd-start class に一意。 -/
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
  simpa [oddEndpointModulus, oddStartClass] using
    (oddStartClassOfAffineData_unique
      (oddSteps w)
      (twoSteps w)
      (affineConst w)
      x
      hx)

/--
canonical start `R`。

Word 自体から primitive に保存するのではなく、
その affine data `(p,H,B)` から導く。
-/
def canonicalStart (w : Word) : ℕ :=
  canonicalStartOfAffineData
    (oddSteps w)
    (twoSteps w)
    (affineConst w)

/--
Word の canonical start は odd-start class の最小非負代表。
-/
theorem canonicalStart_eq_oddStartClass_val
    (w : Word) :
    canonicalStart w = (oddStartClass w).val := by
  rfl

/--
odd endpoint を持つ endpoint equation の start は
必ず odd-start class に属する。
-/
theorem EndpointEquation.start_has_oddStartClass
    {w : Word} {x y : ℕ}
    (h : w.EndpointEquation x y)
    (hy : Odd y) :
    ((x : ℕ) : ZMod (oddEndpointModulus w)) =
      oddStartClass w := by
  apply oddStartClass_unique
  have hEq := (endpointEquation_iff w x y).1 h
  have hcast := congrArg
    (fun n : ℕ =>
      (n : ZMod (oddEndpointModulus w))) hEq
  rcases hy with ⟨k, rfl⟩
  have hid :
      2 ^ twoSteps w * (2 * k + 1) =
        2 ^ twoSteps w +
          oddEndpointModulus w * k := by
    unfold oddEndpointModulus Arithmetic.twoPowModulus
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
