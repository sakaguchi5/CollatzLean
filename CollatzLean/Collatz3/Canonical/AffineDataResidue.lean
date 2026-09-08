import CollatzLean.Collatz3.Arithmetic.ModTwoPow

/-!
# Collatz3: affine data `(p,H,B)` の odd-endpoint residue

Word / Profile に依存しない canonical residue の共有核。

affine equation

`2^H * y = 3^p * x + B`

で endpoint `y` を奇数にする start は

`3^p * x + B = 2^H (mod 2^(H+1))`

を満たす。この一意な合同類と、その最小非負代表だけをここで定義する。
-/

namespace Collatz3

/-- affine data `(p,H,B)` の odd endpoint を分類する法 `2^(H+1)`。 -/
def oddEndpointModulusOfAffineData (H : ℕ) : ℕ :=
  Arithmetic.twoPowModulus (H + 1)

@[simp] theorem oddEndpointModulusOfAffineData_eq (H : ℕ) :
    oddEndpointModulusOfAffineData H = 2 ^ (H + 1) := by
  rfl

@[simp] theorem oddEndpointModulusOfAffineData_pos (H : ℕ) :
    0 < oddEndpointModulusOfAffineData H := by
  simp [oddEndpointModulusOfAffineData, Arithmetic.twoPowModulus]

/--
affine data `(p,H,B)` から決まる odd-start class。

`3^p * R + B = 2^H (mod 2^(H+1))`
の一意解。
-/
def oddStartClassOfAffineData
    (p H B : ℕ) :
    ZMod (oddEndpointModulusOfAffineData H) :=
  Arithmetic.solveThreePow
    p
    (H + 1)
    ((((2 ^ H : ℕ) :
        ZMod (oddEndpointModulusOfAffineData H))) -
      ((B : ℕ) :
        ZMod (oddEndpointModulusOfAffineData H)))

/-- affine-data odd-start class は defining congruence を満たす。 -/
theorem oddStartClassOfAffineData_spec
    (p H B : ℕ) :
    (((3 ^ p : ℕ) :
        ZMod (oddEndpointModulusOfAffineData H)) *
      oddStartClassOfAffineData p H B) +
        ((B : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H)) =
      ((2 ^ H : ℕ) :
        ZMod (oddEndpointModulusOfAffineData H)) := by
  have h :=
    Arithmetic.threePow_mul_solveThreePow
      p
      (H + 1)
      ((((2 ^ H : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H))) -
        ((B : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H)))
  unfold oddStartClassOfAffineData
  exact (eq_sub_iff_add_eq).mp h

/-- defining congruence の解は affine-data odd-start class に一意。 -/
theorem oddStartClassOfAffineData_unique
    (p H B : ℕ)
    (x : ZMod (oddEndpointModulusOfAffineData H))
    (hx :
      (((3 ^ p : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H)) * x) +
        ((B : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H)) =
        ((2 ^ H : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H))) :
    x = oddStartClassOfAffineData p H B := by
  apply Arithmetic.solveThreePow_unique
    (p := p)
    (H := H + 1)
    (rhs :=
      (((2 ^ H : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H)) -
        ((B : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H))))
  exact (eq_sub_iff_add_eq).mpr hx

/--
affine data `(p,H,B)` から決まる canonical start `R`。
odd-start class の最小非負代表。
-/
def canonicalStartOfAffineData
    (p H B : ℕ) : ℕ :=
  (oddStartClassOfAffineData p H B).val

/-- affine-data canonical start は法 `2^(H+1)` 未満。 -/
theorem canonicalStartOfAffineData_lt_modulus
    (p H B : ℕ) :
    canonicalStartOfAffineData p H B <
      oddEndpointModulusOfAffineData H := by
  have : NeZero (oddEndpointModulusOfAffineData H) :=
    ⟨Nat.ne_of_gt (oddEndpointModulusOfAffineData_pos H)⟩
  exact ZMod.val_lt (oddStartClassOfAffineData p H B)

/-- canonical start を `ZMod` に戻すと元の odd-start class。 -/
theorem canonicalStartOfAffineData_cast
    (p H B : ℕ) :
    ((canonicalStartOfAffineData p H B : ℕ) :
        ZMod (oddEndpointModulusOfAffineData H)) =
      oddStartClassOfAffineData p H B := by
  have : NeZero (oddEndpointModulusOfAffineData H) :=
    ⟨Nat.ne_of_gt (oddEndpointModulusOfAffineData_pos H)⟩
  exact ZMod.natCast_zmod_val
    (oddStartClassOfAffineData p H B)

end Collatz3
