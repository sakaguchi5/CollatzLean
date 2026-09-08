import CollatzLean.Collatz3.Canonical.AffineDataResidue

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3: affine data `(p,H,B)` の canonical coordinates `R,Y,Q`

`R` だけでなく canonical endpoint `Y` と drift `Q = Y-R` まで
Word / Profile に依存しない共有核として一度だけ構成する。

Word 側・Profile 側はこの共有核の薄い wrapper とする。
-/

namespace Collatz3

/-- canonical start を affine equation に代入した numerator。 -/
def canonicalNumeratorOfAffineData
    (p H B : ℕ) : ℕ :=
  3 ^ p * canonicalStartOfAffineData p H B + B

/-- canonical numerator の `2^(H+1)` 剰余は exactly `2^H`。 -/
theorem canonicalNumeratorOfAffineData_mod_modulus
    (p H B : ℕ) :
    canonicalNumeratorOfAffineData p H B %
        oddEndpointModulusOfAffineData H =
      2 ^ H := by
  have : NeZero (oddEndpointModulusOfAffineData H) :=
    ⟨Nat.ne_of_gt (oddEndpointModulusOfAffineData_pos H)⟩
  have hcast :
      ((canonicalNumeratorOfAffineData p H B : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H)) =
        ((2 ^ H : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H)) := by
    calc
      ((canonicalNumeratorOfAffineData p H B : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H))
          =
          (((3 ^ p : ℕ) :
              ZMod (oddEndpointModulusOfAffineData H)) *
            ((canonicalStartOfAffineData p H B : ℕ) :
              ZMod (oddEndpointModulusOfAffineData H))) +
          ((B : ℕ) :
            ZMod (oddEndpointModulusOfAffineData H)) := by
              simp [canonicalNumeratorOfAffineData]
      _ =
          (((3 ^ p : ℕ) :
              ZMod (oddEndpointModulusOfAffineData H)) *
            oddStartClassOfAffineData p H B) +
          ((B : ℕ) :
            ZMod (oddEndpointModulusOfAffineData H)) := by
              rw [canonicalStartOfAffineData_cast]
      _ =
          ((2 ^ H : ℕ) :
            ZMod (oddEndpointModulusOfAffineData H)) :=
        oddStartClassOfAffineData_spec p H B
  have hval := congrArg ZMod.val hcast
  have hpowlt :
      2 ^ H < oddEndpointModulusOfAffineData H := by
    unfold oddEndpointModulusOfAffineData
      Arithmetic.twoPowModulus
    exact
      Nat.pow_lt_pow_right
        (by omega)
        (Nat.lt_succ_self _)
  calc
    canonicalNumeratorOfAffineData p H B %
        oddEndpointModulusOfAffineData H
        =
        (((canonicalNumeratorOfAffineData p H B : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H))).val := by
            simp only [ZMod.val_natCast]
    _ =
        (((2 ^ H : ℕ) :
          ZMod (oddEndpointModulusOfAffineData H))).val :=
      hval
    _ =
        (2 ^ H) % oddEndpointModulusOfAffineData H := by
          simp only [ZMod.val_natCast]
    _ = 2 ^ H :=
      Nat.mod_eq_of_lt hpowlt

/-- canonical numerator は `2^H * odd` と exact に因数分解される。 -/
theorem canonicalNumeratorOfAffineData_eq_twoPow_mul_odd
    (p H B : ℕ) :
    ∃ k : ℕ,
      canonicalNumeratorOfAffineData p H B =
        2 ^ H * (2 * k + 1) := by
  have hdecomp :=
    Nat.mod_add_div
      (canonicalNumeratorOfAffineData p H B)
      (oddEndpointModulusOfAffineData H)
  rw [canonicalNumeratorOfAffineData_mod_modulus p H B] at hdecomp
  refine
    ⟨canonicalNumeratorOfAffineData p H B /
        oddEndpointModulusOfAffineData H, ?_⟩
  calc
    canonicalNumeratorOfAffineData p H B
        =
        2 ^ H +
          oddEndpointModulusOfAffineData H *
            (canonicalNumeratorOfAffineData p H B /
              oddEndpointModulusOfAffineData H) := by
                exact hdecomp.symm
    _ =
        2 ^ H *
          (2 *
              (canonicalNumeratorOfAffineData p H B /
                oddEndpointModulusOfAffineData H) +
            1) := by
              unfold oddEndpointModulusOfAffineData
                Arithmetic.twoPowModulus
              rw [pow_succ]
              ring

/-- canonical endpoint `Y = (3^p R + B) / 2^H`。 -/
def canonicalEndOfAffineData
    (p H B : ℕ) : ℕ :=
  canonicalNumeratorOfAffineData p H B / 2 ^ H

/-- canonical endpoint は numerator を exact に割り切る。 -/
theorem twoPow_mul_canonicalEndOfAffineData
    (p H B : ℕ) :
    2 ^ H * canonicalEndOfAffineData p H B =
      canonicalNumeratorOfAffineData p H B := by
  rcases
      canonicalNumeratorOfAffineData_eq_twoPow_mul_odd p H B
      with ⟨k, hk⟩
  simp [canonicalEndOfAffineData, hk]

/-- canonical endpoint `Y` は奇数。 -/
theorem canonicalEndOfAffineData_odd
    (p H B : ℕ) :
    Odd (canonicalEndOfAffineData p H B) := by
  rcases
      canonicalNumeratorOfAffineData_eq_twoPow_mul_odd p H B
      with ⟨k, hk⟩
  have hEnd :
      canonicalEndOfAffineData p H B = 2 * k + 1 := by
    simp [canonicalEndOfAffineData, hk]
  exact ⟨k, hEnd⟩

/-- canonical drift `Q = Y-R`。符号を失わないため整数値。 -/
def canonicalGapOfAffineData
    (p H B : ℕ) : ℤ :=
  (canonicalEndOfAffineData p H B : ℤ) -
    (canonicalStartOfAffineData p H B : ℤ)

/-- affine-data 版 REQ 基本等式 `2^H Y = 3^p R + B`。 -/
theorem reqEquationOfAffineData
    (p H B : ℕ) :
    2 ^ H * canonicalEndOfAffineData p H B =
      3 ^ p * canonicalStartOfAffineData p H B + B := by
  rw [twoPow_mul_canonicalEndOfAffineData]
  rfl

/-- `B = (2^H-3^p)R + 2^H Q`。 -/
theorem affineTranslation_eq_scaleGap_start_add_twoPow_gap
    (p H B : ℕ) :
    (B : ℤ) =
      ((2 : ℤ) ^ H - (3 : ℤ) ^ p) *
          (canonicalStartOfAffineData p H B : ℤ) +
        (2 : ℤ) ^ H *
          canonicalGapOfAffineData p H B := by
  have hEq :=
    congrArg
      (fun n : ℕ => (n : ℤ))
      (reqEquationOfAffineData p H B)
  push_cast at hEq
  calc
    (B : ℤ)
        =
        (2 : ℤ) ^ H *
            (canonicalEndOfAffineData p H B : ℤ) -
          (3 : ℤ) ^ p *
            (canonicalStartOfAffineData p H B : ℤ) := by
              linarith
    _ =
        ((2 : ℤ) ^ H - (3 : ℤ) ^ p) *
            (canonicalStartOfAffineData p H B : ℤ) +
          (2 : ℤ) ^ H *
            canonicalGapOfAffineData p H B := by
              simp [canonicalGapOfAffineData]
              ring

/-- `B = (2^H-3^p)Y + 3^p Q`。 -/
theorem affineTranslation_eq_scaleGap_end_add_threePow_gap
    (p H B : ℕ) :
    (B : ℤ) =
      ((2 : ℤ) ^ H - (3 : ℤ) ^ p) *
          (canonicalEndOfAffineData p H B : ℤ) +
        (3 : ℤ) ^ p *
          canonicalGapOfAffineData p H B := by
  have hEq :=
    congrArg
      (fun n : ℕ => (n : ℤ))
      (reqEquationOfAffineData p H B)
  push_cast at hEq
  calc
    (B : ℤ)
        =
        (2 : ℤ) ^ H *
            (canonicalEndOfAffineData p H B : ℤ) -
          (3 : ℤ) ^ p *
            (canonicalStartOfAffineData p H B : ℤ) := by
              linarith
    _ =
        ((2 : ℤ) ^ H - (3 : ℤ) ^ p) *
            (canonicalEndOfAffineData p H B : ℤ) +
          (3 : ℤ) ^ p *
            canonicalGapOfAffineData p H B := by
              simp [canonicalGapOfAffineData]
              ring

end Collatz3
