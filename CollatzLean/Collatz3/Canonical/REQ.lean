import CollatzLean.Collatz3.Canonical.AffineDataREQ
import CollatzLean.Collatz3.Canonical.OddEndpointResidue

/-!
# Collatz3: Word canonical coordinates `R,Y,Q`

共有数学の正本は `(p,H,B)` に対する `AffineDataREQ` に置く。
Word 側は自分の affine data を共有核へ渡す薄い wrapper と、
actual endpoint equation に接続する theorem だけを持つ。

RecordFerrers の `E_RF` と区別するため canonical endpoint は `Y` と呼ぶ。
Lean API 名は既存互換のため `canonicalEnd` を維持する。
-/

namespace Collatz3
namespace Word

/-- `R` は odd-endpoint modulus 未満。 -/
theorem canonicalStart_lt_modulus (w : Word) :
    canonicalStart w < oddEndpointModulus w := by
  exact
    canonicalStartOfAffineData_lt_modulus
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- canonical start を `ZMod` に戻すと元の class。 -/
theorem canonicalStart_cast (w : Word) :
    ((canonicalStart w : ℕ) :
        ZMod (oddEndpointModulus w)) =
      oddStartClass w := by
  exact
    canonicalStartOfAffineData_cast
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- odd endpoint を持つ endpoint equation の start の剰余は `R`。 -/
theorem EndpointEquation.start_mod_eq_canonicalStart
    {w : Word} {x y : ℕ}
    (h : w.EndpointEquation x y)
    (hy : Odd y) :
    x % oddEndpointModulus w = canonicalStart w := by
  have hc := h.start_has_oddStartClass hy
  have hv := congrArg ZMod.val hc
  rw [canonicalStart_eq_oddStartClass_val]
  simpa only [ZMod.val_natCast] using hv

/-- `R` は同じ odd-endpoint affine class の最小自然数 start。 -/
theorem EndpointEquation.canonicalStart_le_start
    {w : Word} {x y : ℕ}
    (h : w.EndpointEquation x y)
    (hy : Odd y) :
    canonicalStart w ≤ x := by
  have hmod := h.start_mod_eq_canonicalStart hy
  have hdecomp := Nat.mod_add_div x (oddEndpointModulus w)
  rw [hmod] at hdecomp
  omega

/-- Word canonical numerator。 -/
def canonicalNumerator (w : Word) : ℕ :=
  canonicalNumeratorOfAffineData
    (oddSteps w)
    (twoSteps w)
    (affineConst w)

/-- canonical numerator の `2^(H+1)` 剰余は exactly `2^H`。 -/
theorem canonicalNumerator_mod_modulus (w : Word) :
    canonicalNumerator w % oddEndpointModulus w =
      2 ^ twoSteps w := by
  exact
    canonicalNumeratorOfAffineData_mod_modulus
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- canonical numerator は `2^H * odd`。 -/
theorem canonicalNumerator_eq_twoPow_mul_odd (w : Word) :
    ∃ k : ℕ,
      canonicalNumerator w =
        2 ^ twoSteps w * (2 * k + 1) := by
  exact
    canonicalNumeratorOfAffineData_eq_twoPow_mul_odd
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- canonical endpoint `Y = (3^p R + B) / 2^H`。 -/
def canonicalEnd (w : Word) : ℕ :=
  canonicalEndOfAffineData
    (oddSteps w)
    (twoSteps w)
    (affineConst w)

/-- canonical endpoint は numerator を exact に割り切る。 -/
theorem twoPow_mul_canonicalEnd (w : Word) :
    2 ^ twoSteps w * canonicalEnd w =
      canonicalNumerator w := by
  exact
    twoPow_mul_canonicalEndOfAffineData
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- canonical endpoint `Y` は奇数。 -/
theorem canonicalEnd_odd (w : Word) :
    Odd (canonicalEnd w) := by
  exact
    canonicalEndOfAffineData_odd
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- canonical start/end は endpoint equation を満たす。 -/
theorem canonical_endpointEquation (w : Word) :
    w.EndpointEquation (canonicalStart w) (canonicalEnd w) := by
  apply
    (endpointEquation_iff
      w (canonicalStart w) (canonicalEnd w)).2
  exact
    reqEquationOfAffineData
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- canonical drift `Q = Y-R`。 -/
def canonicalGap (w : Word) : ℤ :=
  canonicalGapOfAffineData
    (oddSteps w)
    (twoSteps w)
    (affineConst w)

/-- 基本恒等式 `2^H Y = 3^p R + B`。 -/
theorem req_equation (w : Word) :
    2 ^ twoSteps w * canonicalEnd w =
      3 ^ oddSteps w * canonicalStart w + affineConst w := by
  exact
    reqEquationOfAffineData
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- `B = (2^H-3^p)R + 2^H Q`。 -/
theorem affineConst_eq_gap_start_add_twoPow_gap (w : Word) :
    (affineConst w : ℤ) =
      signedScaleGap w * (canonicalStart w : ℤ) +
        (2 ^ twoSteps w : ℤ) * canonicalGap w := by
  rw [signedScaleGap_eq]
  change
    (affineConst w : ℤ) =
      ((2 : ℤ) ^ twoSteps w - (3 : ℤ) ^ oddSteps w) *
          (canonicalStartOfAffineData
            (oddSteps w) (twoSteps w) (affineConst w) : ℤ) +
        (2 : ℤ) ^ twoSteps w *
          canonicalGapOfAffineData
            (oddSteps w) (twoSteps w) (affineConst w)
  exact
    affineTranslation_eq_scaleGap_start_add_twoPow_gap
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

/-- `B = (2^H-3^p)Y + 3^p Q`。 -/
theorem affineConst_eq_gap_end_add_threePow_gap (w : Word) :
    (affineConst w : ℤ) =
      signedScaleGap w * (canonicalEnd w : ℤ) +
        (3 ^ oddSteps w : ℤ) * canonicalGap w := by
  rw [signedScaleGap_eq]
  change
    (affineConst w : ℤ) =
      ((2 : ℤ) ^ twoSteps w - (3 : ℤ) ^ oddSteps w) *
          (canonicalEndOfAffineData
            (oddSteps w) (twoSteps w) (affineConst w) : ℤ) +
        (3 : ℤ) ^ oddSteps w *
          canonicalGapOfAffineData
            (oddSteps w) (twoSteps w) (affineConst w)
  exact
    affineTranslation_eq_scaleGap_end_add_threePow_gap
      (oddSteps w)
      (twoSteps w)
      (affineConst w)

end Word
end Collatz3
