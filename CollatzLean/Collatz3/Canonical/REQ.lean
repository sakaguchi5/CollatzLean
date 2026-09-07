import CollatzLean.Collatz3.Canonical.OddEndpointResidue
import Mathlib.Tactic.Linarith
/-!
# Collatz3: canonical coordinates `R, E, Q`

`R` は odd-start class の最小非負代表、`E` はその affine endpoint、
`Q = E - R` は符号を失わない canonical drift とする。
`R,E,Q` を packet field として保存せず、すべて word から関数として導く。
-/

namespace Collatz3
namespace Word

/-- canonical start `R`: odd-start class の最小非負代表。 -/
def canonicalStart (w : Word) : ℕ :=
  (oddStartClass w).val

/-- `R` は odd-endpoint modulus 未満。 -/
theorem canonicalStart_lt_modulus (w : Word) :
    canonicalStart w < oddEndpointModulus w := by
  have : NeZero (oddEndpointModulus w) :=
    ⟨Nat.ne_of_gt (oddEndpointModulus_pos w)⟩
  exact ZMod.val_lt (oddStartClass w)

/-- canonical start を ZMod に戻すと元の class。 -/
theorem canonicalStart_cast (w : Word) :
    ((canonicalStart w : ℕ) : ZMod (oddEndpointModulus w)) =
      oddStartClass w := by
  have : NeZero (oddEndpointModulus w) :=
    ⟨Nat.ne_of_gt (oddEndpointModulus_pos w)⟩
  exact ZMod.natCast_zmod_val (oddStartClass w)

/-- odd endpoint を持つ endpoint equation の start の剰余は `R`。 -/
theorem EndpointEquation.start_mod_eq_canonicalStart
    {w : Word} {x y : ℕ}
    (h : w.EndpointEquation x y)
    (hy : Odd y) :
    x % oddEndpointModulus w = canonicalStart w := by
  have hc := h.start_has_oddStartClass hy
  have hv := congrArg ZMod.val hc
  simpa [canonicalStart, ZMod.val_natCast] using hv

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

/-- canonical start を affine equation に代入した分子。 -/
def canonicalNumerator (w : Word) : ℕ :=
  3 ^ oddSteps w * canonicalStart w + affineConst w

/-- canonical numerator の `2^(H+1)` 剰余は exactly `2^H`。 -/
theorem canonicalNumerator_mod_modulus (w : Word) :
    canonicalNumerator w % oddEndpointModulus w = 2 ^ twoSteps w := by
  have : NeZero (oddEndpointModulus w) := ⟨Nat.ne_of_gt (oddEndpointModulus_pos w)⟩
  have hcast :
      ((canonicalNumerator w : ℕ) : ZMod (oddEndpointModulus w)) =
        ((2 ^ twoSteps w : ℕ) : ZMod (oddEndpointModulus w)) := by
    calc
      ((canonicalNumerator w : ℕ) : ZMod (oddEndpointModulus w))
          =
          (((3 ^ oddSteps w : ℕ) : ZMod (oddEndpointModulus w)) *
              ((canonicalStart w : ℕ) : ZMod (oddEndpointModulus w))) +
            ((affineConst w : ℕ) : ZMod (oddEndpointModulus w)) := by
              simp [canonicalNumerator]
      _ =
          (((3 ^ oddSteps w : ℕ) : ZMod (oddEndpointModulus w)) *
              oddStartClass w) +
            ((affineConst w : ℕ) : ZMod (oddEndpointModulus w)) := by
              rw [canonicalStart_cast]
      _ = ((2 ^ twoSteps w : ℕ) : ZMod (oddEndpointModulus w)) :=
        oddStartClass_spec w
  have hval := congrArg ZMod.val hcast
  have hpowlt : 2 ^ twoSteps w < oddEndpointModulus w := by
    unfold oddEndpointModulus Arithmetic.twoPowModulus
    exact Nat.pow_lt_pow_right (by omega) (Nat.lt_succ_self _)
  calc
    canonicalNumerator w % oddEndpointModulus w
        = (((canonicalNumerator w : ℕ) : ZMod (oddEndpointModulus w))).val := by
            simp only [ZMod.val_natCast]
    _ = (((2 ^ twoSteps w : ℕ) : ZMod (oddEndpointModulus w))).val := hval
    _ = (2 ^ twoSteps w) % oddEndpointModulus w := by
      simp only [ZMod.val_natCast]
    _ = 2 ^ twoSteps w := Nat.mod_eq_of_lt hpowlt

/-- canonical numerator は `2^H * odd` と exact に因数分解される。 -/
theorem canonicalNumerator_eq_twoPow_mul_odd (w : Word) :
    ∃ k : ℕ,
      canonicalNumerator w = 2 ^ twoSteps w * (2 * k + 1) := by
  have hdecomp :=
    Nat.mod_add_div (canonicalNumerator w) (oddEndpointModulus w)
  rw [canonicalNumerator_mod_modulus] at hdecomp
  refine ⟨canonicalNumerator w / oddEndpointModulus w, ?_⟩
  calc
    canonicalNumerator w
        = 2 ^ twoSteps w +
            oddEndpointModulus w *
              (canonicalNumerator w / oddEndpointModulus w) := by
                exact hdecomp.symm
    _ = 2 ^ twoSteps w *
          (2 * (canonicalNumerator w / oddEndpointModulus w) + 1) := by
            unfold oddEndpointModulus Arithmetic.twoPowModulus
            rw [pow_succ]
            ring

/-- canonical endpoint `E = (3^p R + A) / 2^H`。 -/
def canonicalEnd (w : Word) : ℕ :=
  canonicalNumerator w / 2 ^ twoSteps w

/-- canonical endpoint は numerator を exact に割り切る。 -/
theorem twoPow_mul_canonicalEnd (w : Word) :
    2 ^ twoSteps w * canonicalEnd w = canonicalNumerator w := by
  rcases canonicalNumerator_eq_twoPow_mul_odd w with ⟨k, hk⟩
  simp [canonicalEnd, hk]

/-- canonical endpoint は奇数。 -/
theorem canonicalEnd_odd (w : Word) : Odd (canonicalEnd w) := by
  rcases canonicalNumerator_eq_twoPow_mul_odd w with ⟨k, hk⟩
  have hEnd : canonicalEnd w = 2 * k + 1 := by
    simp [canonicalEnd, hk]
  exact ⟨k, hEnd⟩

/-- canonical start/end は endpoint equation を満たす。 -/
theorem canonical_endpointEquation (w : Word) :
    w.EndpointEquation (canonicalStart w) (canonicalEnd w) := by
  apply (endpointEquation_iff w (canonicalStart w) (canonicalEnd w)).2
  rw [twoPow_mul_canonicalEnd]
  rfl

/-- canonical drift `Q = E - R`。符号を失わないため整数値とする。 -/
def canonicalGap (w : Word) : ℤ :=
  (canonicalEnd w : ℤ) - (canonicalStart w : ℤ)

/-- 基本恒等式 `2^H E = 3^p R + A`。 -/
theorem req_equation (w : Word) :
    2 ^ twoSteps w * canonicalEnd w =
      3 ^ oddSteps w * canonicalStart w + affineConst w := by
  exact (endpointEquation_iff w (canonicalStart w) (canonicalEnd w)).1
    (canonical_endpointEquation w)

/-- `A = (2^H-3^p)R + 2^H Q`。 -/
theorem affineConst_eq_gap_start_add_twoPow_gap (w : Word) :
    (affineConst w : ℤ) =
      signedScaleGap w * (canonicalStart w : ℤ) +
        (2 ^ twoSteps w : ℤ) * canonicalGap w := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (req_equation w)
  push_cast at h
  calc
    (affineConst w : ℤ)
        = (2 ^ twoSteps w : ℤ) * (canonicalEnd w : ℤ) -
            (3 ^ oddSteps w : ℤ) * (canonicalStart w : ℤ) := by
              linarith
    _ = signedScaleGap w * (canonicalStart w : ℤ) +
          (2 ^ twoSteps w : ℤ) * canonicalGap w := by
            simp [signedScaleGap_eq, canonicalGap]
            ring

/-- `A = (2^H-3^p)E + 3^p Q`。 -/
theorem affineConst_eq_gap_end_add_threePow_gap (w : Word) :
    (affineConst w : ℤ) =
      signedScaleGap w * (canonicalEnd w : ℤ) +
        (3 ^ oddSteps w : ℤ) * canonicalGap w := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (req_equation w)
  push_cast at h
  calc
    (affineConst w : ℤ)
        = (2 ^ twoSteps w : ℤ) * (canonicalEnd w : ℤ) -
            (3 ^ oddSteps w : ℤ) * (canonicalStart w : ℤ) := by
              linarith
    _ = signedScaleGap w * (canonicalEnd w : ℤ) +
          (3 ^ oddSteps w : ℤ) * canonicalGap w := by
            simp [signedScaleGap_eq, canonicalGap]
            ring

end Word
end Collatz3
