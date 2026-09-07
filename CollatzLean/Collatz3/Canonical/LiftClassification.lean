import CollatzLean.Collatz3.Canonical.REQ
import Mathlib.Tactic.Ring

/-!
# Collatz3: 奇数 endpoint affine solution の完全分類

同じ word に対する全 odd-endpoint affine solution は、canonical pair `(R,E)` から
一本の格子直線として得られる。この分類は actual Collatz semantics を使わない。
-/

namespace Collatz3
namespace Word

/-- odd-endpoint affine solution の start は `R + 2^(H+1) k`。 -/
theorem exists_start_lift_of_endpointEquation
    {w : Word} {x y : ℕ}
    (h : w.EndpointEquation x y)
    (hy : Odd y) :
    ∃ k : ℕ,
      x = canonicalStart w + oddEndpointModulus w * k := by
  have hmod := h.start_mod_eq_canonicalStart hy
  have hdecomp := Nat.mod_add_div x (oddEndpointModulus w)
  rw [hmod] at hdecomp
  exact ⟨x / oddEndpointModulus w, hdecomp.symm⟩

/-- odd-endpoint affine solution の完全 lift 分類。 -/
theorem endpointEquation_and_odd_iff_exists_lift
    (w : Word) (x y : ℕ) :
    w.EndpointEquation x y ∧ Odd y ↔
      ∃ k : ℕ,
        x = canonicalStart w + oddEndpointModulus w * k ∧
        y = canonicalEnd w + 2 * (3 ^ oddSteps w) * k := by
  constructor
  · rintro ⟨hEq, hy⟩
    rcases exists_start_lift_of_endpointEquation hEq hy with ⟨k, hx⟩
    refine ⟨k, hx, ?_⟩
    have hMain := (endpointEquation_iff w x y).1 hEq
    have hCan := req_equation w
    have hyMul :
        2 ^ twoSteps w * y =
          2 ^ twoSteps w *
            (canonicalEnd w + 2 * (3 ^ oddSteps w) * k) := by
      calc
        2 ^ twoSteps w * y
            = 3 ^ oddSteps w * x + affineConst w := hMain
        _ = 3 ^ oddSteps w *
              (canonicalStart w + oddEndpointModulus w * k) +
              affineConst w := by rw [hx]
        _ = 2 ^ twoSteps w * canonicalEnd w +
              3 ^ oddSteps w * oddEndpointModulus w * k := by
                rw [hCan]
                ring
        _ = 2 ^ twoSteps w *
              (canonicalEnd w + 2 * (3 ^ oddSteps w) * k) := by
                unfold oddEndpointModulus Arithmetic.twoPowModulus
                rw [pow_succ]
                ring
    exact Nat.mul_left_cancel (Nat.pow_pos (by omega : 0 < (2 : ℕ))) hyMul
  · rintro ⟨k, hx, hy⟩
    constructor
    · apply (endpointEquation_iff w x y).2
      rw [hx, hy]
      have hCan := req_equation w
      calc
        2 ^ twoSteps w *
            (canonicalEnd w + 2 * (3 ^ oddSteps w) * k)
            = 2 ^ twoSteps w * canonicalEnd w +
                2 * (2 ^ twoSteps w) * (3 ^ oddSteps w) * k := by ring
        _ = 3 ^ oddSteps w * canonicalStart w + affineConst w +
                2 * (2 ^ twoSteps w) * (3 ^ oddSteps w) * k := by rw [hCan]
        _ = 3 ^ oddSteps w *
              (canonicalStart w + oddEndpointModulus w * k) +
              affineConst w := by
                unfold oddEndpointModulus Arithmetic.twoPowModulus
                rw [pow_succ]
                ring
    · rcases canonicalEnd_odd w with ⟨t, ht⟩
      refine ⟨t + (3 ^ oddSteps w) * k, ?_⟩
      rw [hy, ht]
      ring

/-- lift `k` における endpoint-start 差。 -/
theorem lift_gap_formula
    {w : Word} {x y k : ℕ}
    (hx : x = canonicalStart w + oddEndpointModulus w * k)
    (hy : y = canonicalEnd w + 2 * (3 ^ oddSteps w) * k) :
    (y : ℤ) - (x : ℤ) =
      canonicalGap w - 2 * (k : ℤ) * signedScaleGap w := by
  rw [hx, hy]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, oddEndpointModulus,
      Arithmetic.twoPowModulus,canonicalGap, signedScaleGap_eq]
  rw [pow_succ]
  ring

end Word
end Collatz3
