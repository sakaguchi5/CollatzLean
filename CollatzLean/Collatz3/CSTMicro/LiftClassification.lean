import CollatzLean.Collatz3.CSTMicro.Realization
import CollatzLean.Collatz3.Arithmetic.Pow23
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTMicro: standard parity cylinder の lift classification

一つの standard parity word `v` に対して、すべての affine realization は

  x = R₀ + 2^H k
  y = Y₀ + 3^p k

の形に exact に分類される。

ここで `R₀ = leastRepresentative v`、`Y₀ = canonicalEndpoint v`。
odd-endpoint canonical class `mod 2^(H+1)` とはまだ接続しない。
-/

namespace Collatz3
namespace CSTMicro

/-- 任意の affine realization は canonical pair の一意な上向き lift に入る。 -/
theorem AffineRealizes.exists_lift
    {v : ParityWord} {x y : ℕ}
    (h : AffineRealizes v x y) :
    ∃ k : ℕ,
      x = leastRepresentative v + parityModulus v * k ∧
      y = canonicalEndpoint v + 3 ^ oddCount v * k := by
  rcases h.exists_start_eq_leastRepresentative_add_modulus_mul with
    ⟨k, hx⟩
  refine ⟨k, hx, ?_⟩
  have hCanonical := canonicalEndpoint_affine v
  unfold AffineRealizes at h hCanonical
  rw [parityModulus] at hx
  rw [hx] at h
  have hEq :
      2 ^ v.length * y =
        2 ^ v.length *
          (canonicalEndpoint v + 3 ^ oddCount v * k) := by
    calc
      2 ^ v.length * y
          = 3 ^ oddCount v *
              (leastRepresentative v + 2 ^ v.length * k) +
                affineConst v := h
      _ =
          (3 ^ oddCount v * leastRepresentative v + affineConst v) +
            2 ^ v.length * (3 ^ oddCount v * k) := by ring
      _ =
          2 ^ v.length * canonicalEndpoint v +
            2 ^ v.length * (3 ^ oddCount v * k) := by
              rw [hCanonical]
      _ =
          2 ^ v.length *
            (canonicalEndpoint v + 3 ^ oddCount v * k) := by ring
  exact Nat.mul_left_cancel (Arithmetic.twoPow_pos v.length) hEq

/-- canonical pair の任意の lift は affine realization。 -/
theorem affine_lift
    (v : ParityWord)
    (k : ℕ) :
    AffineRealizes v
      (leastRepresentative v + parityModulus v * k)
      (canonicalEndpoint v + 3 ^ oddCount v * k) := by
  have hCanonical := canonicalEndpoint_affine v
  unfold AffineRealizes at hCanonical ⊢
  unfold parityModulus
  calc
    2 ^ v.length *
        (canonicalEndpoint v + 3 ^ oddCount v * k)
        = 2 ^ v.length * canonicalEndpoint v +
            2 ^ v.length * (3 ^ oddCount v * k) := by ring
    _ = (3 ^ oddCount v * leastRepresentative v + affineConst v) +
          2 ^ v.length * (3 ^ oddCount v * k) := by rw [hCanonical]
    _ = 3 ^ oddCount v *
          (leastRepresentative v + 2 ^ v.length * k) +
            affineConst v := by ring

/-- canonical pair の任意の lift は exact parity trace も実現する。 -/
theorem trace_lift
    (v : ParityWord)
    (k : ℕ) :
    TraceRealizes v
      (leastRepresentative v + parityModulus v * k)
      (canonicalEndpoint v + 3 ^ oddCount v * k) :=
  (affine_lift v k).trace

/-- exact parity trace も同じ lift classification に従う。 -/
theorem TraceRealizes.exists_lift
    {v : ParityWord} {x y : ℕ}
    (h : TraceRealizes v x y) :
    ∃ k : ℕ,
      x = leastRepresentative v + parityModulus v * k ∧
      y = canonicalEndpoint v + 3 ^ oddCount v * k :=
  h.affine.exists_lift

end CSTMicro
end Collatz3
