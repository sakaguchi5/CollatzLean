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

/--
endpoint equation を満たし、start が canonical lift `k` にあるなら、
endpoint も同じ `k` の canonical lift にある。

start 側の増分 `2^(H+1) * k` は、
endpoint 側では `2 * 3^p * k` に移る。
-/
theorem endpoint_eq_canonicalEnd_add_of_endpointEquation_of_start_lift
    {w : Word} {x y k : ℕ}
    (hEq : w.EndpointEquation x y)
    (hx :
      x = canonicalStart w + oddEndpointModulus w * k) :
    y = canonicalEnd w + 2 * (3 ^ oddSteps w) * k := by
  have hMain := (endpointEquation_iff w x y).1 hEq
  have hCan := req_equation w
  have hyMul :
      2 ^ twoSteps w * y =
        2 ^ twoSteps w *
          (canonicalEnd w + 2 * (3 ^ oddSteps w) * k) := by
    calc
      2 ^ twoSteps w * y
          = 3 ^ oddSteps w * x + affineConst w := hMain
      _ =
          3 ^ oddSteps w *
              (canonicalStart w + oddEndpointModulus w * k) +
            affineConst w := by
              rw [hx]
      _ =
          2 ^ twoSteps w * canonicalEnd w +
            3 ^ oddSteps w * oddEndpointModulus w * k := by
              rw [hCan]
              ring
      _ =
          2 ^ twoSteps w *
            (canonicalEnd w + 2 * (3 ^ oddSteps w) * k) := by
              rw [oddEndpointModulus_eq]
              rw [pow_succ]
              ring
  exact
    Nat.mul_left_cancel
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
      hyMul

/--
odd-endpoint affine solution は、
同じ lift index `k` を使う canonical start/end の組として表される。
-/
theorem exists_canonicalLift_of_endpointEquation
    {w : Word} {x y : ℕ}
    (hEq : w.EndpointEquation x y)
    (hy : Odd y) :
    ∃ k : ℕ,
      x = canonicalStart w + oddEndpointModulus w * k ∧
      y = canonicalEnd w + 2 * (3 ^ oddSteps w) * k := by
  rcases
      exists_start_lift_of_endpointEquation hEq hy
      with ⟨k, hx⟩
  refine ⟨k, hx, ?_⟩
  exact
    endpoint_eq_canonicalEnd_add_of_endpointEquation_of_start_lift
      hEq
      hx

/--
canonical lift の start/end 座標を持つ組は
必ず endpoint equation を満たす。
-/
theorem endpointEquation_of_canonicalLift
    {w : Word} {x y k : ℕ}
    (hx :
      x = canonicalStart w + oddEndpointModulus w * k)
    (hy :
      y = canonicalEnd w + 2 * (3 ^ oddSteps w) * k) :
    w.EndpointEquation x y := by
  apply (endpointEquation_iff w x y).2
  rw [hx, hy]
  have hCan := req_equation w
  calc
    2 ^ twoSteps w *
        (canonicalEnd w + 2 * (3 ^ oddSteps w) * k)
        =
        2 ^ twoSteps w * canonicalEnd w +
          2 * (2 ^ twoSteps w) * (3 ^ oddSteps w) * k := by
            ring
    _ =
        3 ^ oddSteps w * canonicalStart w +
          affineConst w +
          2 * (2 ^ twoSteps w) * (3 ^ oddSteps w) * k := by
            rw [hCan]
    _ =
        3 ^ oddSteps w *
            (canonicalStart w + oddEndpointModulus w * k) +
          affineConst w := by
            rw [oddEndpointModulus_eq]
            rw [pow_succ]
            ring

/--
canonical endpoint の lift
`Y + 2 * 3^p * k`
は常に奇数。
-/
theorem odd_of_eq_canonicalEnd_add
    {w : Word} {y k : ℕ}
    (hy :
      y = canonicalEnd w + 2 * (3 ^ oddSteps w) * k) :
    Odd y := by
  rcases canonicalEnd_odd w with ⟨t, ht⟩
  refine ⟨t + (3 ^ oddSteps w) * k, ?_⟩
  rw [hy, ht]
  ring

/--
canonical lift の start/end 座標を持つ組は
endpoint equation を満たし、endpoint は奇数。
-/
theorem endpointEquation_and_odd_of_canonicalLift
    {w : Word} {x y k : ℕ}
    (hx :
      x = canonicalStart w + oddEndpointModulus w * k)
    (hy :
      y = canonicalEnd w + 2 * (3 ^ oddSteps w) * k) :
    w.EndpointEquation x y ∧ Odd y := by
  exact
    ⟨endpointEquation_of_canonicalLift hx hy,
      odd_of_eq_canonicalEnd_add hy⟩

/--
odd-endpoint affine solution の完全 lift 分類。

すべての解は一意な canonical 格子族

`x = R + 2^(H+1) k`

`y = Y + 2 * 3^p k`

の上にある。
-/
theorem endpointEquation_and_odd_iff_exists_lift
    (w : Word) (x y : ℕ) :
    w.EndpointEquation x y ∧ Odd y ↔
      ∃ k : ℕ,
        x = canonicalStart w + oddEndpointModulus w * k ∧
        y = canonicalEnd w + 2 * (3 ^ oddSteps w) * k := by
  constructor
  · rintro ⟨hEq, hy⟩
    exact exists_canonicalLift_of_endpointEquation hEq hy
  · rintro ⟨k, hx, hy⟩
    exact endpointEquation_and_odd_of_canonicalLift hx hy

/-- lift `k` における endpoint-start 差。 -/
theorem lift_gap_formula
    {w : Word} {x y k : ℕ}
    (hx : x = canonicalStart w + oddEndpointModulus w * k)
    (hy : y = canonicalEnd w + 2 * (3 ^ oddSteps w) * k) :
    (y : ℤ) - (x : ℤ) =
      canonicalGap w - 2 * (k : ℤ) * signedScaleGap w := by
  rw [hx, hy]
  have hGap :
      canonicalGap w =
        (canonicalEnd w : ℤ) - (canonicalStart w : ℤ) := by
    rfl
  rw [hGap]
  rw [signedScaleGap_eq]
  rw [oddEndpointModulus_eq]
  simp only [
    Nat.cast_add,
    Nat.cast_mul,
    Nat.cast_ofNat,
    Nat.cast_pow
  ]
  rw [pow_succ]
  ring


end Word
end Collatz3
