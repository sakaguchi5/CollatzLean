import CollatzLean.Collatz3.CSTMicro.Affine
import Mathlib.Data.ZMod.Basic

/-!
# Collatz3 CSTMicro: parity-cylinder residue

whole affine equation

  3^p x + B(v) ≡ 0 mod 2^H

から standard parity cylinder の一意な start class を作る。
modulus は `2^H`。

これは Collatz3 の odd-endpoint class `mod 2^(H+1)` より一段粗く、
一般 finite coefficient stopping time に必要な standard parity class である。
-/

namespace Collatz3
namespace CSTMicro

/-- standard parity cylinder modulus `2^H`。 -/
def parityModulus (v : ParityWord) : ℕ :=
  2 ^ v.length

@[simp] theorem parityModulus_pos (v : ParityWord) :
    0 < parityModulus v := by
  simp [parityModulus]

/-- `3^p` と parity modulus `2^H` は互いに素。 -/
theorem coprime_threePow_parityModulus (v : ParityWord) :
    Nat.Coprime (3 ^ oddCount v) (parityModulus v) := by
  exact
    ((by decide : Nat.Coprime 3 2).pow_left (oddCount v)).pow_right
      v.length

/-- modulus 上の leading coefficient unit。 -/
def parityLeadingUnit
    (v : ParityWord) :
    (ZMod (parityModulus v))ˣ :=
  ZMod.unitOfCoprime
    (3 ^ oddCount v)
    (coprime_threePow_parityModulus v)

/-- affine congruenceを解く一意な parity start class。 -/
def parityStartClass
    (v : ParityWord) :
    ZMod (parityModulus v) :=
  (↑((parityLeadingUnit v)⁻¹) : ZMod (parityModulus v)) *
    (0 - ((affineConst v : ℕ) : ZMod (parityModulus v)))

/-- parity start class は affine congruenceを満たす。 -/
theorem parityStartClass_spec (v : ParityWord) :
    (((3 ^ oddCount v : ℕ) : ZMod (parityModulus v)) *
        parityStartClass v) +
      ((affineConst v : ℕ) : ZMod (parityModulus v)) = 0 := by
  unfold parityStartClass
  have hleading :
      (((3 ^ oddCount v : ℕ) : ZMod (parityModulus v))) =
        (↑(parityLeadingUnit v) : ZMod (parityModulus v)) := by
    simp [parityLeadingUnit]
  rw [hleading]
  simp [← mul_assoc]

/-- affine congruenceの解は parity start class に一意。 -/
theorem parityStartClass_unique
    (v : ParityWord)
    (x : ZMod (parityModulus v))
    (hx :
      (((3 ^ oddCount v : ℕ) : ZMod (parityModulus v)) * x) +
        ((affineConst v : ℕ) : ZMod (parityModulus v)) = 0) :
    x = parityStartClass v := by
  have hm :
      (↑(parityLeadingUnit v) : ZMod (parityModulus v)) * x =
        -((affineConst v : ℕ) : ZMod (parityModulus v)) := by
    rw [parityLeadingUnit]
    exact eq_neg_of_add_eq_zero_left hx
  calc
    x =
        (↑((parityLeadingUnit v)⁻¹) : ZMod (parityModulus v)) *
          ((↑(parityLeadingUnit v) : ZMod (parityModulus v)) * x) := by
            simp
    _ =
        (↑((parityLeadingUnit v)⁻¹) : ZMod (parityModulus v)) *
          (0 - ((affineConst v : ℕ) : ZMod (parityModulus v))) := by
            rw [hm]
            simp
    _ = parityStartClass v := rfl

/-- parity cylinder の最小非負代表。 -/
def leastRepresentative (v : ParityWord) : ℕ :=
  (parityStartClass v).val

/-- 最小代表は modulus より小さい。 -/
theorem leastRepresentative_lt_modulus (v : ParityWord) :
    leastRepresentative v < parityModulus v := by
  have : NeZero (parityModulus v) :=
    ⟨by simp [parityModulus]⟩
  exact ZMod.val_lt (parityStartClass v)

/-- affine realization の start は一意な parity start class に属する。 -/
theorem AffineRealizes.start_has_parityStartClass
    {v : ParityWord} {x y : ℕ}
    (h : AffineRealizes v x y) :
    ((x : ℕ) : ZMod (parityModulus v)) = parityStartClass v := by
  apply parityStartClass_unique
  have hEq :
      2 ^ v.length * y =
        3 ^ oddCount v * x + affineConst v := h
  have hcast :=
    congrArg
      (fun n : ℕ => (n : ZMod (parityModulus v)))
      hEq
  calc
    (((3 ^ oddCount v : ℕ) : ZMod (parityModulus v)) *
          ((x : ℕ) : ZMod (parityModulus v))) +
        ((affineConst v : ℕ) : ZMod (parityModulus v))
        = (((2 ^ v.length * y : ℕ) : ZMod (parityModulus v))) := by
            simpa [AffineRealizes] using hcast.symm
    _ = 0 := by
      change ((2 ^ v.length * y : ℕ) : ZMod (2 ^ v.length)) = 0
      simp

/-- affine realization start の ordinary remainder は最小代表に一致。 -/
theorem AffineRealizes.start_mod_eq_leastRepresentative
    {v : ParityWord} {x y : ℕ}
    (h : AffineRealizes v x y) :
    x % parityModulus v = leastRepresentative v := by
  have hc := h.start_has_parityStartClass
  have hv := congrArg ZMod.val hc
  simpa [leastRepresentative, ZMod.val_natCast] using hv

/--
同じ parity cylinder の任意の affine realization start は
`R + 2^H k` の形に一意に入る。
-/
theorem AffineRealizes.exists_start_eq_leastRepresentative_add_modulus_mul
    {v : ParityWord} {x y : ℕ}
    (h : AffineRealizes v x y) :
    ∃ k : ℕ,
      x = leastRepresentative v + parityModulus v * k := by
  refine ⟨x / parityModulus v, ?_⟩
  have hmod := h.start_mod_eq_leastRepresentative
  have hdecomp := Nat.mod_add_div x (parityModulus v)
  rw [hmod] at hdecomp
  exact hdecomp.symm

/-- 最小代表は同じ parity cylinder のすべての natural start 以下。 -/
theorem AffineRealizes.leastRepresentative_le_start
    {v : ParityWord} {x y : ℕ}
    (h : AffineRealizes v x y) :
    leastRepresentative v ≤ x := by
  rcases h.exists_start_eq_leastRepresentative_add_modulus_mul with ⟨k, rfl⟩
  omega

end CSTMicro
end Collatz3
