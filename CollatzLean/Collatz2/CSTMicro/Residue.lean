import CollatzLean.Collatz2.CSTMicro.Affine
import Mathlib.Data.ZMod.Basic

/-!
# General CST: parity-cylinder residue

同じ binary path を実現する start の 2-adic class を
whole affine equation から抽出する。

modulus は `2^length`。
これは accelerated odd-endpoint cylinder の `2^(H+1)` より
一般 CST にちょうど必要な coarse parity cylinder である。
-/

namespace Collatz2
namespace CSTMicro

/-- standard parity cylinder modulus。 -/
def parityModulus (v : ParityWord) : ℕ :=
  2 ^ v.length

@[simp] theorem parityModulus_pos (v : ParityWord) :
    0 < parityModulus v := by
  simp [parityModulus]

/-- `3^(oddCount)` と parity modulus は互いに素。 -/
theorem coprime_threePow_parityModulus (v : ParityWord) :
    Nat.Coprime (3 ^ oddCount v) (parityModulus v) := by
  exact
    ((by decide : Nat.Coprime 3 2).pow_left (oddCount v)).pow_right
      v.length

/-- modulus における leading coefficient の unit。 -/
def parityLeadingUnit
    (v : ParityWord) :
    (ZMod (parityModulus v))ˣ :=
  ZMod.unitOfCoprime
    (3 ^ oddCount v)
    (coprime_threePow_parityModulus v)

/--
whole affine numerator

  3^m x + B(P) ≡ 0 mod 2^k

を解く一意な parity-cylinder class。
-/
def parityStartClass
    (v : ParityWord) :
    ZMod (parityModulus v) :=
  (↑((parityLeadingUnit v)⁻¹) : ZMod (parityModulus v)) *
    (0 - ((affineConst v : ℕ) : ZMod (parityModulus v)))

theorem parityStartClass_spec (v : ParityWord) :
    (((3 ^ oddCount v : ℕ) : ZMod (parityModulus v)) *
        parityStartClass v) +
      ((affineConst v : ℕ) : ZMod (parityModulus v)) =
      0 := by
  unfold parityStartClass
  have hleading :
      (((3 ^ oddCount v : ℕ) : ZMod (parityModulus v))) =
        (↑(parityLeadingUnit v) : ZMod (parityModulus v)) := by
    simp [parityLeadingUnit]
  rw [hleading]
  simp [← mul_assoc]

theorem parityStartClass_unique
    (v : ParityWord)
    (x : ZMod (parityModulus v))
    (hx :
      (((3 ^ oddCount v : ℕ) : ZMod (parityModulus v)) * x) +
        ((affineConst v : ℕ) : ZMod (parityModulus v)) =
        0) :
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

/-- parity cylinder の最小非負代表 `R(P)`。 -/
def leastRepresentative
    (v : ParityWord) : ℕ :=
  (parityStartClass v).val

theorem leastRepresentative_lt_modulus
    (v : ParityWord) :
    leastRepresentative v < parityModulus v := by
  have : NeZero (parityModulus v) :=
    ⟨by simp [parityModulus]⟩
  exact ZMod.val_lt (parityStartClass v)

/--
whole affine realization の start は parity cylinder に属する。
-/
theorem AffineRealizes.start_has_parityStartClass
    {v : ParityWord} {x y : ℕ}
    (h : AffineRealizes v x y) :
    ((x : ℕ) : ZMod (parityModulus v)) =
      parityStartClass v := by
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
        =
        (((2 ^ v.length * y : ℕ) :
          ZMod (parityModulus v))) := by
          simpa [AffineRealizes] using hcast.symm
    _ = 0 := by
      change ((2 ^ v.length * y : ℕ) : ZMod (2 ^ v.length)) = 0
      simp

/-- affine realization start の ordinary remainder は `R(P)`。 -/
theorem AffineRealizes.start_mod_eq_leastRepresentative
    {v : ParityWord} {x y : ℕ}
    (h : AffineRealizes v x y) :
    x % parityModulus v = leastRepresentative v := by
  have hc := h.start_has_parityStartClass
  have hv := congrArg ZMod.val hc
  simpa [leastRepresentative, ZMod.val_natCast] using hv

/--
`R(P)` は同じ parity cylinder のすべての natural start 以下。
-/
theorem AffineRealizes.leastRepresentative_le_start
    {v : ParityWord} {x y : ℕ}
    (h : AffineRealizes v x y) :
    leastRepresentative v ≤ x := by
  have hmod := h.start_mod_eq_leastRepresentative
  have hdecomp := Nat.mod_add_div x (parityModulus v)
  rw [hmod] at hdecomp
  omega

end CSTMicro
end Collatz2
