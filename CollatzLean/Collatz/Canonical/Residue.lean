import CollatzLean.Collatz.Word.Affine
import Mathlib.Data.ZMod.Basic

/-!
# canonical residue

有限語のcanonical剰余をpure finite word層の上に置く。
-/

namespace Collatz
namespace Word

/-- canonical residueの法。 -/
def residueModulus (w : Collatz.Word) : ℕ := 2 ^ (w.twoSteps + 1)

/-- `3^p` とcanonical法は互いに素。 -/
theorem coprime_three_pow_residueModulus (w : Collatz.Word) :
    Nat.Coprime (3 ^ w.oddSteps) w.residueModulus := by
  exact ((by decide : Nat.Coprime 3 2).pow_left w.oddSteps).pow_right (w.twoSteps + 1)

/-- canonical法における`3^p`の単元。 -/
def leadingUnit (w : Collatz.Word) : (ZMod w.residueModulus)ˣ :=
  ZMod.unitOfCoprime (3 ^ w.oddSteps) (coprime_three_pow_residueModulus w)

/-- 語を正確に実現する開始値のcanonical剰余類。 -/
def canonicalClass (w : Collatz.Word) : ZMod w.residueModulus :=
  (↑((w.leadingUnit)⁻¹) : ZMod w.residueModulus) *
    (((2 ^ w.twoSteps : ℕ) : ZMod w.residueModulus) -
      ((w.affineConst : ℕ) : ZMod w.residueModulus))

/-- canonical剰余類の最小非負代表。 -/
def canonicalStart (w : Collatz.Word) : ℕ := w.canonicalClass.val

/-- canonical開始値は法より小さい。 -/
theorem canonicalStart_lt_modulus (w : Collatz.Word) :
    w.canonicalStart < w.residueModulus := by
  haveI : NeZero w.residueModulus := ⟨by simp [residueModulus]⟩
  exact ZMod.val_lt w.canonicalClass

/-- canonical方程式。 -/
theorem canonicalClass_spec (w : Collatz.Word) :
    (((3 ^ w.oddSteps : ℕ) : ZMod w.residueModulus) * w.canonicalClass) +
      ((w.affineConst : ℕ) : ZMod w.residueModulus) =
      ((2 ^ w.twoSteps : ℕ) : ZMod w.residueModulus) := by
  unfold canonicalClass
  have hleading :
      (((3 ^ w.oddSteps : ℕ) : ZMod w.residueModulus)) =
        (↑w.leadingUnit : ZMod w.residueModulus) := by
    simp [leadingUnit]
  rw [hleading]
  simp [← mul_assoc]

/-- canonical方程式の解は一意。 -/
theorem canonicalClass_unique
    (w : Collatz.Word)
    (x : ZMod w.residueModulus)
    (hx : (((3 ^ w.oddSteps : ℕ) : ZMod w.residueModulus) * x) +
      ((w.affineConst : ℕ) : ZMod w.residueModulus) =
      ((2 ^ w.twoSteps : ℕ) : ZMod w.residueModulus)) :
    x = w.canonicalClass := by
  have hm : (↑w.leadingUnit : ZMod w.residueModulus) * x =
      (((2 ^ w.twoSteps : ℕ) : ZMod w.residueModulus) -
        ((w.affineConst : ℕ) : ZMod w.residueModulus)) := by
    simpa [leadingUnit, ZMod.coe_unitOfCoprime, eq_sub_iff_add_eq] using hx
  calc
    x = (↑((w.leadingUnit)⁻¹) : ZMod w.residueModulus) *
          ((↑w.leadingUnit : ZMod w.residueModulus) * x) := by simp
    _ = (↑((w.leadingUnit)⁻¹) : ZMod w.residueModulus) *
          (((2 ^ w.twoSteps : ℕ) : ZMod w.residueModulus) -
            ((w.affineConst : ℕ) : ZMod w.residueModulus)) := by rw [hm]
    _ = w.canonicalClass := rfl

/-- 奇数終点を持つ実現の開始値はcanonical剰余類に属する。 -/
theorem Realizes.start_has_canonical_class
    {w : Collatz.Word} {x y : ℕ}
    (h : w.Realizes x y) (hy : Odd y) :
    ((x : ℕ) : ZMod w.residueModulus) = w.canonicalClass := by
  apply canonicalClass_unique
  unfold Realizes at h
  have hcast := congrArg (fun n : ℕ => (n : ZMod w.residueModulus)) h
  rcases hy with ⟨k, rfl⟩
  have hid :
      2 ^ w.twoSteps * (2 * k + 1) =
        2 ^ w.twoSteps + w.residueModulus * k := by
    unfold residueModulus
    rw [pow_succ]
    ring
  calc
    (((3 ^ w.oddSteps : ℕ) : ZMod w.residueModulus) *
          ((x : ℕ) : ZMod w.residueModulus)) +
        ((w.affineConst : ℕ) : ZMod w.residueModulus)
        = (((2 ^ w.twoSteps * (2 * k + 1) : ℕ) : ZMod w.residueModulus)) := by
            simpa using hcast.symm
    _ = (((2 ^ w.twoSteps + w.residueModulus * k : ℕ) : ZMod w.residueModulus)) := by rw [hid]
    _ = ((2 ^ w.twoSteps : ℕ) : ZMod w.residueModulus) := by simp

/-- 小さい自然数代表ならcanonical startそのもの。 -/
theorem Realizes.eq_canonicalStart_of_lt_modulus
    {w : Collatz.Word} {x y : ℕ}
    (h : w.Realizes x y) (hy : Odd y)
    (hx : x < w.residueModulus) :
    x = w.canonicalStart := by
  have hc := h.start_has_canonical_class hy
  have hv := congrArg ZMod.val hc
  simpa [canonicalStart, ZMod.val_natCast, Nat.mod_eq_of_lt hx] using hv

end Word
end Collatz
