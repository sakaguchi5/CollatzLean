import CollatzLean.CollatzFirstLayer.Terminal
import Mathlib.Data.ZMod.Basic

/-!
# canonical residue

語の最終商が奇数になるための開始剰余を、`ZMod (2^(H+1))` 上で一意に定義する。
3の冪は2の冪と互いに素なので単元になる。
-/

namespace CollatzFirstLayer
namespace ExpWord

/-- canonical residueを取る法。 -/
def residueModulus (w : ExpWord) : ℕ := 2 ^ (twoSteps w + 1)

/-- `3^p` とcanonical法は互いに素である。 -/
lemma coprime_three_pow_residueModulus (w : ExpWord) :
    Nat.Coprime (3 ^ oddSteps w) (residueModulus w) := by
  have h32 : Nat.Coprime 3 2 := by decide
  exact (h32.pow_left (oddSteps w)).pow_right (twoSteps w + 1)

/-- canonical法における`3^p`の単元。 -/
def leadingUnit (w : ExpWord) : (ZMod (residueModulus w))ˣ :=
  ZMod.unitOfCoprime (3 ^ oddSteps w) (coprime_three_pow_residueModulus w)

/-- 語を正確に実現する開始値のcanonical剰余類。 -/
def canonicalClass (w : ExpWord) : ZMod (residueModulus w) :=
  (↑((leadingUnit w)⁻¹) : ZMod (residueModulus w)) *
    (((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) -
      ((affineConst w : ℕ) : ZMod (residueModulus w)))

/-- canonical剰余類の最小非負代表。 -/
def canonicalStart (w : ExpWord) : ℕ :=
  (canonicalClass w).val

/-- canonical開始値は法より小さい。 -/
lemma canonicalStart_lt_modulus (w : ExpWord) :
    canonicalStart w < residueModulus w := by
  haveI : NeZero (residueModulus w) := ⟨by simp [residueModulus]⟩
  exact ZMod.val_lt (canonicalClass w)

/-- canonical開始値を法へ戻すとcanonical剰余類になる。 -/
theorem canonicalStart_cast (w : ExpWord) :
    ((canonicalStart w : ℕ) : ZMod (residueModulus w)) = canonicalClass w := by
  haveI : NeZero (residueModulus w) := ⟨by simp [residueModulus]⟩
  exact ZMod.natCast_zmod_val (canonicalClass w)

theorem canonicalClass_spec (w : ExpWord) :
    (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w)) * canonicalClass w) +
      ((affineConst w : ℕ) : ZMod (residueModulus w)) =
      ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) := by
  unfold canonicalClass
  have hleading :
      (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w))) =
        (↑(leadingUnit w) : ZMod (residueModulus w)) := by
    simp [leadingUnit]
  rw [hleading]
  simp [← mul_assoc]

/-- canonical方程式を満たす剰余類は一意である。 -/
theorem canonicalClass_unique (w : ExpWord)
    (x : ZMod (residueModulus w))
    (hx : (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w)) * x) +
      ((affineConst w : ℕ) : ZMod (residueModulus w)) =
      ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w))) :
    x = canonicalClass w := by
  have hm : (↑(leadingUnit w) : ZMod (residueModulus w)) * x =
      (((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) -
        ((affineConst w : ℕ) : ZMod (residueModulus w))) := by
    simpa [leadingUnit, ZMod.coe_unitOfCoprime, eq_sub_iff_add_eq] using hx
  calc
    x = (↑((leadingUnit w)⁻¹) : ZMod (residueModulus w)) *
          ((↑(leadingUnit w) : ZMod (residueModulus w)) * x) := by simp
    _ = (↑((leadingUnit w)⁻¹) : ZMod (residueModulus w)) *
          (((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) -
            ((affineConst w : ℕ) : ZMod (residueModulus w))) := by rw [hm]
    _ = canonicalClass w := rfl

/--
自然数上のアフィン実現で終点が奇数なら、開始値はcanonical方程式を満たす。
-/
theorem realization_canonical_equation
    {w : ExpWord} {x y : ℕ}
    (h : Realizes w x y) (hy : Odd y) :
    (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w)) *
        ((x : ℕ) : ZMod (residueModulus w))) +
      ((affineConst w : ℕ) : ZMod (residueModulus w)) =
      ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) := by
  unfold Realizes at h
  have hcast :
      (((2 ^ twoSteps w * y : ℕ) : ZMod (residueModulus w))) =
        (((3 ^ oddSteps w * x + affineConst w : ℕ) :
          ZMod (residueModulus w))) := by
    exact congrArg (fun n : ℕ => (n : ZMod (residueModulus w))) h
  rcases hy with ⟨k, rfl⟩
  have hid :
      2 ^ twoSteps w * (2 * k + 1) =
        2 ^ twoSteps w + residueModulus w * k := by
    unfold residueModulus
    rw [pow_succ]
    ring
  calc
    (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w)) *
          ((x : ℕ) : ZMod (residueModulus w))) +
        ((affineConst w : ℕ) : ZMod (residueModulus w))
        = (((2 ^ twoSteps w * (2 * k + 1) : ℕ) :
            ZMod (residueModulus w))) := by
            simpa using hcast.symm
    _ = (((2 ^ twoSteps w + residueModulus w * k : ℕ) :
            ZMod (residueModulus w))) := by rw [hid]
    _ = ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) := by simp

/-- 奇数終点を持つ自然数実現の開始値はcanonical剰余類に属する。 -/
theorem natural_start_has_canonical_class
    {w : ExpWord} {x y : ℕ}
    (h : Realizes w x y) (hy : Odd y) :
    ((x : ℕ) : ZMod (residueModulus w)) = canonicalClass w := by
  exact canonicalClass_unique w _ (realization_canonical_equation h hy)

/--
奇数終点を持つ自然数実現の開始値は、canonical開始値と同じ剰余を持つ。
-/
theorem natural_start_mod_eq_canonicalStart
    {w : ExpWord} {x y : ℕ}
    (h : Realizes w x y) (hy : Odd y) :
    x % residueModulus w = canonicalStart w := by
  have hc := natural_start_has_canonical_class h hy
  have hv := congrArg ZMod.val hc
  simpa [canonicalStart, ZMod.val_natCast] using hv

end ExpWord
end CollatzFirstLayer
