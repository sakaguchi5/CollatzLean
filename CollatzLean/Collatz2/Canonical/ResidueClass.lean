import CollatzLean.Collatz2.Core.Realization
import Mathlib.Data.ZMod.Basic

/-!
# Collatz2: odd-endpoint realization residue class

canonical start を primitive に置かない。
まず、一つの word を奇数 endpoint で実現する全 start が属する
2進合同類を lossless affine equation から抽出する。

この合同類の最小非負代表は次段階で canonical representative として定義する。
-/

namespace Collatz2
namespace Word

/--
奇数 endpoint を持つ realization の start を分類する法。
`A = 2^H` に対して modulus は `2A = 2^(H+1)`。
-/
def residueModulus (w : Word) : ℕ :=
  2 ^ (twoSteps w + 1)

@[simp] theorem residueModulus_pos (w : Word) :
    0 < residueModulus w := by
  simp [residueModulus]

/-- `3^p` と odd-endpoint residue modulus は互いに素。 -/
theorem coprime_three_pow_residueModulus (w : Word) :
    Nat.Coprime (3 ^ oddSteps w) (residueModulus w) := by
  exact
    ((by decide : Nat.Coprime 3 2).pow_left (oddSteps w)).pow_right
      (twoSteps w + 1)

/-- residue modulus における `3^p` の単元。 -/
def leadingUnit (w : Word) : (ZMod (residueModulus w))ˣ :=
  ZMod.unitOfCoprime
    (3 ^ oddSteps w)
    (coprime_three_pow_residueModulus w)

/--
奇数 endpoint realization の start が属する一意な合同類。

奇数 `Y = 2k+1` なら
`2^H Y = 2^H (mod 2^(H+1))` なので、
`3^p X + B = 2^H` を modulus 上で解いた class である。
-/
def oddStartClass (w : Word) : ZMod (residueModulus w) :=
  (↑((leadingUnit w)⁻¹) : ZMod (residueModulus w)) *
    (((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) -
      ((affineConst w : ℕ) : ZMod (residueModulus w)))

/-- odd-start class は defining congruence を満たす。 -/
theorem oddStartClass_spec (w : Word) :
    (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w)) * oddStartClass w) +
      ((affineConst w : ℕ) : ZMod (residueModulus w)) =
      ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) := by
  unfold oddStartClass
  have hleading :
      (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w))) =
        (↑(leadingUnit w) : ZMod (residueModulus w)) := by
    simp [leadingUnit]
  rw [hleading]
  simp [← mul_assoc]

/-- defining congruence の解は odd-start class に一意。 -/
theorem oddStartClass_unique
    (w : Word)
    (x : ZMod (residueModulus w))
    (hx :
      (((3 ^ oddSteps w : ℕ) : ZMod (residueModulus w)) * x) +
        ((affineConst w : ℕ) : ZMod (residueModulus w)) =
        ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w))) :
    x = oddStartClass w := by
  have hm :
      (↑(leadingUnit w) : ZMod (residueModulus w)) * x =
        (((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) -
          ((affineConst w : ℕ) : ZMod (residueModulus w))) := by
    simpa [leadingUnit, ZMod.coe_unitOfCoprime, eq_sub_iff_add_eq] using hx
  calc
    x =
        (↑((leadingUnit w)⁻¹) : ZMod (residueModulus w)) *
          ((↑(leadingUnit w) : ZMod (residueModulus w)) * x) := by simp
    _ =
        (↑((leadingUnit w)⁻¹) : ZMod (residueModulus w)) *
          (((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) -
            ((affineConst w : ℕ) : ZMod (residueModulus w))) := by rw [hm]
    _ = oddStartClass w := rfl

/--
奇数 endpoint を持つ realization の start は必ず odd-start class に属する。
-/
theorem Realizes.start_has_oddStartClass
    {w : Word} {x y : ℕ}
    (h : Realizes w x y)
    (hy : Odd y) :
    ((x : ℕ) : ZMod (residueModulus w)) = oddStartClass w := by
  apply oddStartClass_unique
  have hEq := (realizes_iff w x y).1 h
  have hcast := congrArg (fun n : ℕ => (n : ZMod (residueModulus w))) hEq
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
        =
        (((2 ^ twoSteps w * (2 * k + 1) : ℕ) :
          ZMod (residueModulus w))) := by
            simpa using hcast.symm
    _ =
        (((2 ^ twoSteps w + residueModulus w * k : ℕ) :
          ZMod (residueModulus w))) := by rw [hid]
    _ = ((2 ^ twoSteps w : ℕ) : ZMod (residueModulus w)) := by simp

/-- residue modulus の整数 cast。 -/
@[simp] theorem residueModulus_int_cast (w : Word) :
    (residueModulus w : ℤ) = (2 : ℤ) ^ (twoSteps w + 1) := by
  simp [residueModulus]

end Word
end Collatz2
