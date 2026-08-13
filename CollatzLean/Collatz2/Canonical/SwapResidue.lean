import CollatzLean.Collatz2.Canonical.Representative
import CollatzLean.Collatz2.Core.DisplacementForm
import Mathlib.Tactic.Linarith

/-!
# Collatz2 Canonical: word swap と separation residue

word の時間順序を交換しても diagonal coefficients は変わらず、translation だけが変わる。
その exact difference は displacement-form separation であり、canonical residue displacement
はその finite-ring shadow である。
-/

namespace Collatz2

namespace AffineTransfer

/-- Swapping two transfers changes the translation by their separation. -/
theorem followedBy_translate_sub_swap
    (T U : AffineTransfer) :
    (((T.followedBy U).translate : ℕ) : ℤ) -
        (((U.followedBy T).translate : ℕ) : ℤ) =
      T.separation U := by
  simp [AffineTransfer.followedBy,
    AffineTransfer.separation,
    DisplacementForm.resultant,
    AffineTransfer.displacementForm,
    AffineTransfer.determinant]
  ring

end AffineTransfer

namespace Word

/-- Word-order swap translation difference is displacement-form separation. -/
theorem wordSwap_translate_sub
    (u v : Word) :
    ((affineConst (u ++ v) : ℕ) : ℤ) -
        ((affineConst (v ++ u) : ℕ) : ℤ) =
      (AffineTransfer.ofWord u).separation (AffineTransfer.ofWord v) := by
  have h :=
    AffineTransfer.followedBy_translate_sub_swap
      (AffineTransfer.ofWord u) (AffineTransfer.ofWord v)
  rw [← AffineTransfer.ofWord_append u v,
    ← AffineTransfer.ofWord_append v u] at h
  simpa using h

/-- Swapping words preserves odd-endpoint residue modulus. -/
theorem residueModulus_swap
    (u v : Word) :
    residueModulus (v ++ u) = residueModulus (u ++ v) := by
  unfold residueModulus
  apply congrArg (fun n : ℕ => 2 ^ n)
  simp [twoSteps_append, Nat.add_comm]

/-- Swapping words preserves total odd-step count. -/
theorem oddSteps_swap
    (u v : Word) :
    oddSteps (v ++ u) = oddSteps (u ++ v) := by
  simp [oddSteps_append, Nat.add_comm]

/-- Swapping words preserves total two-step count. -/
theorem twoSteps_swap
    (u v : Word) :
    twoSteps (v ++ u) = twoSteps (u ++ v) := by
  simp [twoSteps_append, Nat.add_comm]

/--
Canonical odd-start class swap displacement is the modular shadow of
negative separation.
-/
theorem oddStartClass_swap_displacement
    (u v : Word) :
    let m := residueModulus (u ++ v)
    (((canonicalStart (u ++ v) : ℕ) : ZMod m) -
        ((canonicalStart (v ++ u) : ℕ) : ZMod m)) =
      -((↑((leadingUnit (u ++ v))⁻¹) : ZMod m) *
        (((AffineTransfer.ofWord u).separation
          (AffineTransfer.ofWord v) : ℤ) : ZMod m)) := by
  let m := residueModulus (u ++ v)
  let xuv : ZMod m := ((canonicalStart (u ++ v) : ℕ) : ZMod m)
  let xvu : ZMod m := ((canonicalStart (v ++ u) : ℕ) : ZMod m)
  have hmod : residueModulus (v ++ u) = m := by
    dsimp [m]
    exact residueModulus_swap u v
  have huv := oddStartClass_spec (u ++ v)
  have huvCast := canonicalStart_cast (u ++ v)
  have hvu := oddStartClass_spec (v ++ u)
  have hvuCast := canonicalStart_cast (v ++ u)
  rw! (castMode := .all) [hmod] at hvu hvuCast
  have hodd := oddSteps_swap u v
  have htwo := twoSteps_swap u v
  rw [hodd, htwo] at hvu
  rw [← huvCast] at huv
  rw [← hvuCast] at hvu
  change
    (((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m) * xuv) +
        ((affineConst (u ++ v) : ℕ) : ZMod m) =
      ((2 ^ twoSteps (u ++ v) : ℕ) : ZMod m) at huv
  change
    (((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m) * xvu) +
        ((affineConst (v ++ u) : ℕ) : ZMod m) =
      ((2 ^ twoSteps (u ++ v) : ℕ) : ZMod m) at hvu
  have hdiff :
      (((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m) * (xuv - xvu)) =
        ((affineConst (v ++ u) : ℕ) : ZMod m) -
          ((affineConst (u ++ v) : ℕ) : ZMod m) := by
    calc
      (((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m) * (xuv - xvu))
          =
          ((((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m) * xuv) +
              ((affineConst (u ++ v) : ℕ) : ZMod m)) -
            ((((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m) * xvu) +
              ((affineConst (v ++ u) : ℕ) : ZMod m)) +
            (((affineConst (v ++ u) : ℕ) : ZMod m) -
              ((affineConst (u ++ v) : ℕ) : ZMod m)) := by ring
      _ =
          ((affineConst (v ++ u) : ℕ) : ZMod m) -
            ((affineConst (u ++ v) : ℕ) : ZMod m) := by
              rw [huv, hvu]
              ring
  have hswapInt := wordSwap_translate_sub u v
  have hswapInt' :
      ((affineConst (v ++ u) : ℤ) -
          (affineConst (u ++ v) : ℤ)) =
        -(AffineTransfer.ofWord u).separation (AffineTransfer.ofWord v) := by
    linarith
  have hswapMod := congrArg (fun z : ℤ => (z : ZMod m)) hswapInt'
  have hBmod :
      ((affineConst (v ++ u) : ℕ) : ZMod m) -
          ((affineConst (u ++ v) : ℕ) : ZMod m) =
        -(((AffineTransfer.ofWord u).separation
          (AffineTransfer.ofWord v) : ℤ) : ZMod m) := by
    simpa using hswapMod
  have hleading :
      (((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m)) =
        (↑(leadingUnit (u ++ v)) : ZMod m) := by
    dsimp [m]
    simp [leadingUnit]
  have hunit :
      xuv - xvu =
        (↑((leadingUnit (u ++ v))⁻¹) : ZMod m) *
          ((((3 ^ oddSteps (u ++ v) : ℕ) : ZMod m) *
            (xuv - xvu))) := by
    rw [hleading]
    simp [← mul_assoc]
  change
    xuv - xvu =
      -((↑((leadingUnit (u ++ v))⁻¹) : ZMod m) *
        (((AffineTransfer.ofWord u).separation
          (AffineTransfer.ofWord v) : ℤ) : ZMod m))
  rw [hunit, hdiff, hBmod]
  ring

end Word
end Collatz2
