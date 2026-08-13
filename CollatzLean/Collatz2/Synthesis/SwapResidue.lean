import CollatzLean.Collatz2.Synthesis.PrimitiveCenter
import CollatzLean.Collatz2.Canonical.ResidueClass
import CollatzLean.Collatz2.Canonical.Representative

/-!
# Collatz2 Synthesis: word swap and canonical residue displacement

`omega` は center / commutator の量であるだけでなく、二 word の順序を交換したときの
translation の exact difference でもある。

`u ++ v` と `v ++ u` は同じ diagonal coefficients `C,A` を持つので、
odd-endpoint start residue の差も同じ `omega` によって exact に測られる。
これにより center geometry と canonical / carry 側を一つの scalar で接続する。
-/

namespace Collatz2
namespace Synthesis

open MatrixAnalysis

/-- general affine transfers の temporal order swap は translation だけ `omega` だけずれる。 -/
theorem followedBy_translate_sub_swap
    (T U : AffineTransfer) :
    (((T.followedBy U).translate : ℕ) : ℤ) -
        (((U.followedBy T).translate : ℕ) : ℤ) =
      MatrixAnalysis.omega T U := by
  simp [AffineTransfer.followedBy, MatrixAnalysis.omega,
    AffineTransfer.determinant]
  ring

/-- word order swap の affine translation difference は `omega`。 -/
theorem wordSwap_translate_sub
    (u v : Word) :
    ((Word.affineConst (u ++ v) : ℕ) : ℤ) -
        ((Word.affineConst (v ++ u) : ℕ) : ℤ) =
      MatrixAnalysis.omega
        (AffineTransfer.ofWord u)
        (AffineTransfer.ofWord v) := by
  have h := followedBy_translate_sub_swap
    (AffineTransfer.ofWord u) (AffineTransfer.ofWord v)
  rw [← AffineTransfer.ofWord_append u v,
    ← AffineTransfer.ofWord_append v u] at h
  simpa using h

/-- swapping two words does not change the odd-endpoint residue modulus。 -/
theorem residueModulus_swap
    (u v : Word) :
    Word.residueModulus (v ++ u) =
      Word.residueModulus (u ++ v) := by
  unfold Word.residueModulus
  apply congrArg (fun n : ℕ => 2 ^ n)
  simp [Word.twoSteps_append, Nat.add_comm]

/-- swapping two words does not change total odd coefficient exponent。 -/
theorem oddSteps_swap
    (u v : Word) :
    Word.oddSteps (v ++ u) = Word.oddSteps (u ++ v) := by
  simp [Word.oddSteps_append, Nat.add_comm]

/-- swapping two words does not change total two coefficient exponent。 -/
theorem twoSteps_swap
    (u v : Word) :
    Word.twoSteps (v ++ u) = Word.twoSteps (u ++ v) := by
  simp [Word.twoSteps_append, Nat.add_comm]

/--
word swap による odd-start residue displacement。

common modulus `m = residueModulus (u++v)` 上で

  startClass(uv) - startClass(vu)
    = - C_total^{-1} * omega(u,v).

右辺の inverse は既存 `leadingUnit (u++v)` の inverse。
`canonicalStart(v++u)` は common modulus へ natural cast して比較する。
-/
theorem oddStartClass_swap_displacement
    (u v : Word) :
    let m := Word.residueModulus (u ++ v)
    (((Word.canonicalStart (u ++ v) : ℕ) : ZMod m) -
        ((Word.canonicalStart (v ++ u) : ℕ) : ZMod m)) =
      -((↑((Word.leadingUnit (u ++ v))⁻¹) : ZMod m) *
        ((MatrixAnalysis.omega
          (AffineTransfer.ofWord u)
          (AffineTransfer.ofWord v) : ℤ) : ZMod m)) := by
  let m := Word.residueModulus (u ++ v)
  let xuv : ZMod m :=
    ((Word.canonicalStart (u ++ v) : ℕ) : ZMod m)
  let xvu : ZMod m :=
    ((Word.canonicalStart (v ++ u) : ℕ) : ZMod m)
  have hmod : Word.residueModulus (v ++ u) = m := by
    dsimp [m]
    exact residueModulus_swap u v
  have huv := Word.oddStartClass_spec (u ++ v)
  have huvCast := Word.canonicalStart_cast (u ++ v)
  have hvu := Word.oddStartClass_spec (v ++ u)
  have hvuCast := Word.canonicalStart_cast (v ++ u)
  rw! (castMode := .all) [hmod] at hvu hvuCast
  have hodd := oddSteps_swap u v
  have htwo := twoSteps_swap u v
  rw [hodd, htwo] at hvu
  rw [← huvCast] at huv
  rw [← hvuCast] at hvu
  change
    (((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m) * xuv) +
        ((Word.affineConst (u ++ v) : ℕ) : ZMod m) =
      ((2 ^ Word.twoSteps (u ++ v) : ℕ) : ZMod m) at huv
  change
    (((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m) * xvu) +
        ((Word.affineConst (v ++ u) : ℕ) : ZMod m) =
      ((2 ^ Word.twoSteps (u ++ v) : ℕ) : ZMod m) at hvu
  have hdiff :
      (((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m) * (xuv - xvu)) =
        ((Word.affineConst (v ++ u) : ℕ) : ZMod m) -
          ((Word.affineConst (u ++ v) : ℕ) : ZMod m) := by
    calc
      (((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m) * (xuv - xvu))
          =
          ((((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m) * xuv) +
              ((Word.affineConst (u ++ v) : ℕ) : ZMod m)) -
            ((((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m) * xvu) +
              ((Word.affineConst (v ++ u) : ℕ) : ZMod m)) +
            (((Word.affineConst (v ++ u) : ℕ) : ZMod m) -
              ((Word.affineConst (u ++ v) : ℕ) : ZMod m)) := by ring
      _ =
          ((Word.affineConst (v ++ u) : ℕ) : ZMod m) -
            ((Word.affineConst (u ++ v) : ℕ) : ZMod m) := by
              rw [huv, hvu]
              ring
  have hswapInt := wordSwap_translate_sub u v
  have hswapInt' :
      ((Word.affineConst (v ++ u) : ℤ) -
          (Word.affineConst (u ++ v) : ℤ)) =
        -MatrixAnalysis.omega
          (AffineTransfer.ofWord u)
          (AffineTransfer.ofWord v) := by
    linarith
  have hswapMod :=
    congrArg (fun z : ℤ => (z : ZMod m)) hswapInt'
  have hBmod :
      ((Word.affineConst (v ++ u) : ℕ) : ZMod m) -
          ((Word.affineConst (u ++ v) : ℕ) : ZMod m) =
        -((MatrixAnalysis.omega
          (AffineTransfer.ofWord u)
          (AffineTransfer.ofWord v) : ℤ) : ZMod m) := by
    simpa using hswapMod
  have hleading :
      (((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m)) =
        (↑(Word.leadingUnit (u ++ v)) : ZMod m) := by
    dsimp [m]
    simp [Word.leadingUnit]
  have hunit :
      xuv - xvu =
        (↑((Word.leadingUnit (u ++ v))⁻¹) : ZMod m) *
          ((((3 ^ Word.oddSteps (u ++ v) : ℕ) : ZMod m) *
            (xuv - xvu))) := by
    rw [hleading]
    simp [← mul_assoc]
  change
    xuv - xvu =
      -((↑((Word.leadingUnit (u ++ v))⁻¹) : ZMod m) *
        ((MatrixAnalysis.omega
          (AffineTransfer.ofWord u)
          (AffineTransfer.ofWord v) : ℤ) : ZMod m))
  rw [hunit, hdiff, hBmod]
  ring

end Synthesis
end Collatz2
