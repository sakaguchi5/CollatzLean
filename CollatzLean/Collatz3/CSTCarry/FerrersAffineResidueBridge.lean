import CollatzLean.Collatz3.CSTCarry.FerrersAffineBudget
import CollatzLean.Collatz3.CSTCarry.CarryResidueBridge
import CollatzLean.Collatz3.Bridge.FerrersAffineChainWeight
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTCarry: affine difference と binary start residue の exact bridge

固定 `(p,H)` の affine equation

  2^H y = 3^p x + B

を `mod 2^H` で見ると start class は

  3^p x + B = 0  (mod 2^H)

で決まる。

`B_before = B_after + S` なら start class の displacement は exact に

  x_after - x_before = 3^(-p) S  (mod 2^H)

となる。この右辺は既存の `binaryShiftClass p H S` そのもの。

従って Ferrers affine difference と CSTCarry の binary shift は同じ residue 変位を
二つの語彙で見ている。
-/

namespace Collatz3
namespace CSTCarry

/--
固定 `2^H` 上の affine start class。
`binaryShiftClass p H B = 3^(-p) B` なので、その additive inverse として定義する。
-/
def affineStartClassModTwoPow
    (p H B : ℕ) : ZMod (2 ^ H) :=
  - binaryShiftClass p H B

/-- affine start class の defining congruence。 -/
theorem affineStartClassModTwoPow_spec
    (p H B : ℕ) :
    (((3 ^ p : ℕ) : ZMod (2 ^ H)) *
        affineStartClassModTwoPow p H B) +
      ((B : ℕ) : ZMod (2 ^ H)) = 0 := by
  unfold affineStartClassModTwoPow
  rw [mul_neg, binaryShiftClass_spec]
  simp

/-- affine start class の最小非負代表。 -/
def affineStartRepresentativeModTwoPow
    (p H B : ℕ) : ℕ :=
  (affineStartClassModTwoPow p H B).val

/-- start representative は H-bit 範囲内。 -/
theorem affineStartRepresentativeModTwoPow_lt_modulus
    (p H B : ℕ) :
    affineStartRepresentativeModTwoPow p H B < 2 ^ H := by
  have : NeZero (2 ^ H) := ⟨by positivity⟩
  exact ZMod.val_lt (affineStartClassModTwoPow p H B)

/--
## affine difference -> residue displacement

`B_before = B_after + S` なら

`R_after - R_before = binaryShiftClass p H S`。
-/
theorem affineStartClass_displacement_of_affineDifference
    {p H BBefore BAfter S : ℕ}
    (hB : BBefore = BAfter + S) :
    affineStartClassModTwoPow p H BAfter -
        affineStartClassModTwoPow p H BBefore =
      binaryShiftClass p H S := by
  apply binaryShiftClass_unique p H S
  have hBefore := affineStartClassModTwoPow_spec p H BBefore
  have hAfter := affineStartClassModTwoPow_spec p H BAfter
  have hBeforeMul :
      (((3 ^ p : ℕ) : ZMod (2 ^ H)) *
          affineStartClassModTwoPow p H BBefore) =
        -((BBefore : ℕ) : ZMod (2 ^ H)) := by
    exact eq_neg_of_add_eq_zero_left hBefore
  have hAfterMul :
      (((3 ^ p : ℕ) : ZMod (2 ^ H)) *
          affineStartClassModTwoPow p H BAfter) =
        -((BAfter : ℕ) : ZMod (2 ^ H)) := by
    exact eq_neg_of_add_eq_zero_left hAfter
  have hCast := congrArg
    (fun n : ℕ => (n : ZMod (2 ^ H))) hB
  simp only [Nat.cast_add] at hCast
  calc
    (((3 ^ p : ℕ) : ZMod (2 ^ H)) *
        (affineStartClassModTwoPow p H BAfter -
          affineStartClassModTwoPow p H BBefore))
        =
      (((3 ^ p : ℕ) : ZMod (2 ^ H)) *
          affineStartClassModTwoPow p H BAfter) -
        (((3 ^ p : ℕ) : ZMod (2 ^ H)) *
          affineStartClassModTwoPow p H BBefore) := by ring
    _ =
      -((BAfter : ℕ) : ZMod (2 ^ H)) -
        (-((BBefore : ℕ) : ZMod (2 ^ H))) := by
          rw [hAfterMul, hBeforeMul]
    _ =
      ((BBefore : ℕ) : ZMod (2 ^ H)) -
        ((BAfter : ℕ) : ZMod (2 ^ H)) := by ring
    _ = ((S : ℕ) : ZMod (2 ^ H)) := by
      rw [hCast]
      ring

/--
Ferrers rows では boundary/actual affine difference が weighted defect なので、
その start residue displacement は canonical binary shift class と exact に一致する。
-/
theorem ferrersAffineStart_displacement_eq_binaryShiftClass
    (H : ℕ)
    (rows : List FerrersRow) :
    affineStartClassModTwoPow rows.length H (ferrersActualAffine rows) -
        affineStartClassModTwoPow rows.length H (ferrersBoundaryAffine rows) =
      binaryShiftClass rows.length H (ferrersWeightedDefect rows) := by
  apply affineStartClass_displacement_of_affineDifference
  exact ferrersBoundaryAffine_eq_actualAffine_add_weightedDefect rows

/--
Ferrers binary shift は affine start displacement class の最小非負代表そのもの。
-/
theorem ferrersBinaryShift_eq_affineStartDisplacement_val
    (H : ℕ)
    (rows : List FerrersRow) :
    ferrersBinaryShift H rows =
      (affineStartClassModTwoPow rows.length H (ferrersActualAffine rows) -
        affineStartClassModTwoPow rows.length H (ferrersBoundaryAffine rows)).val := by
  have hClass := ferrersAffineStart_displacement_eq_binaryShiftClass H rows
  have hVal := congrArg ZMod.val hClass
  unfold ferrersBinaryShift binaryShift
  exact hVal.symm

namespace CarryRealizes

/--
carry final residue は、Ferrers boundary affine から actual affine への
start-residue displacement と同じ class。
-/
theorem finalClass_eq_ferrersAffineStart_displacement
    {H : ℕ}
    {rows : List FerrersRow}
    {digits : List ℕ}
    {F : ℕ}
    (h : CarryRealizes (2 ^ H) rows 0 digits F) :
    ((F : ℕ) : ZMod (2 ^ H)) =
      affineStartClassModTwoPow rows.length H (ferrersActualAffine rows) -
        affineStartClassModTwoPow rows.length H (ferrersBoundaryAffine rows) := by
  rw [h.final_mod_eq_binaryShiftClass]
  exact (ferrersAffineStart_displacement_eq_binaryShiftClass H rows).symm

end CarryRealizes
end CSTCarry

namespace Word

/--
word の affine numerator を fixed `2^H` 上の start residue として読む薄い wrapper。
`H` は外部から固定し、Ferrers move 前後で同じ modulus を使えるようにする。
-/
def ferrersStartClassAtDepth
    (H : ℕ)
    (w : Word) : ZMod (2 ^ H) :=
  CSTCarry.affineStartClassModTwoPow (oddSteps w) H (affineConst w)

/-- fixed-depth start residue の最小非負代表。 -/
def ferrersStartRepresentativeAtDepth
    (H : ℕ)
    (w : Word) : ℕ :=
  (ferrersStartClassAtDepth H w).val

/-- representative は H-bit 範囲内。 -/
theorem ferrersStartRepresentativeAtDepth_lt_modulus
    (H : ℕ)
    (w : Word) :
    ferrersStartRepresentativeAtDepth H w < 2 ^ H := by
  have : NeZero (2 ^ H) := ⟨by positivity⟩
  exact ZMod.val_lt (ferrersStartClassAtDepth H w)

namespace FerrersCellStep

/--
## 1-cell residue law

一つの Ferrers cell move の start residue displacement は、その cell affine weight の
binary shift class と exact に一致する。
-/
theorem startClass_displacement
    {wBefore wAfter : Word}
    {weight : ℕ}
    (h : FerrersCellStep wBefore wAfter weight) :
    ferrersStartClassAtDepth (twoSteps wBefore) wAfter -
        ferrersStartClassAtDepth (twoSteps wBefore) wBefore =
      CSTCarry.binaryShiftClass
        (oddSteps wBefore) (twoSteps wBefore) weight := by
  have hp : oddSteps wBefore = oddSteps wAfter := h.length_depth_eq.1
  change
    CSTCarry.affineStartClassModTwoPow
        (oddSteps wAfter) (twoSteps wBefore) (affineConst wAfter) -
      CSTCarry.affineStartClassModTwoPow
        (oddSteps wBefore) (twoSteps wBefore) (affineConst wBefore) =
      CSTCarry.binaryShiftClass
        (oddSteps wBefore) (twoSteps wBefore) weight
  rw [← hp]
  exact CSTCarry.affineStartClass_displacement_of_affineDifference h.affineConst_eq

end FerrersCellStep

namespace FerrersCellChain

/--
有限 Ferrers cell chain 全体でも、endpoint start residue displacement は
chain total affine weight の binary shift class と exact に一致する。
-/
theorem startClass_displacement
    {w₀ w₁ : Word}
    {total : ℕ}
    (h : FerrersCellChain w₀ w₁ total) :
    ferrersStartClassAtDepth (twoSteps w₀) w₁ -
        ferrersStartClassAtDepth (twoSteps w₀) w₀ =
      CSTCarry.binaryShiftClass
        (oddSteps w₀) (twoSteps w₀) total := by
  have hp : oddSteps w₀ = oddSteps w₁ := h.oddSteps_eq
  change
    CSTCarry.affineStartClassModTwoPow
        (oddSteps w₁) (twoSteps w₀) (affineConst w₁) -
      CSTCarry.affineStartClassModTwoPow
        (oddSteps w₀) (twoSteps w₀) (affineConst w₀) =
      CSTCarry.binaryShiftClass
        (oddSteps w₀) (twoSteps w₀) total
  rw [← hp]
  exact CSTCarry.affineStartClass_displacement_of_affineDifference h.affineConst_eq

end FerrersCellChain
end Word
end Collatz3
