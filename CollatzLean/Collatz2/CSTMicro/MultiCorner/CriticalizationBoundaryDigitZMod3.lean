import Mathlib.Data.ZMod.Basic
import CollatzLean.Collatz2.CSTMicro.MultiCorner.ActualCriticalizationBoundaryDigit

/-!
# criticalization boundary digit を `ZMod 3` で読む

整数の divisibility として得られている

  3 ∣ U - E

を `ZMod 3` の equality に移し、canonical unit の最初の 3 進 digit を
明示的な二値 `1 / 2` として取り出す。

ここで

  E = 2^β(s-1) * (1 - 2^(β(s)-β(s-1)) Z_s).

従って boundary digit は、critical shadow を一段左へ延長できなかった
residue の有限状態版である。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- canonical criticalization unit の最初の 3 進 digit。 -/
noncomputable def criticalizationBoundaryDigit
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) : ZMod 3 :=
  (criticalizationUnit P hStart : ZMod 3)

/-- 直前 cut の extension failure を `ZMod 3` へ写した digit。 -/
noncomputable def criticalizationPredFailureDigit
    (P : PureBProfileObstruction) : ZMod 3 :=
  (((2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) *
      (1 -
        (2 : ℤ) ^
            (beattyIndex P.criticalizationStart -
              beattyIndex (P.criticalizationStart - 1)) *
          P.criticalizationStartStateInt) : ℤ) : ZMod 3)

/-- `3 ∣ x-y` を `ZMod 3` の equality に移す薄い補助補題。 -/
theorem zmodThree_eq_of_sub_dvd
    {x y : ℤ}
    (h : (3 : ℤ) ∣ x - y) :
    (x : ZMod 3) = (y : ZMod 3) := by
  have hZero : ((x - y : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).2 h
  have hSub : (x : ZMod 3) - (y : ZMod 3) = 0 := by
    simpa only [Int.cast_sub] using hZero
  exact sub_eq_zero.mp hSub

/-- boundary digit は直前 extension failure digit と exact に一致する。 -/
theorem criticalizationBoundaryDigit_eq_predFailureDigit
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    criticalizationBoundaryDigit P hStart =
      criticalizationPredFailureDigit P := by
  unfold criticalizationBoundaryDigit criticalizationPredFailureDigit
  apply zmodThree_eq_of_sub_dvd
  exact criticalizationUnit_mod_three_eq_pred_failure P hStart

/-- boundary digit は 0 ではない。 -/
theorem criticalizationBoundaryDigit_ne_zero
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    criticalizationBoundaryDigit P hStart ≠ 0 := by
  intro hZero
  have hCastZero :
      ((criticalizationUnit P hStart : ℤ) : ZMod 3) = 0 := by
    simpa [criticalizationBoundaryDigit] using hZero
  have hDvd : (3 : ℤ) ∣ criticalizationUnit P hStart :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).1 hCastZero
  exact criticalizationUnit_not_three_dvd P hStart hDvd

/-- `ZMod 3` の元は 0,1,2 のいずれか。 -/
theorem zmodThree_eq_zero_or_one_or_two
    (x : ZMod 3) :
    x = 0 ∨ x = 1 ∨ x = 2 := by
  have hxlt : x.val < 3 := ZMod.val_lt x
  have hval : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
    omega
  rcases hval with h0 | h1 | h2
  · left
    calc
      x = (x.val : ZMod 3) := (ZMod.natCast_zmod_val x).symm
      _ = 0 := by simp [h0]
  · right
    left
    calc
      x = (x.val : ZMod 3) := (ZMod.natCast_zmod_val x).symm
      _ = 1 := by simp [h1]
  · right
    right
    calc
      x = (x.val : ZMod 3) := (ZMod.natCast_zmod_val x).symm
      _ = 2 := by simp [h2]

/-- 非零性により boundary digit は `1 / 2` の二値まで落ちる。 -/
theorem criticalizationBoundaryDigit_eq_one_or_two
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    criticalizationBoundaryDigit P hStart = 1 ∨
      criticalizationBoundaryDigit P hStart = 2 := by
  rcases zmodThree_eq_zero_or_one_or_two
      (criticalizationBoundaryDigit P hStart) with h0 | h1 | h2
  · exact False.elim (criticalizationBoundaryDigit_ne_zero P hStart h0)
  · exact Or.inl h1
  · exact Or.inr h2

/-- actual minimal B でも boundary digit は `1 / 2` の二値。 -/
theorem actualCriticalizationBoundaryDigit_eq_one_or_two
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (R : RhinLinearForm14)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    criticalizationBoundaryDigit P (actualCriticalizationStart_pos M R hL) = 1 ∨
      criticalizationBoundaryDigit P (actualCriticalizationStart_pos M R hL) = 2 := by
  let P := M.toPureBProfileObstruction hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using actualCriticalizationStart_pos M R hL
  simpa [P] using criticalizationBoundaryDigit_eq_one_or_two P hStart

end MultiCorner
end CSTMicro
end Collatz2
