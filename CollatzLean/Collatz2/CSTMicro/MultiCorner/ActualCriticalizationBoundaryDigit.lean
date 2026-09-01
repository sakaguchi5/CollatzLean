import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileNumeratorValuation
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CriticalizationUnitModThree

/-!
# actual minimal B の criticalization boundary digit

一般の `PureBProfileObstruction` に対して得られた

* `criticalizationStart` の直前 residue の失敗、
* `criticalizationUnit` の非 3-divisibility、
* start state による exact expression、
* 最初の mod 3 digit の同定、

を actual minimal-B packet から直接読める形に包む。

このファイルでは新しい仮定を追加しない。
`RhinLinearForm14` から既存の `criticalizationStart_pos` を取り出して、
既に証明済みの一般定理へ渡すだけである。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- actual minimal B の canonical criticalization start は正。 -/
theorem actualCriticalizationStart_pos
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (R : RhinLinearForm14)
    (hL : 2 < L) :
    0 < (M.toPureBProfileObstruction hL).criticalizationStart :=
  M.criticalizationStart_pos R hL

/-- actual minimal B の criticalization start state。 -/
noncomputable def actualCriticalizationStartStateInt
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) : ℤ :=
  (M.toPureBProfileObstruction hL).criticalizationStartStateInt

/-- actual minimal B の canonical criticalization unit。 -/
noncomputable def actualCriticalizationUnit
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (R : RhinLinearForm14)
    (hL : 2 < L) : ℤ :=
  criticalizationUnit
    (M.toPureBProfileObstruction hL)
    (actualCriticalizationStart_pos M R hL)

/-- actual minimal B では、critical shadow を一段左へ延長する residue が失敗する。 -/
theorem actualCriticalization_pred_not_integral_residue
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (R : RhinLinearForm14)
    (hL : 2 < L) :
    ¬ (3 : ℤ) ∣
      (2 : ℤ) ^
          (beattyIndex (M.toPureBProfileObstruction hL).criticalizationStart -
            beattyIndex
              ((M.toPureBProfileObstruction hL).criticalizationStart - 1)) *
        actualCriticalizationStartStateInt M hL - 1 := by
  let P := M.toPureBProfileObstruction hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using actualCriticalizationStart_pos M R hL
  simpa [P, actualCriticalizationStartStateInt] using
    P.criticalizationStart_pred_not_integral_residue hStart

/-- actual minimal B の canonical criticalization unit は 3 で割れない。 -/
theorem actualCriticalizationUnit_not_three_dvd
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (R : RhinLinearForm14)
    (hL : 2 < L) :
    ¬ (3 : ℤ) ∣ actualCriticalizationUnit M R hL := by
  let P := M.toPureBProfileObstruction hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using actualCriticalizationStart_pos M R hL
  simpa [P, actualCriticalizationUnit] using
    criticalizationUnit_not_three_dvd P hStart

/--
actual minimal B の unit を criticalization start state で exact に展開する。

  U = 3^s (y-q) + Ψ(s) - 2^β(s) Z_s.
-/
theorem actualCriticalizationUnit_eq_start_state_expression
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (R : RhinLinearForm14)
    (hL : 2 < L) :
    actualCriticalizationUnit M R hL =
      let P := M.toPureBProfileObstruction hL
      (3 : ℤ) ^ P.criticalizationStart * (P.y - (P.q : ℤ)) +
        criticalPrefixPhiZ P.criticalizationStart -
        (2 : ℤ) ^ beattyIndex P.criticalizationStart *
          P.criticalizationStartStateInt := by
  let P := M.toPureBProfileObstruction hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using actualCriticalizationStart_pos M R hL
  simpa [P, actualCriticalizationUnit] using
    criticalizationUnit_eq_start_state_expression P hStart

/--
actual minimal B の unit の mod 3 classは、直前 cut での extension failure と一致する。
-/
theorem actualCriticalizationUnit_mod_three_eq_pred_failure
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (R : RhinLinearForm14)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    (3 : ℤ) ∣
      actualCriticalizationUnit M R hL -
        (2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) *
          (1 -
            (2 : ℤ) ^
                (beattyIndex P.criticalizationStart -
                  beattyIndex (P.criticalizationStart - 1)) *
              P.criticalizationStartStateInt) := by
  let P := M.toPureBProfileObstruction hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using actualCriticalizationStart_pos M R hL
  simpa [P, actualCriticalizationUnit] using
    criticalizationUnit_mod_three_eq_pred_failure P hStart

/--
actual minimal B の boundary arithmetic を一つにまとめた packet。
左延長 residue は失敗し、同時に unit も mod 3 で非零である。
-/
theorem actualCriticalization_boundary_packet
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (R : RhinLinearForm14)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    (¬ (3 : ℤ) ∣
      (2 : ℤ) ^
          (beattyIndex P.criticalizationStart -
            beattyIndex (P.criticalizationStart - 1)) *
        P.criticalizationStartStateInt - 1) ∧
    (¬ (3 : ℤ) ∣ actualCriticalizationUnit M R hL) := by
  let P := M.toPureBProfileObstruction hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using actualCriticalizationStart_pos M R hL
  have hPacket := criticalization_pred_failure_and_unit_nonzero P hStart
  simpa [P, actualCriticalizationUnit] using hPacket

end MultiCorner
end CSTMicro
end Collatz2
