import CollatzLean.Collatz2.CSTMicro.MultiCorner.ShiftedCriticalizationHenselPacket

/-!
# MultiCorner: actual minimal-B shifted criticalization bridge

`ShiftedCriticalizationHenselPacket` の pure witness `y-q` を、
minimal actual B の canonical upper representative に戻す薄い wrapper。

pure packet の定義では

  y = upperR + q,
  P.q = actual q,

なので exact に

  y - q = upperR

である。従って shifted affine state の equation は

  2^p_s X_s = 3^s upperR + A_s

となる。

ここでは `X_s` と step-by-step actual prefix trace state の同定までは主張しない。
その同定が式 (7) の actual left-step recurrence に必要な最後の bridge である。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace MinimalActualABObstructionPacket

/--
actual minimal-B 由来の pure packet では `y-q` は upper representative そのもの。
-/
theorem toPureBProfileObstruction_y_sub_q_eq_upperR
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).y -
        ((M.toPureBProfileObstruction hL).q : ℤ) =
      (M.actual.firstFailureEdge.step.edge.upperR : ℤ) := by
  rw [M.toPureBProfileObstruction_y_eq_upperR_add_q hL]
  rw [M.toPureBProfileObstruction_q_eq hL]
  ring

/--
actual minimal-B specialization of the shifted affine-state equation。

日本語で読むと、criticalization cut `s` における canonical affine state は、
actual B の upper representative を `s` odd steps運んだ affine numerator を
checkpoint の 2 冪で割った値になっている。
-/
theorem shiftedAffineState_scaled_eq_actualUpperPrefixNumerator
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S :
      ShiftedCriticalizationHenselPacket
        (M.toPureBProfileObstruction hL) N) :
    (2 : ℤ) ^ S.base 0 * S.affineStateAtCriticalization =
      (3 : ℤ) ^ (M.toPureBProfileObstruction hL).criticalizationStart *
          (M.actual.firstFailureEdge.step.edge.upperR : ℤ) +
        (profileAffineNumerator
          (M.toPureBProfileObstruction hL).criticalizationStart
          (M.toPureBProfileObstruction hL).h : ℤ) := by
  have hEq := S.pow_base_mul_affineState_eq_affineNumerator
  have hYQ := toPureBProfileObstruction_y_sub_q_eq_upperR M hL
  rw [hYQ] at hEq
  exact hEq

/--
actual specializationでも state separation はそのまま成立する。

この不等式はまだ Collatz trace state との同定を使わないため、
純粋 packet の strict positivity の直接 wrapper である。
-/
theorem shiftedScaledShadow_lt_affineState
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S :
      ShiftedCriticalizationHenselPacket
        (M.toPureBProfileObstruction hL) N) :
    (2 : ℤ) ^
          (M.toPureBProfileObstruction hL).h
            (M.toPureBProfileObstruction hL).criticalizationStart *
        (M.toPureBProfileObstruction hL).criticalizationStartStateInt <
      S.affineStateAtCriticalization :=
  S.scaledShadow_lt_affineStateAtCriticalization

/--
式 (7) に必要な actual one-step bridge を名前付き obligation として露出する。

これを証明すれば `X_s` が単なる canonical affine state ではなく、
actual Collatz prefix state として一段左の state を持つことが確定する。
-/
def ShiftedActualLeftStepObligation
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S :
      ShiftedCriticalizationHenselPacket
        (M.toPureBProfileObstruction hL) N) : Prop :=
  S.HasActualLeftStepBridge

end MinimalActualABObstructionPacket

end MultiCorner
end CSTMicro
end Collatz2
