import CollatzLean.Collatz2.CSTMicro.MultiCorner.LeftOfCriticalizationBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CriticalizationPredResidue

/-!
# criticalization unit と開始 state の exact identity

profile numerator の exact 3 進 quotient

  N = 3^(m-s) * U

で定義される `criticalizationUnit = U` を、`criticalizationStart = s` における
critical shadow state `Z_s` と直接結ぶ。

得られる式は

  U = 3^s (y-q) + Ψ(s) - 2^β(s) Z_s.

これにより global profile numerator の最初の非零 3 進 digit を、
criticalization boundary の one-step state と同じ式の中で扱える。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
`criticalizationUnit` を criticalization 開始 state で exact に展開する。

  U = 3^s (y-q) + Ψ(s) - 2^β(s) Z_s.

証明は origin raw-tail balance と cut `s` での raw-tail decomposition を、
共通因子 `3^(m-s)` で割るだけである。
-/
theorem criticalizationUnit_eq_start_state_expression
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    criticalizationUnit P hStart =
      (3 : ℤ) ^ P.criticalizationStart *
          (P.y - (P.q : ℤ)) +
        criticalPrefixPhiZ P.criticalizationStart -
        (2 : ℤ) ^ beattyIndex P.criticalizationStart *
          P.criticalizationStartStateInt := by
  have hsLe : P.criticalizationStart ≤ P.m :=
    P.criticalizationStart_spec.1
  have hTail :=
    P.terminalRawTail_zero_eq_scaled_tail_sub_prefix hsLe
  have hState :=
    P.terminalRawTail_criticalizationStart_eq_threePow_mul_state
  have hBalance := P.terminalRawTail_zero_eq_profile_balance
  have hUnit :=
    profileNumerator_eq_threePow_mul_criticalizationUnit P hStart
  have hM :
      P.m =
        (P.m - P.criticalizationStart) + P.criticalizationStart := by
    omega
  have hPowM :
      (3 : ℤ) ^ P.m =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          (3 : ℤ) ^ P.criticalizationStart := by
    calc
      (3 : ℤ) ^ P.m =
          (3 : ℤ) ^
            ((P.m - P.criticalizationStart) + P.criticalizationStart) := by
              congr 1
      _ =
          (3 : ℤ) ^ (P.m - P.criticalizationStart) *
            (3 : ℤ) ^ P.criticalizationStart := by
              rw [pow_add]
  have hTailFactored :
      P.terminalRawTail 0 =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((2 : ℤ) ^ beattyIndex P.criticalizationStart *
              P.criticalizationStartStateInt -
            criticalPrefixPhiZ P.criticalizationStart) := by
    calc
      P.terminalRawTail 0
          =
        (2 : ℤ) ^ beattyIndex P.criticalizationStart *
            P.terminalRawTail P.criticalizationStart -
          (3 : ℤ) ^ (P.m - P.criticalizationStart) *
            criticalPrefixPhiZ P.criticalizationStart := hTail
      _ =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((2 : ℤ) ^ beattyIndex P.criticalizationStart *
              P.criticalizationStartStateInt -
            criticalPrefixPhiZ P.criticalizationStart) := by
              rw [hState]
              ring
  have hBalanceFactored :
      P.terminalRawTail 0 =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((3 : ℤ) ^ P.criticalizationStart *
              (P.y - (P.q : ℤ)) -
            criticalizationUnit P hStart) := by
    calc
      P.terminalRawTail 0
          =
        (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) -
          (profileDyadicCellNumerator P.m P.h : ℤ) := hBalance
      _ =
        (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) -
          (3 : ℤ) ^ (P.m - P.criticalizationStart) *
            criticalizationUnit P hStart := by
              rw [hUnit]
      _ =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((3 : ℤ) ^ P.criticalizationStart *
              (P.y - (P.q : ℤ)) -
            criticalizationUnit P hStart) := by
              rw [hPowM]
              ring
  have hPowNe :
      (3 : ℤ) ^ (P.m - P.criticalizationStart) ≠ 0 := by
    positivity
  have hScaled :
      (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((2 : ℤ) ^ beattyIndex P.criticalizationStart *
              P.criticalizationStartStateInt -
            criticalPrefixPhiZ P.criticalizationStart) =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((3 : ℤ) ^ P.criticalizationStart *
              (P.y - (P.q : ℤ)) -
            criticalizationUnit P hStart) := by
    calc
      (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((2 : ℤ) ^ beattyIndex P.criticalizationStart *
              P.criticalizationStartStateInt -
            criticalPrefixPhiZ P.criticalizationStart)
          = P.terminalRawTail 0 := hTailFactored.symm
      _ =
        (3 : ℤ) ^ (P.m - P.criticalizationStart) *
          ((3 : ℤ) ^ P.criticalizationStart *
              (P.y - (P.q : ℤ)) -
            criticalizationUnit P hStart) := hBalanceFactored
  have hCore :
      (2 : ℤ) ^ beattyIndex P.criticalizationStart *
            P.criticalizationStartStateInt -
          criticalPrefixPhiZ P.criticalizationStart =
        (3 : ℤ) ^ P.criticalizationStart *
            (P.y - (P.q : ℤ)) -
          criticalizationUnit P hStart :=
    mul_left_cancel₀ hPowNe hScaled
  linarith

end MultiCorner
end CSTMicro
end Collatz2
