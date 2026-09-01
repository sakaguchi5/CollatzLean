import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalPhasePeriodicity
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CriticalizationUnitStartState

/-!
# criticalization unit の最初の 3 進 digit

`criticalizationUnit` の mod 3 class を、`criticalizationStart = s` の一段左で
critical shadow を延長できなかった residue と同定する。

中心式は

  U ≡ 2^β(s-1) * (1 - 2^(β(s)-β(s-1)) Z_s)  (mod 3).

従って `U` の最初の非零 3 進 digit は、arithmetic criticalization の
one-step extension failure をそのまま記録している。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
正の `s` では critical prefix numerator は最後の一セルを分離して

  Ψ(s) = 3 Ψ(s-1) + 2^β(s-1)

と書ける。
-/
theorem criticalPrefixPhiZ_eq_three_mul_pred_add_twoPow
    {s : ℕ}
    (hs : 0 < s) :
    criticalPrefixPhiZ s =
      3 * criticalPrefixPhiZ (s - 1) +
        (2 : ℤ) ^ beattyIndex (s - 1) := by
  have hPredLe : s - 1 ≤ s := by omega
  have hEndpoint :=
    criticalPrefixPhiZ_endpoint_decomposition hPredLe
  have hSucc : s - 1 + 1 = s := by omega
  have hCell := criticalIntervalPhiZ_step_eq_one_stage8 (s - 1)
  rw [hSucc] at hCell
  have hDist : s - (s - 1) = 1 := by omega
  rw [hDist, hCell] at hEndpoint
  norm_num at hEndpoint
  exact hEndpoint

/--
`criticalizationUnit` の mod 3 classは、直前 cut から critical shadow を
一段延長できなかった residue と一致する。

Lean では合同式を divisibility として

  3 ∣ U - 2^β(s-1) * (1 - 2^(β(s)-β(s-1)) Z_s)

と表す。
-/
theorem criticalizationUnit_mod_three_eq_pred_failure
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    (3 : ℤ) ∣
      criticalizationUnit P hStart -
        (2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) *
          (1 -
            (2 : ℤ) ^
                (beattyIndex P.criticalizationStart -
                  beattyIndex (P.criticalizationStart - 1)) *
              P.criticalizationStartStateInt) := by
  have hUnit :=
    criticalizationUnit_eq_start_state_expression P hStart
  have hPrefix :=
    criticalPrefixPhiZ_eq_three_mul_pred_add_twoPow hStart
  have hBetaLe :
      beattyIndex (P.criticalizationStart - 1) ≤
        beattyIndex P.criticalizationStart :=
    le_of_lt (beattyIndex_strictMono (by omega))
  have hBeta :
      beattyIndex P.criticalizationStart =
        beattyIndex (P.criticalizationStart - 1) +
          (beattyIndex P.criticalizationStart -
            beattyIndex (P.criticalizationStart - 1)) := by
    omega
  have hTwoPow :
      (2 : ℤ) ^ beattyIndex P.criticalizationStart =
        (2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) *
          (2 : ℤ) ^
            (beattyIndex P.criticalizationStart -
              beattyIndex (P.criticalizationStart - 1)) := by
    calc
      (2 : ℤ) ^ beattyIndex P.criticalizationStart =
          (2 : ℤ) ^
            (beattyIndex (P.criticalizationStart - 1) +
              (beattyIndex P.criticalizationStart -
                beattyIndex (P.criticalizationStart - 1))) := by
              congr 1
      _ =
          (2 : ℤ) ^ beattyIndex (P.criticalizationStart - 1) *
            (2 : ℤ) ^
              (beattyIndex P.criticalizationStart -
                beattyIndex (P.criticalizationStart - 1)) := by
              rw [pow_add]
  have hStartEq :
      P.criticalizationStart =
        (P.criticalizationStart - 1) + 1 := by
    omega
  have hThreePow :
      (3 : ℤ) ^ P.criticalizationStart =
        3 * (3 : ℤ) ^ (P.criticalizationStart - 1) := by
    calc
      (3 : ℤ) ^ P.criticalizationStart =
          (3 : ℤ) ^ ((P.criticalizationStart - 1) + 1) := by
            congr 1
      _ = (3 : ℤ) ^ (P.criticalizationStart - 1) * 3 := by
            rw [pow_succ]
      _ = 3 * (3 : ℤ) ^ (P.criticalizationStart - 1) := by ring
  refine ⟨
    (3 : ℤ) ^ (P.criticalizationStart - 1) *
        (P.y - (P.q : ℤ)) +
      criticalPrefixPhiZ (P.criticalizationStart - 1),
    ?_⟩
  rw [hUnit, hPrefix, hThreePow, hTwoPow]
  ring

/--
前の residue の失敗は、上の合同式を通して `criticalizationUnit` が mod 3 で
零にならないことと整合する。

この補題は両事実を一つの packet として後段へ渡すためのまとめである。
-/
theorem criticalization_pred_failure_and_unit_nonzero
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    (¬ (3 : ℤ) ∣
      (2 : ℤ) ^
          (beattyIndex P.criticalizationStart -
            beattyIndex (P.criticalizationStart - 1)) *
        P.criticalizationStartStateInt - 1) ∧
    (¬ (3 : ℤ) ∣ criticalizationUnit P hStart) := by
  constructor
  · exact P.criticalizationStart_pred_not_integral_residue hStart
  · exact criticalizationUnit_not_three_dvd P hStart

end MultiCorner
end CSTMicro
end Collatz2
