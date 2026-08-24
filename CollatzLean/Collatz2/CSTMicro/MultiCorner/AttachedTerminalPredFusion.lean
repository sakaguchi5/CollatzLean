import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCriticalTailFusion
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCanonicalHenselBridge
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Attached terminal predecessor fused anchor

attached straight interior では fused state

  S_k = 2^(h_k) Z_k + Q_k

が `3 S_k = 2 S_(k+1)` で運ばれる。
terminal endpoint では free-base `delta width = 0` を使わず、actual terminal exposed cut
`k = terminalCriticalStart - 1` で critical recurrence と terminal Hensel recurrence を
直接合成する。

その結果

  3 S_k = 2^(carryRunGap(k)) Z_(k+1) + 2

という exact terminal anchor を得る。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
terminal exposed predecessor における fused state の exact anchor。
右辺の指数は actual carry-normalized terminal gap そのものである。
-/
theorem terminalPred_criticalFusedValue_eq_carry
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart) :
    let k := A.normalForm.terminal
    let I := P.criticalizationStart_spec
    let Z :=
      P.integralCriticalTailStateInt
        I k
        (by
          have hCrit := A.criticalization_le_previous
          have hPrevTerm := A.normalForm.previous_lt_terminal
          dsimp [k]
          omega)
        (by
          have hSucc := A.terminal_succ_eq_terminalCriticalStart
          have hcM := P.terminalCriticalStart_spec.1
          dsimp [k]
          omega)
    let ZNext :=
      P.integralCriticalTailStateInt
        I (k + 1)
        (by
          have hCrit := A.criticalization_le_previous
          have hPrevTerm := A.normalForm.previous_lt_terminal
          dsimp [k]
          omega)
        (by
          have hSucc := A.terminal_succ_eq_terminalCriticalStart
          have hcM := P.terminalCriticalStart_spec.1
          dsimp [k]
          omega)
    3 * attachedCriticalFusedValue
        (P.h k)
        Z
        (terminalCarryTailQuotient P hStart k + 1) =
      (2 : ℤ) ^ carryRunGap P P.terminalCriticalStart k * ZNext + 2 := by
  dsimp
  let k := A.normalForm.terminal
  let I := P.criticalizationStart_spec
  have hkSucc : k + 1 = P.terminalCriticalStart := by
    dsimp [k]
    exact A.terminal_succ_eq_terminalCriticalStart
  have hkCrit : P.criticalizationStart ≤ k := by
    dsimp [k]
    have hCrit := A.criticalization_le_previous
    have hPrevTerm := A.normalForm.previous_lt_terminal
    omega
  have hkLtC : k < P.terminalCriticalStart := by
    omega
  have hkLtM : k < P.m := by
    have hcM := P.terminalCriticalStart_spec.1
    omega
  have hkNextCrit : P.criticalizationStart ≤ k + 1 := by
    omega
  have hkNextM : k + 1 ≤ P.m := by
    rw [hkSucc]
    exact P.terminalCriticalStart_spec.1
  let Z :=
    P.integralCriticalTailStateInt I k hkCrit (Nat.le_of_lt hkLtM)
  let ZNext :=
    P.integralCriticalTailStateInt I (k + 1) hkNextCrit hkNextM
  have hCritical :=
    P.integralCriticalTailStateInt_step
      I hkCrit hkLtM
  have hCritical' :
      3 * Z =
        (2 : ℤ) ^ (beattyIndex (k + 1) - beattyIndex k) * ZNext - 1 := by
    dsimp [Z, ZNext]
    linarith [hCritical]
  have hQRec :=
    terminalCarryTailQuotient_recurrence
      P hStart hkCrit hkLtC
  have hQTerminal :=
    terminalCarryTailQuotient_terminal P hStart
  have hQ :
      3 * (terminalCarryTailQuotient P hStart k + 1) =
        (2 : ℤ) ^ P.h k + 2 := by
    rw [hkSucc, hQTerminal] at hQRec
    simp only [mul_zero, zero_add] at hQRec
    linarith
  have hDepth : P.h k ≤ beattyIndex k :=
    P.admissible.depth_le hkLtM
  have hBeta : beattyIndex k ≤ beattyIndex (k + 1) :=
    le_of_lt (beattyIndex_lt_succ k)
  have hGap :=
    carryRunGap_of_succ_eq P hkSucc
  have hExponent :
      P.h k + (beattyIndex (k + 1) - beattyIndex k) =
        carryRunGap P P.terminalCriticalStart k := by
    rw [hGap]
    rw [← hkSucc]
    unfold profileCheckpoint
    omega
  have hPow :
      (2 : ℤ) ^ P.h k *
          (2 : ℤ) ^ (beattyIndex (k + 1) - beattyIndex k) =
        (2 : ℤ) ^ carryRunGap P P.terminalCriticalStart k := by
    rw [← pow_add, hExponent]
  unfold attachedCriticalFusedValue
  calc
    3 *
        ((2 : ℤ) ^ P.h k *
            P.integralCriticalTailStateInt
              I k hkCrit (Nat.le_of_lt hkLtM) +
          (terminalCarryTailQuotient P hStart k + 1)) =
      (2 : ℤ) ^ P.h k *
          (3 * P.integralCriticalTailStateInt
            I k hkCrit (Nat.le_of_lt hkLtM)) +
        3 * (terminalCarryTailQuotient P hStart k + 1) := by ring
    _ =
      (2 : ℤ) ^ P.h k *
          ((2 : ℤ) ^ (beattyIndex (k + 1) - beattyIndex k) *
              P.integralCriticalTailStateInt
                I (k + 1) hkNextCrit hkNextM - 1) +
        ((2 : ℤ) ^ P.h k + 2) := by
          rw [hCritical', hQ]
    _ =
      ((2 : ℤ) ^ P.h k *
          (2 : ℤ) ^ (beattyIndex (k + 1) - beattyIndex k)) *
          P.integralCriticalTailStateInt
            I (k + 1) hkNextCrit hkNextM + 2 := by ring
    _ =
      (2 : ℤ) ^ carryRunGap P P.terminalCriticalStart k *
          P.integralCriticalTailStateInt
            I (k + 1) hkNextCrit hkNextM + 2 := by
          rw [hPow]

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
