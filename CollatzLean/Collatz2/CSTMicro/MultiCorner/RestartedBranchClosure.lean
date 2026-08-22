import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalComponentRigidity
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSingleCornerHenselObligation

/-!
# MultiCorner: restarted branch closure modulo one pure Hensel obligation

このファイルでは唯一の axiom
`singleCornerDefect_fullDepth_exact_threeAdicOrder`
以外はすべて current repo の定義・定理から導く。

Case I restarted:

  s ≤ a,
  a は previous exposed,
  h(a+1)=0,
  terminal exposed t=c-1

から

  3^(w+1) | Tail[b,c]
  Tail[b,c] = singleCornerDefect b w

を得る。一方 full-depth exact-order axiom は extra digit を禁止するため False。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- restarted terminal straight packet は arithmetic obligation と矛盾する。 -/
theorem restartedBranch_impossible
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart) :
    False := by
  have hExtraTail := S.tail_extra_threeAdic_dvd hStart
  have hTailEq := S.tail_eq_singleCornerDefect
  rw [hTailEq] at hExtraTail
  have hFullPow :
      (3 : ℤ) ^ S.width ∣ (3 : ℤ) ^ (S.width + 1) :=
    threePow_dvd_threePow_of_le (by omega)
  have hFull :
      (3 : ℤ) ^ S.width ∣
        (singleCornerDefect S.b S.width : ℤ) :=
    dvd_trans hFullPow hExtraTail
  have hNoExtra :=
    singleCornerDefect_fullDepth_exact_threeAdicOrder
      S.beattyIndex_b_pos S.width_pos hFull
  exact hNoExtra hExtraTail

/--
raw last-two geometry から restarted packet を作ってそのまま閉じる wrapper。

`hRestart : h(a+1)=0` が restarted の局所条件、
`hCaseI : s≤a` が Case I。
-/
theorem restartedBranch_impossible_of_lastTwo
    {P : PureBProfileObstruction}
    (N : LastTwoExposedNormalForm P)
    (hTerminal : N.terminal = P.terminalCriticalStart - 1)
    (hcPos : 0 < P.terminalCriticalStart)
    (hCaseI : P.criticalizationStart ≤ N.previous)
    (hRestart : P.h (N.previous + 1) = 0)
    (hStart : 0 < P.criticalizationStart) :
    False := by
  let S : RestartedTerminalStraightPacket P N := {
    terminal_eq := hTerminal
    terminalCriticalStart_pos := hcPos
    criticalization_le_previous := hCaseI
    restart_zero := hRestart
  }
  exact restartedBranch_impossible S hStart

end MultiCorner
end CSTMicro
end Collatz2
