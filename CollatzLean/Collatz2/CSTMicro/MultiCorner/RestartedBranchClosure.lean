import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalComponentRigidity
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSingleCornerHenselObligation

/-!
# MultiCorner: restarted branch closure modulo one branch-specific arithmetic obligation

このファイルでは唯一の axiom
`restartedSingleCorner_noExtraThreeAdic`
以外はすべて current repo の定義・定理から導く。

Case I restarted:

  s ≤ a,
  a は previous exposed,
  h(a+1)=0,
  terminal exposed t=c-1

から

  3^(w+1) | Tail[b,c]
  Tail[b,c] = singleCornerDefect b w

を得る。

新しい arithmetic obligation は arbitrary `(b,w)` の
full-depth exact-order を要求しない。
この actual restarted packet について extra digit
`3^(w+1)` だけを禁止するため、そのまま False になる。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- restarted terminal straight packet は branch-specific arithmetic obligation と矛盾する。 -/
theorem restartedBranch_impossible
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart) :
    False := by
  have hExtraTail := S.tail_extra_threeAdic_dvd hStart
  have hTailEq := S.tail_eq_singleCornerDefect
  rw [hTailEq] at hExtraTail
  exact
    (restartedSingleCorner_noExtraThreeAdic S hStart)
      hExtraTail

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
