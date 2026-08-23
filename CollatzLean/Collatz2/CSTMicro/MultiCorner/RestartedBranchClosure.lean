import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalComponentRigidity
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSingleCornerHenselObligation

/-!
# MultiCorner: restarted branch closure modulo one large-width arithmetic obligation

このファイルでは唯一の axiom
`restartedSingleCorner_noExtraThreeAdic_large`
以外はすべて current repo の定義・定理から導く。

Case I restarted から

  3^(w+1) | Tail[b,c]
  Tail[b,c] = singleCornerDefect b w

を得る。

ここで width を分ける。

* `w ≤ 3`:
  `RestartedSingleCornerHenselObligation` 内の exact finite recurrence 計算で
  extra digit を theorem として排除する。

* `4 ≤ w`:
  branch-specific large-width obligation
  `restartedSingleCorner_noExtraThreeAdic_large`
  を使う。

したがって axiom は actual restarted branch の large-width 部分だけに残る。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- restarted terminal straight packet は small theorem / large-width obligation と矛盾する。 -/
theorem restartedBranch_impossible
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart) :
    False := by
  have hExtraTail := S.tail_extra_threeAdic_dvd hStart
  have hTailEq := S.tail_eq_singleCornerDefect
  rw [hTailEq] at hExtraTail
  by_cases hSmall : S.width ≤ 3
  · exact
      (restartedSingleCorner_noExtraThreeAdic_small S hSmall)
        hExtraTail
  · have hLarge : 4 ≤ S.width := by
      omega
    exact
      (restartedSingleCorner_noExtraThreeAdic_large
        S hStart hLarge)
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
