import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalComponentRigidity
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselFinite36
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselLargeWidthClosure

/-!
# MultiCorner: restarted branch theorem-only closure

restarted Case I から作られる `RestartedTerminalStraightPacket` は、
現在は全 width を axiom なしで排除できる。

* `width ≤ 36`:
  deterministic backward Hensel certificates と restart extra digit により
  `RestartedSuffixHenselFinite36` で排除する。

* `37 ≤ width`:
  forced Beatty repeat の nonzero branch と zero branch をともに排除した
  `RestartedSuffixHenselLargeWidthClosure` で閉じる。

従って旧 `restartedSingleCorner_noExtraThreeAdic_large` axiom は
この closure では一切使用しない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
actual restarted terminal straight packet は全 width で不可能。

finite / large の二分だけで閉じる theorem-only の最終入口。
-/
theorem restartedBranch_impossible
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart) :
    False := by
  by_cases hFinite : S.width ≤ 36
  · exact S.false_of_width_le_thirtySix hStart hFinite
  · have hLarge : 37 ≤ S.width := by
      omega
    exact
      S.restartedSuffixHensel_false_of_width_ge_37
        hStart hLarge

/--
raw last-two geometry から restarted packet を作ってそのまま theorem-only で閉じる wrapper。

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
