import CollatzLean.CollatzSecondLayer3.UnboundedConstantReduction
import CollatzLean.CollatzSecondLayer3.ConstantTerminalLegacyBridge
import CollatzLean.CollatzSecondLayer3.FutureMinimumHighEvent

/-!
# 発散反例排除の新しい主入口

大型リファクタ後のall-length議論に加え、Constant terminalはさらに
`terminalTime = 0`のfuture-minimum high-event towerまで縮約できる。

主経路：

`Unbounded odd orbit`
  → standard future-minimum
  → high exponent positions occur cofinally
  → sufficiently far high-event windows are Special C3
  → first-deferred terminalTime = 0
  → T=0 Constant terminal family

従って現在の最も鋭い発散側主目標は、future-minimum high-event towerの不存在である。
Constant terminal排除原理を証明すれば、この主目標も直ちに従う。
-/

namespace CollatzSecondLayer3

/--
現在の大型リファクタ後に残る最も鋭い発散側exclusion target。
非有界軌道なら必ずこのtowerが存在するため、これを排除すれば発散反例は存在しない。
-/
def FutureMinimumHighEventExclusionPrinciple : Prop :=
  ¬ HasFutureMinimumHighEventTower

/-- 現在の主目標。 -/
def ConstantTerminalMainTarget : Prop :=
  FutureMinimumHighEventExclusionPrinciple

/-- 従来のConstant terminal排除原理は新しいhigh-event主目標を含意する。 -/
theorem mainTarget_of_constantTerminal_exclusion
    (hConstant : ConstantTerminalExclusionPrinciple) :
    ConstantTerminalMainTarget := by
  exact no_highEventTower_of_constantTerminal_exclusion hConstant

/-- high-event主目標を閉じれば発散odd-only反例は存在しない。 -/
theorem no_unbounded_odd_orbit_of_mainTarget
    (hMain : ConstantTerminalMainTarget) :
    ¬ CollatzCore.HasUnboundedOddOrbit :=
  no_unbounded_odd_orbit_of_highEvent_exclusion hMain

end CollatzSecondLayer3
