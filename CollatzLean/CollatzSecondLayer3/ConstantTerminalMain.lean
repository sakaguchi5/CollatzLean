import CollatzLean.CollatzSecondLayer3.UnboundedConstantReduction
import CollatzLean.CollatzSecondLayer3.ConstantTerminalLegacyBridge

/-!
# 発散反例排除の新しい主入口

主経路：

`Unbounded odd orbit`
  → fixed future-minimum上の全正長first-deferred系
  → Constant terminal familyが無ければterminal timeが全長さで無限遠へ逃げる
  → tail最小exponentを十分大きい全shiftへ複製
  → exponent tail eventually constant
  → 非有界性に矛盾

従って残る数学的核心はConstant terminal familyの排除一つである。
既存のConstant nested解析は`ConstantTerminalLegacyBridge`から再利用する。
-/

namespace CollatzSecondLayer3

/--
現在の大型リファクタ後に残る唯一の発散側exclusion target。
この命題を証明すれば`no_unbounded_odd_orbit_of_constantTerminal_exclusion`が直ちに使える。
-/
def ConstantTerminalMainTarget : Prop :=
  ConstantTerminalExclusionPrinciple

/-- Constant terminal主目標を閉じれば発散odd-only反例は存在しない。 -/
theorem no_unbounded_odd_orbit_of_mainTarget
    (hMain : ConstantTerminalMainTarget) :
    ¬ CollatzCore.HasUnboundedOddOrbit :=
  no_unbounded_odd_orbit_of_constantTerminal_exclusion hMain

end CollatzSecondLayer3
