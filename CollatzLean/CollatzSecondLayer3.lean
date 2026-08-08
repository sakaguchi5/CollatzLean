import CollatzLean.CollatzSecondLayer3.ActualReturn.Main
import CollatzLean.CollatzSecondLayer3.Legacy.SpecialC3
import CollatzLean.CollatzSecondLayer3.Legacy.NegativeShadow
import CollatzLean.CollatzSecondLayer3.Legacy.Terminal
/-!
# CollatzSecondLayer3

発散側の正本入口を actual-return 二局所枝へ移す。

主経路:

`HasUnboundedOddOrbit`
  → actual-return extraction
  → `r < p` を well-founded descent に吸収
  → `ExactAdjacency` または `LateNextMinimum`
  → 二枝排除
  → `¬ HasUnboundedOddOrbit`

旧 Special C3 / negative-shadow / Constant terminal 群は `Legacy` umbrella の裏で
互換 API として保持する。
-/

-- 発散側の新しい正本。

-- 旧証明経路は互換 API として保持。
