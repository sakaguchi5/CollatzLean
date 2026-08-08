import CollatzLean.CollatzSecondLayer3.ActualReturn.Main
import CollatzLean.CollatzSecondLayer3.ActualReturn.AssetReconnect
import CollatzLean.CollatzSecondLayer3.Legacy.SpecialC3
import CollatzLean.CollatzSecondLayer3.Legacy.NegativeShadow
import CollatzLean.CollatzSecondLayer3.Legacy.Terminal

/-!
# CollatzSecondLayer3

発散側の正本入口を標準 future-minimum の隣接 actual-return 二局所枝へ移す。

主経路:

`HasUnboundedOddOrbit`
  → consecutive standard future minima
  → determinant sign dichotomy
  → `AdjacentExpandingReturn` または `AdjacentContractingReturn`
  → 二枝排除
  → `¬ HasUnboundedOddOrbit`

この reduction は first crossing の存在を要求しないため、one-sided meander も
Adjacent Expanding Return 側の内部に自動的に含まれる。

`ActualReturn.AssetReconnect` では、ここまでに得た first-crossing / Exact-Late /
sharp affine / valuation 資産を新しい adjacent-return 二枝へ再接続する。

旧 Special C3 / negative-shadow / Constant terminal 群は `Legacy` umbrella の裏で
互換 API として保持する。
-/
