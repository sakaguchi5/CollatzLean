import CollatzLean.Collatz3.Experimental.UnitCarryRoof
import CollatzLean.Collatz3.Experimental.RoofPathExact
import CollatzLean.Collatz3.Experimental.CarryCocycle
import CollatzLean.Collatz3.Experimental.RecordCarryBudget

set_option linter.style.header false
/-!
# Collatz3 mathematical experiments

Collatz3 全面書き換え前に、一般化候補を現行本体から隔離して検証するための import 入口。

現段階では次だけを扱う。

1. 0/1-carry を持つ一般整数値屋根、
2. その屋根から導く strict chord inequality、
3. 一般 roof path 上の local failure exact law、
4. terminal minimality exact law。

この層は現行 `Critical` / `Ferrers` / `Semantics` を import しない。
-/
