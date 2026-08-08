import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentState
import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentExpandingReturn
import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentContractingReturn
import CollatzLean.CollatzSecondLayer3.ActualReturn.Valuation

/-!
# compatibility shim: actual-return 旧入口

発散側 actual-return の正本は `CollatzSecondLayer3/ActualReturn/` へ移動した。
現在の正本局所状態は first crossing ではなく標準 future-minimum の隣接 return であり、

* Adjacent Expanding Return
* Adjacent Contracting Return

の二枝を公開する。

旧 first-crossing arithmetic / valuation API は局所補題供給源として引き続き保持する。
新規コードでは `CollatzLean.CollatzSecondLayer3.ActualReturn.Main` または
必要な個別モジュールを直接 import する。
-/
