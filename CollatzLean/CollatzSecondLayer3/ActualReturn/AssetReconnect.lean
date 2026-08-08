import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentGeometry
import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentAffineBounds
import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentContractingBridge
import CollatzLean.CollatzSecondLayer3.ActualReturn.AdjacentValuation

/-!
# adjacent-return 資産再接続パッケージ

新しい adjacent-return 二分岐へ、旧 first-crossing / valuation / sharp affine 資産を
再接続する公開入口。

主な追加内容：

* Adjacent Expanding Return の全 proper prefix expanding
* 両枝共通の proper suffix contracting
* prefix / suffix 由来の sharp affine bounds
* Adjacent Expanding の全 consecutive prefix pair に対する 7/4 bound
* Adjacent Contracting tower から旧 ExactAdjacency / LateNextMinimum tower への復元
* 隣接 future-minimum の `x+1`, `y+1`, `Δ` に対する valuation triangle
-/
