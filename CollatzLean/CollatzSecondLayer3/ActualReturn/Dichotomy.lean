import CollatzLean.CollatzSecondLayer3.ActualReturn.Extraction
import CollatzLean.CollatzSecondLayer3.ActualReturn.EarlyNextMinimum
import CollatzLean.CollatzSecondLayer3.ActualReturn.ExactAdjacency
import CollatzLean.CollatzSecondLayer3.ActualReturn.LateNextMinimumD1
import CollatzLean.CollatzSecondLayer3.ActualReturn.LateNextMinimumHighBlock
import CollatzLean.CollatzSecondLayer3.ActualReturn.MultiHighExcursion

/-!
# 発散反例の actual-return 最終二分岐

`r < p` を well-founded descent に吸収した後、非有界軌道から残る obstruction を

* `r = p` : ExactAdjacencyTowerData
* `p < r` : LateNextMinimumTowerData

の二つだけにする。

このファイルの `ActualReturnDichotomyPrinciple` が、旧 Special C3 / terminal 主経路を
完全に actual-return 主経路へ置換するための reduction theorem target である。
-/

namespace CollatzSecondLayer3

open CollatzCore

/--
最終 reduction target。
非有界軌道は exact-adjacency または late-next-minimum のどちらかを生成する。
-/
def ActualReturnDichotomyPrinciple : Prop :=
  ∀ O : OddOrbit,
    O.Unbounded →
      Nonempty (ExactAdjacencyTowerData O) ∨
        Nonempty (LateNextMinimumTowerData O)

end CollatzSecondLayer3
