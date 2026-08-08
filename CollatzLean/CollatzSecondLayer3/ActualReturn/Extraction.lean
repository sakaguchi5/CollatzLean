import CollatzLean.CollatzSecondLayer3.ActualReturn.State
import CollatzLean.CollatzSecondLayer3.SourcePreservingSpecialC3Reduction
import CollatzLean.CollatzSecondLayer3.MeanderAbsorption

/-!
# legacy obstruction から actual-return state への extraction bridge

meander / Special C3 / normalization の生成履歴を最終 API から隠し、
標準 future-minimum 上の arbitrarily long first-crossing tower だけを取り出す。

この bridge が証明されれば、以後の主証明は actual orbit のみを参照できる。
-/

namespace CollatzSecondLayer3

open CollatzCore

/--
非有界軌道から標準 future-minimum actual-return tower を抽出できる、という
リファクタ後の唯一の legacy-to-actual bridge。
-/
def ActualReturnExtractionPrinciple : Prop :=
  ∀ O : OddOrbit,
    O.Unbounded → Nonempty (StandardFutureMinimumReturnTowerData O)

end CollatzSecondLayer3
