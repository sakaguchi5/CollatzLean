import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationBridge
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationCanonicity
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.DeletionPotentialCocycle
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BooleanFamilyCanonicity
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationCoordinates
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationReconstruction

/-!
# Record–Ferrers Perturbation Bridge

`Perturbation/All.lean` は P01--P35 の純粋な摂動理論だけを束ねたままにする。
この `Bridge/All.lean` は、その完成済み Perturbation 層を actual arithmetic /
decoration 側へ接続するファイルだけを集約するための独立入口である。

現在の Bridge 層では、

* actual source → canonical flat top の arithmetic decoration canonicity
* canonical Boolean deletion family 上の path-independent affine cocycle
* Boolean family / flat geometry / arithmetic deletion system 全体の
  RecordDecomposition-independence
* actual record decoration の canonical local translation coordinates と、
  scalar `decorationGap` の coordinate reconstruction
* fine arithmetic coordinate vector から actual source 全体を一意に戻す
  lossless reconstruction

までを束ねる。
-/
