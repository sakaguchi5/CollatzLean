import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationBridge
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationCanonicity
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.DeletionPotentialCocycle
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BooleanFamilyCanonicity
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationCoordinates
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationReconstruction
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecorationSeparation
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationGap
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationPositivity
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationAreaDecomposition
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecoratedDeletionSystem

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
* full `(length,B)` coordinates を canonical flat geometry と pure local `B`-vector に
  exact に分離する nonredundant arithmetic decoration separation
* scalar `decorationGap` を canonical flat baseline に対する local translation defects の
  signed weighted sumへ exact に展開する local decoration gap formula
* flat local baseline を `3^r - 2^r` と同定し、全 local decoration defects の
  componentwise nonnegativity を閉じる local decoration positivity
- signed defect evaluator を RecordDecomposition 自体に付随する自然数 local Ferrers weighted area
  へ完全に置換し、`decorationGap = 2 * localWeightedDecorationArea` を得る
  local area decomposition
- actual → canonical flat top → absolute bottom の二段階 positive normalization と、
  finite / terminating / confluent Boolean deletion、
  path-independent arithmetic cocycle、
  lossless source separation を一つに束ねる
  arithmetic decorated deletion system

までを束ねる。
-/
