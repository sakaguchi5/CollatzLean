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
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationCriticalSubshape
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationDeletionSystem
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.GlobalLocalDecorationDeletion
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.DecorationIntervalSkeletonPreservation
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ProperLocalDecorationSupport
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.FixedSkeletonDecorationAssembly
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.FixedSkeletonDecorationEquivalence
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalAreaProduct
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ProductDecorationDeletionSystem

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
* signed defect evaluator を RecordDecomposition 自体に付随する自然数 local Ferrers weighted area
  へ完全に置換し、`decorationGap = 2 * localWeightedDecorationArea` を得る
  local area decomposition
* actual → canonical flat top → absolute bottom の二段階 positive normalization と、
  finite / terminating / confluent Boolean deletion、path-independent arithmetic cocycle、
  lossless source separation を一つに束ねる arithmetic decorated deletion system
* positive local decoration を universal critical Ferrers subshape と exact に同一視し、
  Ferrers interval の one-cell unit-chain existence を与える local critical-subshape layer
* local decoration space 上で zero critical shape を唯一の normal form とする
  terminating / joinable one-cell deletion system
* actual fixed fiber 上で source → canonical flat top を genuine one-cell Ferrers deletions として
  実現し、任意 trace cost を `decorationGap = 2 * localWeightedDecorationArea` と同定する
  global local-decoration deletion layer
* actual→flat-top decoration interval の全中間点が元 source と同じ canonical record
  length skeleton を持つことを閉じる decoration-interval skeleton preservation
* one-cell edge の唯一 changed Ferrers column を抽出し、その column を strict interior に持つ
  genuine canonical record block 内へ `BlockReplacement` support を縮める proper local support
* fixed genuine record skeleton の各 `LocalDecoration` を mutually independently 選び、
  chosen block list を exact に保った genuine FirstCrossing / RecordDecomposition へ戻す
  fixed-skeleton decoration assembly
* fixed-skeleton actual source space 自体を `LocalDecorationTuple D.lengths` と exact に同一視し、
  independent assembly を state-space product equivalence に昇格する fixed-skeleton equivalence
* 各 local decoration を realizable Ferrers-area spectrum point と exact に同一視し、
  fixed-skeleton actual state space を local-area dependent product へ移すとともに、
  product weighted area を既存 `localWeightedDecorationArea` / `decorationGap` と同定する
  local-area product layer
* local one-cell rewrite を fixed skeleton 全体の asynchronous product rewrite へ持ち上げ、
  reachability の componentwise characterization、termination、all-flat unique normal form、
  joinability、weighted-area strict descent を閉じ、その dynamics を actual fixed-skeleton
  state space へ exact transport する product decoration deletion system

までを束ねる。
-/
