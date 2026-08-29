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
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationBundle
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationArithmeticExactness
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationInterfiberMerge
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationCanonicalInterfiberMerge
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationInterfiberMergeExactness
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationInterfiberMergeCoherence
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationCanonicalMergeActualCompatibility
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationCanonicalMergeCompactSupport

/-!
# Record–Ferrers Perturbation Bridge

`Perturbation/All.lean` は P01--P35 の純粋な摂動理論だけを束ねたままにする。
この `Bridge/All.lean` は、その完成済み Perturbation 層を actual arithmetic /
decoration 側へ接続するファイルだけを集約するための独立入口である。

現在の Bridge 層では、

* actual source -> canonical flat top の arithmetic decoration canonicity
* canonical Boolean deletion family 上の path-independent affine cocycle
* Boolean family / flat geometry / arithmetic deletion system 全体の RecordDecomposition-independence
* actual record decoration の canonical local translation coordinates と
  scalar `decorationGap` の reconstruction
* fine arithmetic coordinate vector から actual source 全体を一意に戻す lossless reconstruction
* full `(length,B)` coordinates の nonredundant arithmetic decoration separation
* local decoration gap formula と componentwise positivity
* `decorationGap = 2 * localWeightedDecorationArea` の local area decomposition
* actual -> flat top -> absolute bottom の arithmetic decorated deletion system
* local critical-subshape / local one-cell deletion / global actual one-cell deletion
* decoration interval 全体の skeleton preservation と genuine record-block support
* fixed-skeleton arbitrary local-decoration assembly と exact state-space product equivalence
* local-area product coordinate と product decoration deletion system
* Boolean retained-boundary base 上の dependent `BoundaryDecorationBundle`
* bundle 全域の `affineConst = absoluteBase + bundleTotalExcess` arithmetic exactness
* P27--P29 actual merge engine を任意の下位 boundary fiber へ持ち上げる existence-level inter-fiber layer
* relative flags と local-area product recursionを同期させ、existential target choiceを使わず
  `R -> S` の canonical fiber map を直接定義する canonical inter-fiber merge
* canonical merge の area-vector action と genuine affine loss を exact に読む inter-fiber merge exactness
* canonical downward maps の identity / composition と
  Boolean base diamond を閉じる inter-fiber merge coherence
* P27 compact-support merge の外側 local-area 保存と merged-area zero を canonical area coordinates へ接続し、
  canonical target の area-vector uniqueness と flat-section actual compatibility を閉じる
  canonical merge actual compatibility
* genuine one-boundary canonical merge を P27 の actual flat-interval deformation と同一視し、
  source の隣接二 RecordBlock の外端だけを support に持つ `BlockReplacement` と
  merged local area zero を arbitrary decorated fiber 上で閉じる canonical merge compact support

までを束ねる。
-/
