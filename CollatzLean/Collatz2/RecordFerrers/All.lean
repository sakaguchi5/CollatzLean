import CollatzLean.Collatz2.RecordFerrers.Core.FixedChordFiber
import CollatzLean.Collatz2.RecordFerrers.Core.ProfileDisplacement
import CollatzLean.Collatz2.RecordFerrers.Lattice.FerrersFiber
import CollatzLean.Collatz2.RecordFerrers.Lattice.FirstCrossingLattice
import CollatzLean.Collatz2.RecordFerrers.Lattice.WeightedArea
import CollatzLean.Collatz2.RecordFerrers.Record.RecordBlock
import CollatzLean.Collatz2.RecordFerrers.Record.RecordDecomposition
import CollatzLean.Collatz2.RecordFerrers.Record.Skeleton
import CollatzLean.Collatz2.RecordFerrers.Record.RecordWalls

import CollatzLean.Collatz2.RecordFerrers.Deformation.IntervalTransfer
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockReplacement
import CollatzLean.Collatz2.RecordFerrers.Deformation.SplitMerge
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockPermutation

import CollatzLean.Collatz2.RecordFerrers.Factorization.RecordFerrersFactorization
import CollatzLean.Collatz2.RecordFerrers.Factorization.InitialAnchorFirstCrossing
import CollatzLean.Collatz2.RecordFerrers.Factorization.RecordInverse
import CollatzLean.Collatz2.RecordFerrers.Factorization.PrimitiveReducedInverse
import CollatzLean.Collatz2.RecordFerrers.Factorization.BlockFerrersDeficit

import CollatzLean.Collatz2.RecordFerrers.Reconstruction.FerrersReconstruction
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.LocalTranslationSet
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.InformationBoundary

-- RF-A+1 ... RF-A+4: specialist-theory completion before Phase B migration.
import CollatzLean.Collatz2.RecordFerrers.Extensions.PublicAPI
import CollatzLean.Collatz2.RecordFerrers.Record.Canonicality
import CollatzLean.Collatz2.RecordFerrers.Lattice.MetricCompletion
import CollatzLean.Collatz2.RecordFerrers.Lattice.WeightedPotential
-- RF-A+5 ... RF-A+8: carry statistics, permutation symmetry,
-- H-independent FirstCrossing geometry, and lossless local translation coordinates.
import CollatzLean.Collatz2.RecordFerrers.Record.CarryStatistics
import CollatzLean.Collatz2.RecordFerrers.Deformation.InteriorPermutation
import CollatzLean.Collatz2.RecordFerrers.Lattice.UniversalFirstCrossingFiber
import CollatzLean.Collatz2.RecordFerrers.Reconstruction.TranslationCoordinates

-- RF-B0 ... RF-B4: 既存数学から得る制約を、どの情報からどこまで戻せるかを
-- 明示する輸送基盤と、FirstCrossing の整数座標化。
import CollatzLean.Collatz2.RecordFerrers.Transport.Certificates
import CollatzLean.Collatz2.RecordFerrers.Transport.InformationLedger
import CollatzLean.Collatz2.RecordFerrers.Lattice.PrefixCoordinates
import CollatzLean.Collatz2.RecordFerrers.Lattice.ClearanceSlack
import CollatzLean.Collatz2.RecordFerrers.Lattice.PrefixPolytope


/-!
# Record–Ferrers Phase A umbrella (pre-record stage)

既存ファイルを変更しない add-only shadow layer。

順序:

`FixedChordFiber`
  → `ProfileDisplacement`
  → `FerrersFiber`
  → `FirstCrossingLattice`
  → `WeightedArea`

record point / record block / skeleton / deformation specializations は次段で追加する。
-/

/-!
# Record–Ferrers Phase A complete umbrella

既存ファイルを move / rewrite せずに作る add-only specialist layer の完成入口。

pre-record:
`FixedChordFiber -> ProfileDisplacement -> FerrersFiber -> FirstCrossingLattice -> WeightedArea`

record:
`RecordBlock -> RecordDecomposition -> Skeleton -> RecordWalls`

deformation:
`IntervalTransfer -> BlockReplacement -> SplitMerge -> BlockPermutation`

final:
`Factorization (forward + generic inverse + primitive/reduced inverse) -> Reconstruction`

既存 `Collatz2.RecordFerrers` facade や `Collatz2.lean` の import 切替は Phase B で行う。
-/


/-!
# Record–Ferrers RF-A+1 ... RF-A+4 extension

Phase B の import migration より前に、専門層内部で以下を完成させる。

* public API extraction
* canonical record length / skeleton theory
* distributive Ferrers lattice + metric / unit-chain geometry
* weighted affine potential / bottom-top extremal theory
-/


/-!
# Record–Ferrers RF-A+5 ... RF-A+8 extension

* RF-A+5: arbitrary carry statistics / zero-carry telescope / permutation invariant
* RF-A+6: arbitrary interior `List.Perm` symmetry and contextual affine exchange law
* RF-A+7: universal H-independent FirstCrossing fiber and terminal-depth chord shear
* RF-A+8: local decoration `≃` local translation spectrum and global `(length,B)` coordinates
-/


/-!
# Record–Ferrers RF-B0 ... RF-B4

既存数学を取り込む前に、制約を Collatz 側へ戻すための受け皿を整える。

* RF-B0: 性質決定・数値決定・必要条件・完全翻訳を区別する証明書語彙
* RF-B1: Phase A までに得た情報境界を証明書として台帳化
* RF-B2: Ferrers 図形と累積整数座標の exact 同値
* RF-B3: critical clearance と整数上限制約の余裕の exact 同一視
* RF-B4: universal FirstCrossing object と臨界上限制約つき整数点の exact 同値

この段階では外部の多面体定理そのものは仮定しない。
後続段階では RF-B4 の整数点空間を入口として、既存の整数幾何・行列式制約を接続する。
-/
