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
