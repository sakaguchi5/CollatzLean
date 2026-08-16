import CollatzLean.Collatz2.Core.BoundaryForm
import CollatzLean.Collatz2.Core.BlockAffineFactorization

import CollatzLean.Collatz2.Geometry.CriticalProfile
import CollatzLean.Collatz2.Geometry.IntegerFerrersDeficit
import CollatzLean.Collatz2.Geometry.CriticalCarry
import CollatzLean.Collatz2.Geometry.MinimalCrossingBlock
import CollatzLean.Collatz2.Geometry.RecordDecomposition
import CollatzLean.Collatz2.Geometry.RecordFerrersFactorization
import CollatzLean.Collatz2.Geometry.PrimitiveReducedRecordInverse
import CollatzLean.Collatz2.Geometry.FerrersReconstruction
import CollatzLean.Collatz2.Geometry.LocalTranslationSet
import CollatzLean.Collatz2.Geometry.BlockFerrersDeficit
import CollatzLean.Collatz2.Geometry.InformationBoundary

import CollatzLean.Collatz2.Mountain.RecordBridge

set_option linter.style.header false

/-!
# Collatz2 Record/Ferrers general layer

record / Ferrers / affine micro--macro factorization の current-A 非依存 API をまとめる入口。
current A への接着は `Canonical.EndpointFloorRecordFactorizationBridge` 側に置く。
-/
