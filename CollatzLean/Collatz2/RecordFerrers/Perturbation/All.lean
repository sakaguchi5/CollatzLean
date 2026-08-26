import CollatzLean.Collatz2.RecordFerrers.Perturbation.P01BoundaryExcess
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P02BoundaryExcessRecurrence
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P03BoundaryExcessClosedForm
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P04CarryBoundaryCharacterization
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P05SpliceLocality
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P06FerrersCoordinateLocality
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P07FixedSkeletonDistanceAdditivity
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P08AdjacentTransferCarrySupport
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P09OneBitDefectLaw
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P10PersistentExcess
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P11OldBoundaryDestruction
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P12BoundaryExcessMonotonicity
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P13PermanentOldBoundaryFailure
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P14RoofContactSaturation
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P15CanonicalRepairCut
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P16PrimitiveReducedChristoffelRepair
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P17FirstFundamentalStripReturn
/-!
# Record–Ferrers 摂動理論 1–16

1–11 の fixed-skeleton locality / one-bit defect / old-boundary destruction に続き、
12–16 では defect 後の一般単調性から canonical repair cut、
primitive + reduced における Christoffel floor/mod 条件までをまとめる。

12. boundary excess の一般単調性
13. 正の defect 後は旧 block-aligned boundary へ永久に戻れない
14. roof contact と `displacement = clearance` の exact 同値
15. 最初の roof contact としての canonical repair cut、その一意性
16. primitive + reduced repair の Christoffel floor / remainder 座標化
-/
