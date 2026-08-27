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
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P18DefectPhaseBridge
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P19AdmissibleRecordContact
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P20PrimitiveReducedResegmentationExistence
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P21AdjacentCutRealization
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P22DefectSplitBestLower
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P23FlexibleAdjacentPairPerturbation
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P24CanonicalInteriorFlexibility
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P25TerminalRigidityAndGlobalDefect
import CollatzLean.Collatz2.RecordFerrers.Perturbation.P26CanonicalAdjacentPairFlexibility

/-!
# Record–Ferrers 摂動理論 1–26

1–11 では fixed-skeleton locality、一ビット欠陥、旧境界破壊を構築する。
12–18 では欠陥後の単調性から幾何学的 repair cut、Christoffel 座標、
fundamental rank strip への最初の復帰、欠陥位相と repair 位相の橋まで進める。

19 では単なる roof contact と genuine record endpoint を分離し、
`RoofContact + anchor-relative carry = 1` を admissible contact とする。
最初の admissible contact が interior RecordBlock を与え、存在しない場合は
terminal absorption が一つの terminal RecordBlock を与える。

20 ではこの target-side の一歩存在定理を残り長さで反復し、primitive + StripReduced
FirstCrossing target が正の roof anchor から genuine RecordDecomposition を持つことを示す。

21 では source の genuine adjacent RecordBlocks と actual BlockReplacement、target middle cut から
P08 の `AdjacentLengthTransfer` を導出する realization bridge を構成する。
さらに P09 の一ビット欠陥を actual block depth と P19 の admissibility dichotomy へ戻す。

22 では outer length の defect split

  criticalCarry x (L-x) = 0

を `log₂ 3` の lower phase record 条件へ exact に翻訳し、
`DefectSplit ⇔ not CriticalLowerBestDenominator` を pure integer arithmetic で証明する。

23 では flexible defect split から二段 plateau Ferrers target を実際に構成する。
この target は actual BlockReplacement、FirstCrossing、P21 one-bit defect を同時に満たし、
P20 canonical resegmentation を通して source と target の record length skeleton が異なることまで示す。

24 では cut 1 以下の critical phase にある canonical anchor 上で、
adjacent interior RecordBlock pair の lower-best rigid branch を pure carry arithmetic で排除する。
従って P22 defect split が自動存在し、primitive + StripReduced + FirstCrossing では
P23 actual perturbation と canonical skeleton change まで自動化される。

25 では P19 complement identity と P20 terminal-depth identity から whole denominator が
strict upper-best phase denominator であることを証明する。これにより terminal rigid pair は `p=3`
にしか残れず、`p>3` の cut-1 canonical RecordDecomposition では terminal を含む全 adjacent pair が
defect split を持つ。

26 では terminal defect split を terminal 専用 two-plateau Ferrers target として actual に実現する。
terminal outer carry=0 と local defect carry=0 から new cut 左右の carry は両方 0 となり、
new cut は roof だが admissible ではない。target では proper admissible contact が消えるため P19 の
terminal absorption が発動し、source `[r,s]` は target `[r+s]` へ exact に merge する。
最後に P24 の interior branch と合わせ、`p>3` の canonical phase 領域では任意の adjacent pair が
actual fixed-chord deformation を持つことを一つの theorem にまとめる。
-/
