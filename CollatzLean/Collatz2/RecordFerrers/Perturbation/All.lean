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

/-!
# Record–Ferrers 摂動理論 1–11

固定 skeleton 上の decoration 局所性と、skeleton を動かしたときの
carry defect / persistent excess / record 境界再分割を一つの入口から読み込む。

1. boundary excess
2. 一段 recurrence
3. `Σ (1-carry)` 閉形式
4. carry 条件との同値
5. minimal block splice の局所性
6. block 外の residue / quotient 座標不変性
7. disjoint support の L1 距離加法性
8. adjacent length transfer の raw carry support
9. one-bit defect law
10. excess の後方持続
11. defect 後の旧 record 境界崩壊
-/
