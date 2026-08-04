import CollatzLean.CollatzSecondLayer.SynchronizationTransport
import CollatzLean.CollatzSecondLayer.RotationNormalization

/-!
# record block圧縮とrotation-drift staircase

最初の浅い2進差と、それより一段以上深い残余差を足しても、全体のexact深さは
最初の深さに等しい。この有限整数補題をrecord block圧縮の核として証明する。

また同期語が`W_next = W ++ E`と入れ子になった隣接rotationについて、
`E`が現在rotation終点から次rotation開始点へのactual runになることを証明する。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- exact深さ`d`の数に`d+1`以上深い数を加えてもexact深さは`d`。 -/
theorem exactTwoFactor_add_deeper
    {a b d u v : ℕ}
    (ha : ExactTwoFactor a d u)
    (hb : b = 2 ^ (d + 1) * v) :
    ExactTwoFactor (a + b) d (u + 2 * v) := by
  rcases ha with ⟨haeq, hu⟩
  constructor
  · rw [haeq, hb, pow_succ]
    ring
  · rcases hu with ⟨k, hk⟩
    refine ⟨k + v, ?_⟩
    rw [hk]
    ring

/--
二つの増加差`middle-lower`と`upper-middle`を連結する。
後半差が一段深ければ、全差のexact深さは前半差と同じ。
-/
theorem exactTwoFactor_interval_compress
    {lower middle upper d u v : ℕ}
    (hlm : lower ≤ middle)
    (hmu : middle ≤ upper)
    (hfirst : ExactTwoFactor (middle - lower) d u)
    (hrest : upper - middle = 2 ^ (d + 1) * v) :
    ExactTwoFactor (upper - lower) d (u + 2 * v) := by
  have hsum :
      upper - lower = (middle - lower) + (upper - middle) := by
    omega
  rw [hsum]
  exact exactTwoFactor_add_deeper hfirst hrest

/-- record block圧縮で保存すべき有限整数データ。 -/
structure RecordBlockCompressionData where
  lower : ℕ
  firstUpper : ℕ
  finalUpper : ℕ
  depth : ℕ
  firstOddPart : ℕ
  deeperQuotient : ℕ
  lower_le_first : lower ≤ firstUpper
  first_le_final : firstUpper ≤ finalUpper
  firstExact :
    ExactTwoFactor (firstUpper - lower) depth firstOddPart
  remainderDeeper :
    finalUpper - firstUpper = 2 ^ (depth + 1) * deeperQuotient

namespace RecordBlockCompressionData

/-- 圧縮後の全差も最初のexact深さを持つ。 -/
theorem totalExact (D : RecordBlockCompressionData) :
    ExactTwoFactor
      (D.finalUpper - D.lower)
      D.depth
      (D.firstOddPart + 2 * D.deeperQuotient) :=
  exactTwoFactor_interval_compress
    D.lower_le_first D.first_le_final
    D.firstExact D.remainderDeeper

end RecordBlockCompressionData

/--
二つのrotationが隣接し、次同期語が現在同期語へ非空語を追加したもの。
-/
structure NestedAdjacentRotationData where
  current : RotationNormalizedData
  next : RotationNormalizedData
  driftWord : ExpWord
  adjacentStart : current.upperStart = next.lowerStart
  synchronizationExtension :
    next.W = current.W ++ driftWord
  drift_nonempty : driftWord ≠ []

namespace NestedAdjacentRotationData

/--
同期語の入れ子から、現在rotation終点から次rotation開始点へのdrift runを得る。
-/
theorem driftRun (D : NestedAdjacentRotationData) :
    Runs D.driftWord
      D.current.rotatedFinish
      D.next.rotatedStart := by
  have hnext :
      Runs (D.current.W ++ D.driftWord)
        D.current.upperStart
        D.next.rotatedStart := by
    rw [← D.synchronizationExtension, D.adjacentStart]
    exact D.next.lowerPrefixRun
  obtain ⟨middle, hprefix, hdrift⟩ :=
    ExpWord.Runs.split_append hnext
  have hmiddle :
      middle = D.current.rotatedFinish :=
    hprefix.end_unique D.current.upperPrefixRun
  subst middle
  exact hdrift

end NestedAdjacentRotationData

/-- staircaseの一段`X --Q--> Z --E--> X'`。 -/
structure RotationDriftStepData where
  rotation : RotationNormalizedData
  nextRotation : RotationNormalizedData
  driftWord : ExpWord
  rotationRun :
    Runs rotation.rotatedWord
      rotation.rotatedStart rotation.rotatedFinish
  driftRun :
    Runs driftWord
      rotation.rotatedFinish nextRotation.rotatedStart
  drift_nonempty : driftWord ≠ []

/-- nested adjacent rotationからstaircase一段を構成する。 -/
def RotationDriftStepData.ofNested
    (D : NestedAdjacentRotationData) : RotationDriftStepData where
  rotation := D.current
  nextRotation := D.next
  driftWord := D.driftWord
  rotationRun := D.current.toRotationSourceData.rotatedRun
  driftRun := D.driftRun
  drift_nonempty := D.drift_nonempty

/-- 無限rotation-drift staircase。 -/
structure RotationDriftStaircaseData where
  rotation : ℕ → RotationNormalizedData
  driftWord : ℕ → ExpWord
  drift_nonempty : ∀ j : ℕ, driftWord j ≠ []
  driftRun : ∀ j : ℕ,
    Runs (driftWord j)
      (rotation j).rotatedFinish
      (rotation (j + 1)).rotatedStart
  fixedDepth : ℕ
  depth_eq : ∀ j : ℕ, (rotation j).depth = fixedDepth

namespace RotationDriftStaircaseData

/-- staircaseの第`j`段。 -/
def step (D : RotationDriftStaircaseData) (j : ℕ) :
    RotationDriftStepData where
  rotation := D.rotation j
  nextRotation := D.rotation (j + 1)
  driftWord := D.driftWord j
  rotationRun := (D.rotation j).toRotationSourceData.rotatedRun
  driftRun := D.driftRun j
  drift_nonempty := D.drift_nonempty j

end RotationDriftStaircaseData

/--
bounded-depth long-sync rotation列からrecord blockを選び、固定depthのstaircaseへ
圧縮できるという、次段階の明示的接続原理。

この原理に残る作業は、record添字選択、block内のdeeper differenceの有限和、
同期語の入れ子`W_next = W ++ E`の三点である。
-/
def RecordBlockCompressionPrinciple : Prop :=
  ∀ O : OddOrbit,
  ∀ S : CoherentC3CylinderSequence O,
  ∀ C : InfiniteOrderedTerminalChain S,
  BoundedDepthLongSyncRotationData C →
    Nonempty RotationDriftStaircaseData

/-- rotation-drift staircaseが存在すること。 -/
def HasRotationDriftStaircase : Prop :=
  Nonempty RotationDriftStaircaseData

end CollatzSecondLayer
