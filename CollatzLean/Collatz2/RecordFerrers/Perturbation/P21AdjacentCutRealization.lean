import CollatzLean.Collatz2.RecordFerrers.Perturbation.P20PrimitiveReducedResegmentationExistence
import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockReplacement

/-!
# Record–Ferrers 摂動理論 21: 隣接 cut の actual realization bridge

P08–P10 の `AdjacentLengthTransfer r s r' s'` は、

  r + s = r' + s'

だけを保持する pure skeleton-level object である。
したがって、それ自体は `FiberPoint u -> v` という実際の fixed-chord deformation を
表していない。

本ファイルでは向きを逆にする。

* source `u` に genuine な隣接 interior `RecordBlock` が二つある
* その外側 endpoints を固定した actual `BlockReplacement u v` がある
* target `v` の内部 cut `k` が critical roof に接触する

という actual geometry から、

  r' := k - a
  s' := ((a + r) + s) - k

を読み取り、`AdjacentLengthTransfer r s r' s'` を導出する。

さらに、P09 の一ビット欠陥を actual target block depth へ戻す。
局所 carry `criticalCarry r' s' = 0` なら、候補二分割のうち正確に一方だけが
minimal depth `criticalHeight len + 1` を持ち、もう一方は
`criticalHeight len` に一段だけ浅くなる。

P19 の言葉では、これは target middle cut `k` の左右について
「正確に一方だけが `AdmissibleRecordContact` になる」ことに対応する。

重要: 本ファイルは target の canonical resegmentation を新たに構成しない。
P19–P20 はその target-side existence / canonicality layer として独立のまま使う。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
source の genuine adjacent record pair と、その外側 endpoints を固定した actual deformation、
さらに target の新しい内部 roof cut を一つに束ねる。

`AdjacentLengthTransfer` は field にしない。新しい二長は `k` から読み取り、後で導出する。
-/
structure RealizedAdjacentCutTransfer
    {p H : ℕ}
    (u v : FiberPoint p H)
    (a r s k : ℕ) : Prop where
  leftSource : RecordBlock u a r
  rightSource : RecordBlock u (a + r) s
  outerInterior : (a + r) + s < p
  replacement : BlockReplacement u v a ((a + r) + s)
  newCutInside : a < k ∧ k < (a + r) + s
  newCutRoof : RoofContact v k

namespace RealizedAdjacentCutTransfer

/-- source の左 block は interior。 -/
theorem leftSource_interior
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    a + r < p := by
  exact lt_of_le_of_lt
    (Nat.le_add_right (a + r) s)
    R.outerInterior

/-- source の genuine adjacent pair は P09 の `InteriorPairCarry` を自動的に満たす。 -/
theorem sourceInteriorPairCarry
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    InteriorPairCarry a r s := by
  exact
    ⟨R.leftSource.criticalCarry_eq_one_of_interior R.leftSource_interior,
      R.rightSource.criticalCarry_eq_one_of_interior R.outerInterior⟩

/--
actual deformation の外側 endpoints と target middle cut から読み取った二長は、
source pair と同じ total odd length を持つ。

従って P08 の `AdjacentLengthTransfer` は actual geometry から自動的に得られる。
-/
theorem adjacentLengthTransfer
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    AdjacentLengthTransfer
      r s
      (k - a)
      (((a + r) + s) - k) := by
  constructor
  rcases R.newCutInside with ⟨hAK, hKC⟩
  omega

/-- block replacement は左 outer anchor を固定するので、target でも roof contact が残る。 -/
theorem targetAnchorRoof
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    RoofContact v a := by
  have hEq := R.replacement.height_start
  unfold RoofContact
  rw [← hEq]
  exact R.leftSource.start_roof

/-- source の右 block の endpoint は outer interior roof。 -/
theorem sourceOuterRoof
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    RoofContact u ((a + r) + s) := by
  unfold RoofContact
  exact R.rightSource.next_roof_if_interior R.outerInterior

/-- block replacement は右 outer anchor も固定するので、target でも outer roof が残る。 -/
theorem targetOuterRoof
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    RoofContact v ((a + r) + s) := by
  have hEq := R.replacement.height_stop
  have hSource := R.sourceOuterRoof
  unfold RoofContact at hSource ⊢
  rw [← hEq]
  exact hSource

/--
actual `BlockReplacement` は outer endpoints の height を固定するので、
source の二 block を合わせた total two-depth と、target middle cut `k` で読んだ
候補二区間の total two-depth は exact に一致する。

これは carry defect の有無より前に成立する fixed-chord realization の保存則である。
-/
theorem sourcePairTotalDepth_eq_targetPairTotalDepth
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    twoSteps (blockWord u a r) +
        twoSteps (blockWord u (a + r) s) =
      twoSteps (blockWord v a (k - a)) +
        twoSteps (blockWord v k (((a + r) + s) - k)) := by
  have hU1 := height_add_eq_add_blockDepth u a r
  have hU2 := height_add_eq_add_blockDepth u (a + r) s
  have hV1 := height_add_eq_add_blockDepth v a (k - a)
  have hV2 :=
    height_add_eq_add_blockDepth v k (((a + r) + s) - k)
  have hAK : a + (k - a) = k := by
    exact Nat.add_sub_of_le (Nat.le_of_lt R.newCutInside.1)
  have hKC : k + (((a + r) + s) - k) = (a + r) + s := by
    exact Nat.add_sub_of_le (Nat.le_of_lt R.newCutInside.2)
  have hStart := R.replacement.height_start
  have hStop := R.replacement.height_stop
  rw [hAK] at hV1
  rw [hKC] at hV2
  omega

/--
source whole word が FirstCrossing で、replacement 内部の signed displacement が
source clearance を越えなければ、actual target も FirstCrossing。

P21 の realization packet 自体には FirstCrossing を埋め込まず、安全性を必要な箇所で渡す。
-/
theorem targetFirstCrossing_of_clearance
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k)
    (hFu : FirstCrossing u.word)
    (hSafe :
      ∀ j : ℕ,
        a < j →
        j < (a + r) + s →
        profileDisplacement u v j ≤ criticalDefectInt u j) :
    FirstCrossing v.word := by
  exact R.replacement.preserves_firstCrossing hFu hSafe

/--
左候補区間 `[a,k]` の actual two-depth は、両 endpoint が roof なので
critical height と anchor-relative carry だけで exact に決まる。
-/
theorem leftActualDepth_eq_criticalHeight_add_carry
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    twoSteps (blockWord v a (k - a)) =
      criticalHeight (k - a) + criticalCarry a (k - a) := by
  let len := k - a
  have hEndEq : a + len = k := by
    dsimp [len]
    exact Nat.add_sub_of_le (Nat.le_of_lt R.newCutInside.1)
  have hHeight := height_add_eq_add_blockDepth v a len
  have hCrit := criticalHeight_add_eq a len
  have hA := R.targetAnchorRoof
  have hK := R.newCutRoof
  unfold RoofContact at hA hK
  rw [hEndEq, hA, hK] at hHeight
  rw [hEndEq] at hCrit
  have hEq :
      criticalHeight a +
          twoSteps (blockWord v a len) =
        criticalHeight a +
          (criticalHeight len + criticalCarry a len) := by
    calc
      criticalHeight a +
          twoSteps (blockWord v a len) =
        criticalHeight k := by
          exact hHeight.symm
      _ =
        criticalHeight a +
          (criticalHeight len + criticalCarry a len) := by
          simpa [Nat.add_assoc] using hCrit
  have hDepth :
      twoSteps (blockWord v a len) =
        criticalHeight len + criticalCarry a len :=
    Nat.add_left_cancel hEq
  simpa [len] using hDepth

/--
右候補区間 `[k,c]`, `c=(a+r)+s` の actual two-depth も、
両 endpoint が roof なので local critical height + carry に一致する。
-/
theorem rightActualDepth_eq_criticalHeight_add_carry
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    twoSteps
        (blockWord v k (((a + r) + s) - k)) =
      criticalHeight (((a + r) + s) - k) +
        criticalCarry k (((a + r) + s) - k) := by
  let len := ((a + r) + s) - k
  have hEndEq : k + len = (a + r) + s := by
    dsimp [len]
    exact Nat.add_sub_of_le (Nat.le_of_lt R.newCutInside.2)
  have hHeight := height_add_eq_add_blockDepth v k len
  have hCrit := criticalHeight_add_eq k len
  have hK := R.newCutRoof
  have hC := R.targetOuterRoof
  unfold RoofContact at hK hC
  rw [hEndEq, hK, hC] at hHeight
  rw [hEndEq] at hCrit
  have hEq :
      criticalHeight k +
          twoSteps (blockWord v k len) =
        criticalHeight k +
          (criticalHeight len + criticalCarry k len) := by
    calc
      criticalHeight k +
          twoSteps (blockWord v k len) =
        criticalHeight ((a + r) + s) := by
          exact hHeight.symm
      _ =
        criticalHeight k +
          (criticalHeight len + criticalCarry k len) := by
          simpa [Nat.add_assoc] using hCrit
  have hDepth :
      twoSteps (blockWord v k len) =
        criticalHeight len + criticalCarry k len :=
    Nat.add_left_cancel hEq
  simpa [len] using hDepth

/--
left candidate `a -> k` は、すでに両 endpoint が roof なので、
P19 の admissibility と left anchor-relative carry = 1 が exact に同値。
-/
theorem leftAdmissible_iff_carry_one
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    AdmissibleRecordContact v a k ↔
      criticalCarry a (k - a) = 1 := by
  constructor
  · intro h
    exact h.2.2.2.2
  · intro hCarry
    have hkLt : k < p := lt_trans R.newCutInside.2 R.outerInterior
    exact
      ⟨R.newCutInside.1,
        hkLt,
        R.targetAnchorRoof,
        R.newCutRoof,
        hCarry⟩

/--
right candidate `k -> c` についても、admissibility は right carry = 1 と exact に同値。
-/
theorem rightAdmissible_iff_carry_one
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k) :
    AdmissibleRecordContact v k ((a + r) + s) ↔
      criticalCarry k (((a + r) + s) - k) = 1 := by
  constructor
  · intro h
    exact h.2.2.2.2
  · intro hCarry
    exact
      ⟨R.newCutInside.2,
        R.outerInterior,
        R.newCutRoof,
        R.targetOuterRoof,
        hCarry⟩

/--
P09 の local carry defect を actual target depth へ戻した exact dichotomy。

`criticalCarry r' s' = 0` なら、candidate pair のうち正確に一方だけが
minimal depth `criticalHeight len + 1` を持ち、もう一方は critical height そのもの。
-/
theorem defect_actualDepthDichotomy
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k)
    (hLocal :
      criticalCarry
        (k - a)
        (((a + r) + s) - k) = 0) :
    (twoSteps (blockWord v a (k - a)) =
        criticalHeight (k - a) ∧
      twoSteps (blockWord v k (((a + r) + s) - k)) =
        criticalHeight (((a + r) + s) - k) + 1) ∨
    (twoSteps (blockWord v a (k - a)) =
        criticalHeight (k - a) + 1 ∧
      twoSteps (blockWord v k (((a + r) + s) - k)) =
        criticalHeight (((a + r) + s) - k)) := by
  have hOld := R.sourceInteriorPairCarry
  have T := R.adjacentLengthTransfer
  have hSides :=
    (adjacentTransfer_localCarry_zero_iff_left_or_right_defect hOld T).1 hLocal
  have hLeftDepth := R.leftActualDepth_eq_criticalHeight_add_carry
  have hRightDepth := R.rightActualDepth_eq_criticalHeight_add_carry
  have hAK : a + (k - a) = k := by
    exact Nat.add_sub_of_le (Nat.le_of_lt R.newCutInside.1)
  rcases hSides with hLeft | hRight
  · unfold LeftCarryDefect at hLeft
    have hRightCarry :
        criticalCarry k (((a + r) + s) - k) = 1 := by
      simpa only [hAK] using hLeft.2
    left
    constructor
    · rw [hLeft.1] at hLeftDepth
      simpa using hLeftDepth
    · rw [hRightCarry] at hRightDepth
      exact hRightDepth
  · unfold RightCarryDefect at hRight
    have hRightCarry :
        criticalCarry k (((a + r) + s) - k) = 0 := by
      simpa only [hAK] using hRight.2
    right
    constructor
    · rw [hRight.1] at hLeftDepth
      exact hLeftDepth
    · rw [hRightCarry] at hRightDepth
      simpa using hRightDepth

/--
actual target 上での一ビット欠陥は、candidate middle cut `k` の左右について
正確に一方だけが P19 の `AdmissibleRecordContact` になることを意味する。
-/
theorem defect_admissibleDichotomy
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k)
    (hLocal :
      criticalCarry
        (k - a)
        (((a + r) + s) - k) = 0) :
    (¬ AdmissibleRecordContact v a k ∧
        AdmissibleRecordContact v k ((a + r) + s)) ∨
      (AdmissibleRecordContact v a k ∧
        ¬ AdmissibleRecordContact v k ((a + r) + s)) := by
  have hOld := R.sourceInteriorPairCarry
  have T := R.adjacentLengthTransfer
  have hSides :=
    (adjacentTransfer_localCarry_zero_iff_left_or_right_defect hOld T).1 hLocal
  have hLeftIff := R.leftAdmissible_iff_carry_one
  have hRightIff := R.rightAdmissible_iff_carry_one
  have hAK : a + (k - a) = k := by
    exact Nat.add_sub_of_le (Nat.le_of_lt R.newCutInside.1)
  rcases hSides with hLeft | hRight
  · unfold LeftCarryDefect at hLeft
    have hRightCarry :
        criticalCarry k (((a + r) + s) - k) = 1 := by
      simpa only [hAK] using hLeft.2
    left
    constructor
    · intro hAdm
      have hOne := hLeftIff.1 hAdm
      omega
    · exact hRightIff.2 hRightCarry
  · unfold RightCarryDefect at hRight
    have hRightCarry :
        criticalCarry k (((a + r) + s) - k) = 0 := by
      simpa only [hAK] using hRight.2
    right
    constructor
    · exact hLeftIff.2 hRight.1
    · intro hAdm
      have hOne := hRightIff.1 hAdm
      omega

/--
local carry defect の下では candidate pair の actual total depth は
`criticalHeight (r' + s') + 1` に正確に一致する。

両 candidate をともに minimal depth にすると一段多過ぎるが、
one-bit defect により片側だけが一段浅くなるため fixed total depth が保たれる。
-/
theorem defect_actualTotalDepth_eq_criticalHeight_add_one
    {p H a r s k : ℕ}
    {u v : FiberPoint p H}
    (R : RealizedAdjacentCutTransfer u v a r s k)
    (hLocal :
      criticalCarry
        (k - a)
        (((a + r) + s) - k) = 0) :
    twoSteps (blockWord v a (k - a)) +
        twoSteps (blockWord v k (((a + r) + s) - k)) =
      criticalHeight
          ((k - a) + (((a + r) + s) - k)) + 1 := by
  have hDepths := R.defect_actualDepthDichotomy hLocal
  have hCrit :=
    criticalHeight_add_eq
      (k - a)
      (((a + r) + s) - k)
  rw [hLocal] at hCrit
  rcases hDepths with hLeft | hRight
  · omega
  · omega

end RealizedAdjacentCutTransfer

end RecordFerrers
end Collatz2
