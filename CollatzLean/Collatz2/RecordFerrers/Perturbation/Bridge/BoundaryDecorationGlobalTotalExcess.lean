import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationGlobalNormalization

/-!
# Record–Ferrers Perturbation / Global Total Excess

`BoundaryDecorationGlobalNormalization` では、fiber 内の一セル削除と
一つの retained boundary の canonical merge を同じ大域書き換え関係に束ね、

  (retained boundary count, local cell count)

の辞書式順位によって停止性を証明した。

一方、既存の bundle 算術完全性では任意の bundle point `Z` に対して

  affineConst (realization Z)
    = absoluteBase + boundaryDecorationBundleTotalExcess Z

が exact に成立し、さらに `boundaryDecorationBundleTotalExcess` は bundle 全体で単射、
その唯一の零点は absolute bottom である。

本ファイルでは残っていた最後の接続を閉じる。

* fiber one-cell deletion では local weighted area が strict に減る。
* genuine canonical boundary merge は actual Ferrers profile を pointwise に下げる。
* boundary merge の source / target は異なる actual points なので `affineConst` は strict に減る。
* 従って大域的一歩は常に同じ自然数 `boundaryDecorationBundleTotalExcess` を strict に減らす。

その結果、dependent boundary-decoration bundle 全体は

  Z |-> boundaryDecorationBundleTotalExcess Z : ℕ

という一つの情報損失のない自然数座標へ埋め込まれ、全大域辺はその自然数の strict downward
orientation と両立する。

さらに endpoint difference を大域 loss として定義し、有限到達に沿う加法 cocycle と、
absolute bottom までの全 loss が source total excess そのものになることまで閉じる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. Ferrers inclusion と affineConst の strict 単調性 -/

namespace FiberPoint

/--
同じ fixed chord 上で Ferrers profile が pointwise に下がり、点自体も異なれば、
`affineConst` も strict に下がる。

既存 `affineConst = baseAffineConst + weightedArea` と
fixed-fiber `affineConst` の lossless 性を組み合わせた短い API。
-/
theorem affineConst_lt_of_ferrersLe_of_ne
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hxy : x.FerrersLe y)
    (hne : x ≠ y) :
    affineConst x.word < affineConst y.word := by
  change x.toFerrersShape.Le y.toFerrersShape at hxy
  have hArea :
      weightedArea x.toFerrersShape ≤
        weightedArea y.toFerrersShape :=
    weightedArea_mono hxy
  have hLe :
      affineConst x.word ≤ affineConst y.word := by
    rw [affineConst_eq_base_add_weightedArea x,
        affineConst_eq_base_add_weightedArea y]
    exact Nat.add_le_add_left hArea _
  have hAffineNe :
      affineConst x.word ≠ affineConst y.word := by
    intro hEq
    exact hne (fiberPoint_eq_of_same_affineConst hEq)
  omega

end FiberPoint

/-! ## 2. compact-support flat merge は source Ferrers profile 以下 -/

/--
一つの source RecordBlock の roof anchor `a` から始まり、
open interval `(a,(a+r)+s)` だけを置換し、target 側で長さ `r+s` の merged RecordBlock が
local area 0 になっているなら、target Ferrers profile は source profile 以下。

area 0 の genuine local decoration は唯一の flat local decorationなので、merged interval 内の
target excess は左端 roof の `criticalExcess a` に固定される。
source excess は nondecreasing なので、その値以上に留まる。
区間外は `BlockReplacement` により exact に不変。
-/
theorem ferrersLe_of_flat_merged_recordBlock
    {p H a r s : ℕ}
    {x y : FiberPoint p H}
    (hSource : RecordBlock x a r)
    (hRep : BlockReplacement x y a ((a + r) + s))
    (hMerged : RecordBlock y a (r + s))
    (hAreaZero :
      localDecorationArea (blockWord y a (r + s)) = 0) :
    y.FerrersLe x := by
  unfold FiberPoint.FerrersLe
  intro i
  change y.excessAt i.1 ≤ x.excessAt i.1
  by_cases hLeft : i.1 ≤ a
  · have hDisp :=
      hRep.outside i.1 (Nat.le_of_lt i.isLt) (Or.inl hLeft)
    have hHeight : y.height i.1 = x.height i.1 := by
      unfold profileDisplacement at hDisp
      exact_mod_cast (sub_eq_zero.mp hDisp)
    unfold FiberPoint.excessAt
    rw [hHeight]
  · have hAi : a < i.1 := by omega
    by_cases hRight : (a + r) + s ≤ i.1
    · have hDisp :=
        hRep.outside i.1 (Nat.le_of_lt i.isLt) (Or.inr hRight)
      have hHeight : y.height i.1 = x.height i.1 := by
        unfold profileDisplacement at hDisp
        exact_mod_cast (sub_eq_zero.mp hDisp)
      unfold FiberPoint.excessAt
      rw [hHeight]
    · have hInside : i.1 < (a + r) + s := by omega
      have hLenPos : 0 < r + s := hMerged.length_pos
      let L : LocalDecoration (r + s) := {
        word := blockWord y a (r + s)
        validMinimal := {
          toMinimalBlock := hMerged.minimal
          valid := RecordBlock.local_valid
        }
        length_eq := hMerged.local_oddSteps
      }
      have hAreaL : localDecorationArea L.word = 0 := by
        simpa [L] using hAreaZero
      have hFlatArea :
          localDecorationArea
            (localFlatDecoration (r + s) hLenPos).word = 0 :=
        localDecorationArea_localFlatDecoration_eq_zero
          (r + s) hLenPos
      have hLFlat :
          L = localFlatDecoration (r + s) hLenPos :=
        LocalDecoration.eq_of_localDecorationArea_eq
          (hAreaL.trans hFlatArea.symm)
      have hjLt : i.1 - a < r + s := by
        omega
      have hLocalZero :
          L.toFiberPoint.excessAt (i.1 - a) = 0 := by
        have hShape :
            L.ferrersShape = FerrersShape.zero (r + s) := by
          rw [hLFlat]
          exact localFlatDecoration_ferrersShape
            (r + s) hLenPos
        change
          L.ferrersShape.column ⟨i.1 - a, hjLt⟩ = 0
        rw [hShape]
        rfl
      have hIndex : a + (i.1 - a) = i.1 :=
        Nat.add_sub_of_le (Nat.le_of_lt hAi)
      have hY :=
        hMerged.globalExcess_eq_criticalExcess_add_localExcess
          (j := i.1 - a) (Nat.le_of_lt hjLt)
      change
        y.excessAt (a + (i.1 - a)) =
          criticalExcess a + L.toFiberPoint.excessAt (i.1 - a)
        at hY
      rw [hIndex, hLocalZero, Nat.add_zero] at hY
      have hRoof : x.excessAt a = criticalExcess a :=
        excessAt_eq_criticalExcess_of_roof hSource.start_roof
      have hMono : x.excessAt a ≤ x.excessAt i.1 :=
        x.excess_mono
          (Nat.le_of_lt hAi)
          (Nat.le_of_lt i.isLt)
      rw [hRoof] at hMono
      rw [hY]
      exact hMono

/-! ## 3. genuine canonical boundary merge は actual Ferrers profile を strict に下げる -/

/--
genuine one-boundary canonical actual merge の target は source Ferrers profile 以下。

`BoundaryDecorationCanonicalMergeCompactSupport` の主定理が与える
source adjacent pair、compact replacement、merged area zero を前節の一般補題へ渡す。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_ferrersLe_source
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    FiberPoint.FerrersLe
      (boundaryDecorationActualCanonicalInterfiberMerge
        P hPrimitive hReduced u D R b X).1
      X.1 := by
  obtain ⟨a, r, s, hLeft, _hRight, hRep, hMerged, hArea⟩ :=
    boundaryDecorationActualCanonicalInterfiberMerge_compactSupport
      P hPrimitive hReduced u D R b hb X
  exact ferrersLe_of_flat_merged_recordBlock
    hLeft hRep hMerged hArea

/--
genuine one-boundary canonical actual merge は source point と同一ではない。

もし underlying fixed-fiber point が同じなら、actual bundle の point-injectivity により
base boundary pattern まで同一になる。しかし genuine deletion は retained boundary count を
exact に一つ減らすので矛盾。
-/
theorem boundaryDecorationActualCanonicalInterfiberMerge_ne_source
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    (boundaryDecorationActualCanonicalInterfiberMerge
        P hPrimitive hReduced u D R b X).1 ≠ X.1 := by
  intro hEq
  let Y := boundaryDecorationActualCanonicalInterfiberMerge
    P hPrimitive hReduced u D R b X
  have hBundle :
      (⟨eraseRetainedBoundary R b, Y⟩ :
          BoundaryDecorationActualBundle
            P hPrimitive hReduced u D) =
        ⟨R, X⟩ := by
    apply boundaryDecorationActualBundle_point_injective
      P hPrimitive hReduced u D
    simpa [Y] using hEq
  have hBase : eraseRetainedBoundary R b = R :=
    congrArg (fun Z => Z.1) hBundle
  have hCount := retainedBoundaryCount_erase_add_one R b hb
  rw [hBase] at hCount
  omega

/-- genuine canonical boundary merge では actual `affineConst` が strict に減る。 -/
theorem boundaryDecorationActualCanonicalInterfiberMerge_affineConst_lt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true)
    (X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R) :
    affineConst
        (boundaryDecorationActualCanonicalInterfiberMerge
          P hPrimitive hReduced u D R b X).1.word <
      affineConst X.1.word := by
  exact FiberPoint.affineConst_lt_of_ferrersLe_of_ne
    (boundaryDecorationActualCanonicalInterfiberMerge_ferrersLe_source
      P hPrimitive hReduced u D R b hb X)
    (boundaryDecorationActualCanonicalInterfiberMerge_ne_source
      P hPrimitive hReduced u D R b hb X)

/-! ## 4. 二種類の global edge は同じ TotalExcess を strict に下げる -/

namespace LocalAreaTupleCellDeletion

/--
area-product one-cell deletion は weighted area を strict に下げる。
-/
theorem weightedArea_lt
    {rs : List ℕ}
    {A B : LocalAreaTuple rs}
    (h : LocalAreaTupleCellDeletion A B) :
    B.weightedArea < A.weightedArea := by
  have hRaw :=
    h.toDecorationTuple.weightedArea_lt
  have hB :
      B.toLocalDecorationTuple.weightedArea =
        B.weightedArea := by
    rw [
      LocalDecorationTuple.weightedArea_eq_toLocalAreaTuple_weightedArea,
      LocalAreaTuple.toLocalDecorationTuple_toLocalAreaTuple
    ]
  have hA :
      A.toLocalDecorationTuple.weightedArea =
        A.weightedArea := by
    rw [
      LocalDecorationTuple.weightedArea_eq_toLocalAreaTuple_weightedArea,
      LocalAreaTuple.toLocalDecorationTuple_toLocalAreaTuple
    ]
  rw [hB, hA] at hRaw
  exact hRaw

end LocalAreaTupleCellDeletion

/--
同じ retained-boundary base の二つの fiber point では、
weighted area の strict decrease は bundle total excess の strict decrease を与える。

boundary residual は共通なので、比較を担うのは weighted area だけ。
-/
theorem boundaryDecorationBundleTotalExcess_lt_of_weightedArea_lt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    {A B : BoundaryDecorationFiber D R}
    (hWeighted : B.weightedArea < A.weightedArea) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D ⟨R, B⟩ <
      boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D ⟨R, A⟩ := by
  unfold boundaryDecorationBundleTotalExcess
  change
    boundaryResidualToBottom
          P hPrimitive hReduced u D R
        + 2 * B.weightedArea <
      boundaryResidualToBottom
          P hPrimitive hReduced u D R
        + 2 * A.weightedArea
  omega

/-- fixed-base fiber one-cell deletion は bundle total excess を strict に下げる。 -/
theorem boundaryDecorationFiberCellDeletion_totalExcess_lt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    {A B : BoundaryDecorationFiber D R}
    (hAB : BoundaryDecorationFiberCellDeletion
      P hPrimitive hReduced u D R A B) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D ⟨R, B⟩ <
      boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D ⟨R, A⟩ := by
  have hArea : LocalAreaTupleCellDeletion A B :=
    (boundaryDecorationFiberCellDeletion_iff_areaTupleCellDeletion
      P hPrimitive hReduced u D R A B).1 hAB
  exact
    boundaryDecorationBundleTotalExcess_lt_of_weightedArea_lt
      P hPrimitive hReduced u D R
      hArea.weightedArea_lt

/-- genuine one-boundary canonical merge は bundle total excess を strict に下げる。 -/
theorem boundaryDecorationCanonicalInterfiberMerge_totalExcess_lt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true)
    (A : BoundaryDecorationFiber D R) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D
        ⟨eraseRetainedBoundary R b,
          boundaryDecorationCanonicalInterfiberMerge D R b A⟩ <
      boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D ⟨R, A⟩ := by
  let X : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D R :=
    (boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R).symm A
  let Y : BoundaryDecorationActualFiber
      P hPrimitive hReduced u D (eraseRetainedBoundary R b) :=
    boundaryDecorationActualCanonicalInterfiberMerge
      P hPrimitive hReduced u D R b X
  have hAffine : affineConst Y.1.word < affineConst X.1.word := by
    dsimp [Y]
    exact boundaryDecorationActualCanonicalInterfiberMerge_affineConst_lt
      P hPrimitive hReduced u D R b hb X
  have hXCoord :
      boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D R X = A := by
    dsimp [X]
    exact (boundaryDecorationFiberEquiv
      P hPrimitive hReduced u D R).apply_symm_apply A
  have hYCoord :
      boundaryDecorationFiberEquiv
          P hPrimitive hReduced u D
          (eraseRetainedBoundary R b) Y =
        boundaryDecorationCanonicalInterfiberMerge D R b A := by
    dsimp [Y]
    rw [boundaryDecorationActualCanonicalInterfiberMerge_coordinate]
    exact congrArg
      (boundaryDecorationCanonicalInterfiberMerge D R b)
      hXCoord
  have hX :=
    boundaryDecorationActualFiber_affineConst_eq_absoluteBase_add_totalExcess
      P hPrimitive hReduced u D R X
  have hY :=
    boundaryDecorationActualFiber_affineConst_eq_absoluteBase_add_totalExcess
      P hPrimitive hReduced u D
      (eraseRetainedBoundary R b) Y
  rw [hXCoord] at hX
  rw [hYCoord] at hY
  have hTotal :
      boundaryResidualToBottom
          P hPrimitive hReduced u D
          (eraseRetainedBoundary R b) +
        2 * LocalAreaTuple.weightedArea
          (boundaryDecorationCanonicalInterfiberMerge D R b A) <
      boundaryResidualToBottom
          P hPrimitive hReduced u D R +
        2 * LocalAreaTuple.weightedArea A := by
    rw [hY, hX] at hAffine
    omega
  unfold boundaryDecorationBundleTotalExcess
  change
    boundaryResidualToBottom
        P hPrimitive hReduced u D
        (eraseRetainedBoundary R b) +
      2 * LocalAreaTuple.weightedArea
        (boundaryDecorationCanonicalInterfiberMerge D R b A) <
    boundaryResidualToBottom
        P hPrimitive hReduced u D R +
      2 * LocalAreaTuple.weightedArea A
  exact hTotal

/--
## Global Single-Scalar Descent

fiber one-cell deletion と genuine canonical boundary merge のどちらを選んでも、
同じ自然数 `boundaryDecorationBundleTotalExcess` が strict に減る。
-/
theorem BoundaryDecorationGlobalStep.totalExcess_lt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W : BoundaryDecorationBundle D}
    (h : BoundaryDecorationGlobalStep
      P hPrimitive hReduced u D Z W) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D W <
      boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D Z := by
  cases h with
  | @fiber R A B hAB =>
      exact boundaryDecorationFiberCellDeletion_totalExcess_lt
        P hPrimitive hReduced u D R hAB
  | @boundary R b hb A =>
      exact boundaryDecorationCanonicalInterfiberMerge_totalExcess_lt
        P hPrimitive hReduced u D R b hb A

/--
大域書き換えは辞書式順位を使わず、`TotalExcess : Bundle -> ℕ` 一個だけで well-founded。
-/
theorem boundaryDecorationGlobalStep_wellFounded_by_totalExcess
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    WellFounded
      (fun W Z : BoundaryDecorationBundle D =>
        BoundaryDecorationGlobalStep
          P hPrimitive hReduced u D Z W) := by
  refine
    (measure
      (boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D)).wf.mono ?_
  intro W Z hStep
  exact BoundaryDecorationGlobalStep.totalExcess_lt
    P hPrimitive hReduced u D hStep

/-! ## 5. TotalExcess は状態識別と向きを同時に担う自然数埋め込み -/

/--
boundary-decoration bundle 全体を `TotalExcess` 一個で自然数へ埋め込む。

単射なので状態識別に情報損失がなく、前節により全 global edge はこの自然数を strict に下げる。
-/
noncomputable def boundaryDecorationBundleTotalExcessEmbedding
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationBundle D ↪ ℕ where
  toFun := boundaryDecorationBundleTotalExcess
    P hPrimitive hReduced u D
  inj' := boundaryDecorationBundleTotalExcess_injective
    P hPrimitive hReduced u D

/--
上の自然数埋め込みは、global one-step を自然数の strict decrease へ送る。
すなわち状態識別と書き換え方向の双方を同じ scalar が担う。
-/
theorem boundaryDecorationBundleTotalExcessEmbedding_maps_globalStep
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W : BoundaryDecorationBundle D}
    (h : BoundaryDecorationGlobalStep
      P hPrimitive hReduced u D Z W) :
    boundaryDecorationBundleTotalExcessEmbedding
        P hPrimitive hReduced u D W <
      boundaryDecorationBundleTotalExcessEmbedding
        P hPrimitive hReduced u D Z := by
  change
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D W <
      boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D Z
  exact BoundaryDecorationGlobalStep.totalExcess_lt
    P hPrimitive hReduced u D h

/-! ## 6. global loss と有限到達上の加法 cocycle -/

/-- bundle endpoint 間の total-excess loss。 -/
def boundaryDecorationGlobalLoss
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z W : BoundaryDecorationBundle D) : ℕ :=
  boundaryDecorationBundleTotalExcess
      P hPrimitive hReduced u D Z -
    boundaryDecorationBundleTotalExcess
      P hPrimitive hReduced u D W

/-- 一回の global edge の loss は strict positive。 -/
theorem BoundaryDecorationGlobalStep.loss_pos
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W : BoundaryDecorationBundle D}
    (h : BoundaryDecorationGlobalStep
      P hPrimitive hReduced u D Z W) :
    0 < boundaryDecorationGlobalLoss
      P hPrimitive hReduced u D Z W := by
  have hLt := BoundaryDecorationGlobalStep.totalExcess_lt
    P hPrimitive hReduced u D h
  unfold boundaryDecorationGlobalLoss
  omega

/-- 一回の global edge では source total excess が loss + target に exact 分解する。 -/
theorem BoundaryDecorationGlobalStep.totalExcess_eq_loss_add_target
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W : BoundaryDecorationBundle D}
    (h : BoundaryDecorationGlobalStep
      P hPrimitive hReduced u D Z W) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D Z =
      boundaryDecorationGlobalLoss
          P hPrimitive hReduced u D Z W +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D W := by
  have hLt := BoundaryDecorationGlobalStep.totalExcess_lt
    P hPrimitive hReduced u D h
  unfold boundaryDecorationGlobalLoss
  omega

namespace BoundaryDecorationGlobalReachable

/-- finite global reachability に沿って total excess は nonincreasing。 -/
theorem totalExcess_le
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W : BoundaryDecorationBundle D}
    (h : BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D Z W) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D W ≤
      boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D Z := by
  induction h with
  | refl =>
      exact le_rfl
  | cons hStep hTail ih =>
      exact le_trans ih (Nat.le_of_lt
        (BoundaryDecorationGlobalStep.totalExcess_lt
          P hPrimitive hReduced u D hStep))

/--
有限到達の endpoint でも source total excess は endpoint loss と target excess に exact 分解する。
この式は経路内部の一歩一歩を参照せず、両 endpoint だけで決まる。
-/
theorem totalExcess_eq_loss_add_target
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W : BoundaryDecorationBundle D}
    (h : BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D Z W) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D Z =
      boundaryDecorationGlobalLoss
          P hPrimitive hReduced u D Z W +
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D W := by
  have hLe := totalExcess_le P hPrimitive hReduced u D h
  unfold boundaryDecorationGlobalLoss
  omega

/--
有限到達が非自明なら TotalExcess は strict に下がる。
したがって自然数埋め込み上に directed cycle は存在しない。
-/
theorem totalExcess_lt_of_ne
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W : BoundaryDecorationBundle D}
    (h : BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D Z W)
    (hne : Z ≠ W) :
    boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D W <
      boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D Z := by
  have hLe := totalExcess_le P hPrimitive hReduced u D h
  by_contra hNot
  have hEq :
      boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D W =
        boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D Z := by
    omega
  have hPoints := boundaryDecorationBundleTotalExcess_injective
    P hPrimitive hReduced u D hEq
  exact hne hPoints.symm

end BoundaryDecorationGlobalReachable

/--
連続する有限到達 `Z ->* W ->* V` では endpoint loss が exact に加法的。
従って mixed local/boundary path の total arithmetic loss は経路ではなく endpoint だけで決まる。
-/
theorem boundaryDecorationGlobalLoss_add_of_reachable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W V : BoundaryDecorationBundle D}
    (hZW : BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D Z W)
    (hWV : BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D W V) :
    boundaryDecorationGlobalLoss
        P hPrimitive hReduced u D Z V =
      boundaryDecorationGlobalLoss
          P hPrimitive hReduced u D Z W +
        boundaryDecorationGlobalLoss
          P hPrimitive hReduced u D W V := by
  have hWZ := BoundaryDecorationGlobalReachable.totalExcess_le
    P hPrimitive hReduced u D hZW
  have hVW := BoundaryDecorationGlobalReachable.totalExcess_le
    P hPrimitive hReduced u D hWV
  unfold boundaryDecorationGlobalLoss
  omega

/-- absolute bottom までの endpoint loss は source total excess そのもの。 -/
theorem boundaryDecorationGlobalLoss_to_bottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z : BoundaryDecorationBundle D) :
    boundaryDecorationGlobalLoss
        P hPrimitive hReduced u D Z
        (boundaryDecorationBundleBottom D) =
      boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D Z := by
  unfold boundaryDecorationGlobalLoss
  rw [boundaryDecorationBundleBottom_totalExcess]
  simp

/-! ## 7. closure package -/

/--
一個の自然数 `TotalExcess` が

* bundle state を完全に識別し、
* 全 global one-step を strict に向き付け、
* それだけで termination を証明し、
* 0 であることが absolute bottom と同値で、
* endpoint loss が finite reachability 上の加法 cocycle をなす

ことを一つに束ねる。
-/
structure BoundaryDecorationGlobalTotalExcessClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  scalar_injective :
    Function.Injective
      (boundaryDecorationBundleTotalExcess
        P hPrimitive hReduced u D)
  step_strict :
    ∀ {Z W : BoundaryDecorationBundle D},
      BoundaryDecorationGlobalStep
          P hPrimitive hReduced u D Z W →
        boundaryDecorationBundleTotalExcess
            P hPrimitive hReduced u D W <
          boundaryDecorationBundleTotalExcess
            P hPrimitive hReduced u D Z
  termination_by_scalar :
    WellFounded
      (fun W Z : BoundaryDecorationBundle D =>
        BoundaryDecorationGlobalStep
          P hPrimitive hReduced u D Z W)
  zero_iff_bottom :
    ∀ Z : BoundaryDecorationBundle D,
      boundaryDecorationBundleTotalExcess
          P hPrimitive hReduced u D Z = 0 ↔
        Z = boundaryDecorationBundleBottom D
  loss_positive :
    ∀ {Z W : BoundaryDecorationBundle D},
      BoundaryDecorationGlobalStep
          P hPrimitive hReduced u D Z W →
        0 < boundaryDecorationGlobalLoss
          P hPrimitive hReduced u D Z W
  loss_additive :
    ∀ {Z W V : BoundaryDecorationBundle D},
      BoundaryDecorationGlobalReachable
          P hPrimitive hReduced u D Z W →
      BoundaryDecorationGlobalReachable
          P hPrimitive hReduced u D W V →
        boundaryDecorationGlobalLoss
            P hPrimitive hReduced u D Z V =
          boundaryDecorationGlobalLoss
              P hPrimitive hReduced u D Z W +
            boundaryDecorationGlobalLoss
              P hPrimitive hReduced u D W V

/--
## Global Total Excess Closure

boundary-decoration bundle 全体は、一個の自然数 `TotalExcess` によって
状態識別と大域書き換えの向き付けを同時に持つ。
-/
theorem boundaryDecorationGlobalTotalExcess_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationGlobalTotalExcessClosed
      P hPrimitive hReduced u D := by
  exact {
    scalar_injective :=
      boundaryDecorationBundleTotalExcess_injective
        P hPrimitive hReduced u D
    step_strict := fun h =>
      BoundaryDecorationGlobalStep.totalExcess_lt
        P hPrimitive hReduced u D h
    termination_by_scalar :=
      boundaryDecorationGlobalStep_wellFounded_by_totalExcess
        P hPrimitive hReduced u D
    zero_iff_bottom :=
      boundaryDecorationBundleTotalExcess_eq_zero_iff_eq_bottom
        P hPrimitive hReduced u D
    loss_positive := fun h =>
      BoundaryDecorationGlobalStep.loss_pos
        P hPrimitive hReduced u D h
    loss_additive :=
      boundaryDecorationGlobalLoss_add_of_reachable
        P hPrimitive hReduced u D
  }

end RecordFerrers
end Collatz2
