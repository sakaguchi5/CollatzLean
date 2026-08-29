import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.BoundaryDecorationMixedMoveCoherence
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WellFounded

/-!
# Record–Ferrers Perturbation / Boundary Decoration Global Normalization

`BoundaryDecorationMixedMoveCoherence` までで、dependent boundary-decoration bundle 上の
二種類の genuine local move

* fixed base fiber 内の one-cell deletion
* retained boundary 一個の canonical merge

について、local/local、boundary/boundary、local/boundary の全 critical-pair geometry が揃った。

本ファイルではこれらを一つの global rewrite relation に束ね、その有限閉包を構成する。

中心となる順位は

  (retained boundary count, decoded fiber cell count)

の辞書式順序である。

* fiber one-cell deletion は第1成分を固定し、第2成分を exact に 1 減らす。
* genuine boundary merge は第1成分を exact に 1 減らすので、第2成分の変化に依存せず下降する。

従って global relation は well-founded。

さらに任意 bundle point `(R,A)` から

  (R,A)
    ->* (R, flat fiber)
    ->* (retainNoBoundaries, flat fiber)

という explicit normalization path を作る。
後半は P35 の actual boundary-deletion reachability と、canonical merge が flat fiber を
flat fiber に送る exact compatibility を使う。

終点は既存

  boundaryDecorationBundleBottom D

そのものであり、これは canonical no-boundary actual point、fixed fiber の absolute bottom を
realize する。従って global normal form は一意で、任意二点はこの bottom で joinable。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. bundle 上の global one-step relation -/

/--
Boundary-decoration bundle 上の global one-step rewrite。

* `fiber`    : current retained-boundary base を固定した one-cell deletion。
* `boundary` : genuine retained boundary 一個の canonical inter-fiber merge。
-/
inductive BoundaryDecorationGlobalStep
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationBundle D -> BoundaryDecorationBundle D -> Prop
  | fiber
      {R : RetainedBoundaryPattern D}
      {A B : BoundaryDecorationFiber D R}
      (hAB : BoundaryDecorationFiberCellDeletion
        P hPrimitive hReduced u D R A B) :
      BoundaryDecorationGlobalStep
        P hPrimitive hReduced u D
        ⟨R, A⟩ ⟨R, B⟩
  | boundary
      {R : RetainedBoundaryPattern D}
      (b : InternalRecordBoundary D)
      (hb : R b = true)
      (A : BoundaryDecorationFiber D R) :
      BoundaryDecorationGlobalStep
        P hPrimitive hReduced u D
        ⟨R, A⟩
        ⟨eraseRetainedBoundary R b,
          boundaryDecorationCanonicalInterfiberMerge D R b A⟩

/-! ## 2. lexicographic termination rank -/

/--
各 bundle point の global termination rank。

第1成分を boundary count とすることで、boundary merge の際に fiber complexity が
どう変化しても必ず下降する。第2成分は decoded local-decoration tuple の ordinary cell count。
-/
noncomputable def boundaryDecorationGlobalRank
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (Z : BoundaryDecorationBundle D) : ℕ ×ₗ ℕ :=
  toLex
    (retainedBoundaryCount D Z.1,
      Z.2.toLocalDecorationTuple.cellCount)

/-- fiber one-cell step は decoded fiber cell count を exact に 1 減らす。 -/
theorem boundaryDecorationFiberCellDeletion_cellCount_succ
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    {A B : BoundaryDecorationFiber D R}
    (hAB : BoundaryDecorationFiberCellDeletion
      P hPrimitive hReduced u D R A B) :
    A.toLocalDecorationTuple.cellCount =
      B.toLocalDecorationTuple.cellCount + 1 := by
  have hArea : LocalAreaTupleCellDeletion A B :=
    (boundaryDecorationFiberCellDeletion_iff_areaTupleCellDeletion
      P hPrimitive hReduced u D R A B).1 hAB
  exact hArea.toDecorationTuple.cellCount_succ

/-- global one-step は辞書式 rank を strict に下げる。 -/
theorem BoundaryDecorationGlobalStep.rank_lt
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W : BoundaryDecorationBundle D}
    (h : BoundaryDecorationGlobalStep
      P hPrimitive hReduced u D Z W) :
    boundaryDecorationGlobalRank W <
      boundaryDecorationGlobalRank Z := by
  cases h with
  | @fiber R A B hAB =>
      apply Prod.Lex.toLex_lt_toLex.mpr
      right
      refine ⟨rfl, ?_⟩
      change
        B.toLocalDecorationTuple.cellCount <
          A.toLocalDecorationTuple.cellCount
      have hCount :=
        boundaryDecorationFiberCellDeletion_cellCount_succ
          P hPrimitive hReduced u D R hAB
      omega
  | @boundary R b hb A =>
      apply Prod.Lex.toLex_lt_toLex.mpr
      left
      change
        retainedBoundaryCount D
            (eraseRetainedBoundary R b) <
          retainedBoundaryCount D R
      have hCount :=
        retainedBoundaryCount_erase_add_one R b hb
      omega

/--
## Global Termination

fiber/local と boundary/inter-fiber を同じ rewrite relation に混ぜても停止する。
辞書式 rank の well-foundedness による。
-/
theorem boundaryDecorationGlobalStep_wellFounded
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    WellFounded
      (fun W Z : BoundaryDecorationBundle D =>
        BoundaryDecorationGlobalStep
          P hPrimitive hReduced u D Z W) := by
  let rank : BoundaryDecorationBundle D -> ℕ ×ₗ ℕ :=
    boundaryDecorationGlobalRank
  refine
    ((wellFounded_lt :
      WellFounded ((· < ·) : (ℕ ×ₗ ℕ) -> (ℕ ×ₗ ℕ) -> Prop)).onFun
      (f := rank)).mono ?_
  intro W Z hStep
  change rank W < rank Z
  exact BoundaryDecorationGlobalStep.rank_lt
    P hPrimitive hReduced u D hStep

/-! ## 3. finite global reachability -/

/-- global one-step relation の reflexive-transitive finite closure。 -/
inductive BoundaryDecorationGlobalReachable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationBundle D -> BoundaryDecorationBundle D -> Prop
  | refl (Z : BoundaryDecorationBundle D) :
      BoundaryDecorationGlobalReachable
        P hPrimitive hReduced u D Z Z
  | cons
      {Z W V : BoundaryDecorationBundle D} :
      BoundaryDecorationGlobalStep
          P hPrimitive hReduced u D Z W ->
      BoundaryDecorationGlobalReachable
          P hPrimitive hReduced u D W V ->
      BoundaryDecorationGlobalReachable
          P hPrimitive hReduced u D Z V

namespace BoundaryDecorationGlobalReachable

/-- global reachability は推移的。 -/
theorem trans
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
    BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D Z V := by
  induction hZW with
  | refl =>
      exact hWV
  | cons hStep hTail ih =>
      exact BoundaryDecorationGlobalReachable.cons hStep (ih hWV)

end BoundaryDecorationGlobalReachable

/-! ## 4. fixed base fiber の normalization を global path へ持ち上げる -/

/--
concrete local-decoration tuple の finite product path は、同じ boundary base 上の
bundle global path へそのまま持ち上がる。
-/
theorem boundaryDecorationGlobalReachable_of_decorationTupleReachable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    {A B : LocalDecorationTuple (coarsenedLengthsFor D R)}
    (hAB : LocalDecorationTupleDeletionReachable A B) :
    BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D
      ⟨R, A.toLocalAreaTuple⟩
      ⟨R, B.toLocalAreaTuple⟩ := by
  induction hAB with
  | refl A =>
      exact BoundaryDecorationGlobalReachable.refl _
  | @cons A B C hStep hTail ih =>
      apply BoundaryDecorationGlobalReachable.cons
      · apply BoundaryDecorationGlobalStep.fiber
        apply
          (boundaryDecorationFiberCellDeletion_iff_areaTupleCellDeletion
            P hPrimitive hReduced u D R
            A.toLocalAreaTuple B.toLocalAreaTuple).2
        exact LocalAreaTupleCellDeletion.ofDecorationTuple hStep
      · exact ih

/-- 任意 bundle fiber point は同じ base の canonical flat fiber へ global に到達する。 -/
theorem boundaryDecorationGlobalReachable_to_flatFiber
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (A : BoundaryDecorationFiber D R) :
    BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D
      ⟨R, A⟩
      (boundaryDecorationFlatSection D R) := by
  let T := A.toLocalDecorationTuple
  have hReach :
      LocalDecorationTupleDeletionReachable
        T
        (flatLocalDecorationTuple
          (coarsenedLengthsFor D R)
          (coarsenedLengthsFor_pos D R)) :=
    localDecorationTupleDeletionReachable_to_flat
      (coarsenedLengthsFor_pos D R) T
  have hLift :=
    boundaryDecorationGlobalReachable_of_decorationTupleReachable
      P hPrimitive hReduced u D R hReach
  have hRoundTrip :
      T.toLocalAreaTuple = A := by
    dsimp [T]
    exact LocalAreaTuple.toLocalDecorationTuple_toLocalAreaTuple A
  rw [hRoundTrip] at hLift
  simpa [
    boundaryDecorationFlatSection,
    boundaryDecorationFlatFiber
  ] using hLift

/-! ## 5. flat section の boundary normalization -/

/-- genuine one-boundary deletion は flat section 上でも一段 global step。 -/
theorem boundaryDecorationGlobalStep_flat_boundary
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (R : RetainedBoundaryPattern D)
    (b : InternalRecordBoundary D)
    (hb : R b = true) :
    BoundaryDecorationGlobalStep
      P hPrimitive hReduced u D
      (boundaryDecorationFlatSection D R)
      (boundaryDecorationFlatSection D (eraseRetainedBoundary R b)) := by
  change
    BoundaryDecorationGlobalStep
      P hPrimitive hReduced u D
      ⟨R, boundaryDecorationFlatFiber D R⟩
      ⟨eraseRetainedBoundary R b,
        boundaryDecorationFlatFiber D (eraseRetainedBoundary R b)⟩
  rw [← boundaryDecorationCanonicalInterfiberMerge_flatFiber D R b]
  exact BoundaryDecorationGlobalStep.boundary b hb
    (boundaryDecorationFlatFiber D R)

/--
P35 の finite actual boundary-deletion path は、flat section 上の global path として lift できる。
-/
theorem boundaryDecorationGlobalReachable_flat_of_actualBoundaryReachable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {R S : RetainedBoundaryPattern D}
    (hRS : ActualCanonicalDeletionReachable
      P hPrimitive hReduced u D R S) :
    BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D
      (boundaryDecorationFlatSection D R)
      (boundaryDecorationFlatSection D S) := by
  induction hRS with
  | refl =>
      exact BoundaryDecorationGlobalReachable.refl _
  | @tail S T hReach hStep ih =>
      rcases hStep.pattern_step with ⟨b, hb, hT⟩
      subst T
      exact BoundaryDecorationGlobalReachable.trans
        P hPrimitive hReduced u D
        ih
        (BoundaryDecorationGlobalReachable.cons
          (boundaryDecorationGlobalStep_flat_boundary
            P hPrimitive hReduced u D S b hb)
          (BoundaryDecorationGlobalReachable.refl _))

/-! ## 6. absolute global bottom への normalization -/

/--
## Global Normalization to the Absolute Bottom

任意の dependent bundle point は、fiber normalization と boundary normalization を有限回組み合わせて
canonical absolute bottom へ到達する。
-/
theorem boundaryDecorationGlobalReachable_to_bottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z : BoundaryDecorationBundle D) :
    BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D
      Z
      (boundaryDecorationBundleBottom D) := by
  rcases Z with ⟨R, A⟩
  have hFiber :=
    boundaryDecorationGlobalReachable_to_flatFiber
      P hPrimitive hReduced u D R A
  have hPattern :
      ActualCanonicalDeletionReachable
        P hPrimitive hReduced u D R (retainNoBoundaries D) :=
    actualReachable_to_none P hPrimitive hReduced u D R
  have hBoundary :=
    boundaryDecorationGlobalReachable_flat_of_actualBoundaryReachable
      P hPrimitive hReduced u D hPattern
  exact BoundaryDecorationGlobalReachable.trans
    P hPrimitive hReduced u D hFiber hBoundary

/-- 元 actual source の top bundle embedding も absolute bottom へ global に正規化される。 -/
theorem sourceBoundaryDecorationBundlePoint_globalReachable_to_bottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D
      (sourceBoundaryDecorationBundlePoint
        P hPrimitive hReduced u D)
      (boundaryDecorationBundleBottom D) :=
  boundaryDecorationGlobalReachable_to_bottom
    P hPrimitive hReduced u D
    (sourceBoundaryDecorationBundlePoint
      P hPrimitive hReduced u D)

/-! ## 7. global normal form の一意性 -/

/-- outgoing global one-step を持たない bundle point。 -/
def BoundaryDecorationGlobalNormal
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z : BoundaryDecorationBundle D) : Prop :=
  ∀ W : BoundaryDecorationBundle D,
    ¬ BoundaryDecorationGlobalStep
      P hPrimitive hReduced u D Z W

/-- global-normal source から reachable な endpoint は source 自身に限る。 -/
theorem BoundaryDecorationGlobalReachable.eq_of_source_normal
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W : BoundaryDecorationBundle D}
    (hNormal : BoundaryDecorationGlobalNormal
      P hPrimitive hReduced u D Z)
    (hReach : BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D Z W) :
    Z = W := by
  cases hReach with
  | refl =>
      rfl
  | cons hStep hTail =>
      exact False.elim (hNormal _ hStep)

/-- canonical absolute bottom は global-normal。 -/
theorem boundaryDecorationBundleBottom_globalNormal
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationGlobalNormal
      P hPrimitive hReduced u D
      (boundaryDecorationBundleBottom D) := by
  unfold BoundaryDecorationGlobalNormal
  change
    ∀ W : BoundaryDecorationBundle D,
      ¬ BoundaryDecorationGlobalStep
        P hPrimitive hReduced u D
        ⟨retainNoBoundaries D,
          boundaryDecorationFlatFiber D (retainNoBoundaries D)⟩ W
  intro W hStep
  cases hStep with
  | @fiber R A B hAB =>
      have hArea : LocalAreaTupleCellDeletion _ _ :=
        (boundaryDecorationFiberCellDeletion_iff_areaTupleCellDeletion
          P hPrimitive hReduced u D _ _ B).1 hAB
      have hDec := hArea.toDecorationTuple
      have hFlatNormal :=
        flatLocalDecorationTuple_normal
          (coarsenedLengthsFor D (retainNoBoundaries D))
          (coarsenedLengthsFor_pos D (retainNoBoundaries D))
      apply hFlatNormal B.toLocalDecorationTuple
      simpa [
        boundaryDecorationBundleBottom,
        boundaryDecorationFlatSection,
        boundaryDecorationFlatFiber
      ] using hDec
  | @boundary R b hb A =>
      simp only [retainNoBoundaries, Bool.false_eq_true] at hb

/--
Global normal form は canonical absolute bottom に限り、逆も成り立つ。
-/
theorem boundaryDecorationGlobalNormal_iff_eq_bottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z : BoundaryDecorationBundle D) :
    BoundaryDecorationGlobalNormal
        P hPrimitive hReduced u D Z ↔
      Z = boundaryDecorationBundleBottom D := by
  constructor
  · intro hNormal
    exact BoundaryDecorationGlobalReachable.eq_of_source_normal
      P hPrimitive hReduced u D hNormal
      (boundaryDecorationGlobalReachable_to_bottom
        P hPrimitive hReduced u D Z)
  · intro hEq
    subst Z
    exact boundaryDecorationBundleBottom_globalNormal
      P hPrimitive hReduced u D

/-- global normal form は一意。 -/
theorem boundaryDecorationGlobalNormal_unique
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z W : BoundaryDecorationBundle D}
    (hZ : BoundaryDecorationGlobalNormal
      P hPrimitive hReduced u D Z)
    (hW : BoundaryDecorationGlobalNormal
      P hPrimitive hReduced u D W) :
    Z = W := by
  have hZBottom :=
    (boundaryDecorationGlobalNormal_iff_eq_bottom
      P hPrimitive hReduced u D Z).1 hZ
  have hWBottom :=
    (boundaryDecorationGlobalNormal_iff_eq_bottom
      P hPrimitive hReduced u D W).1 hW
  exact hZBottom.trans hWBottom.symm

/-! ## 8. global joinability / confluence -/

/-- 任意二 bundle points は absolute bottom で joinable。 -/
theorem boundaryDecorationGlobalReachable_joinable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (Z W : BoundaryDecorationBundle D) :
    ∃ V : BoundaryDecorationBundle D,
      BoundaryDecorationGlobalReachable
        P hPrimitive hReduced u D Z V ∧
      BoundaryDecorationGlobalReachable
        P hPrimitive hReduced u D W V := by
  exact ⟨
    boundaryDecorationBundleBottom D,
    boundaryDecorationGlobalReachable_to_bottom
      P hPrimitive hReduced u D Z,
    boundaryDecorationGlobalReachable_to_bottom
      P hPrimitive hReduced u D W
  ⟩

/-- 任意の global reachability fork は common descendant を持つ。 -/
theorem boundaryDecorationGlobalReachable_confluent
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {X Y Z : BoundaryDecorationBundle D}
    (_hXY : BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D X Y)
    (_hXZ : BoundaryDecorationGlobalReachable
      P hPrimitive hReduced u D X Z) :
    ∃ W : BoundaryDecorationBundle D,
      BoundaryDecorationGlobalReachable
        P hPrimitive hReduced u D Y W ∧
      BoundaryDecorationGlobalReachable
        P hPrimitive hReduced u D Z W :=
  boundaryDecorationGlobalReachable_joinable
    P hPrimitive hReduced u D Y Z

/-! ## 9. arithmetic / actual endpoint identification -/

/-- global bottom は bundle total excess の unique zero。 -/
theorem boundaryDecorationGlobalBottom_totalExcess_zero
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryDecorationBundleTotalExcess
      P hPrimitive hReduced u D
      (boundaryDecorationBundleBottom D) = 0 :=
  boundaryDecorationBundleBottom_totalExcess
    P hPrimitive hReduced u D

/-- global-normal bundle point は total excess 0。 -/
theorem boundaryDecorationGlobalNormal_totalExcess_zero
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z : BoundaryDecorationBundle D}
    (hZ : BoundaryDecorationGlobalNormal
      P hPrimitive hReduced u D Z) :
    boundaryDecorationBundleTotalExcess
      P hPrimitive hReduced u D Z = 0 := by
  rw [(boundaryDecorationGlobalNormal_iff_eq_bottom
    P hPrimitive hReduced u D Z).1 hZ]
  exact boundaryDecorationBundleBottom_totalExcess
    P hPrimitive hReduced u D

/-- global bottom の actual realization は P35 の canonical no-boundary absolute point。 -/
theorem boundaryDecorationGlobalBottom_realization
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    boundaryDecorationBundleRealization
        P hPrimitive hReduced u D
        (boundaryDecorationBundleBottom D) =
      canonicalNoBoundaryPoint P hPrimitive hReduced u D :=
  boundaryDecorationBundleRealization_bottom
    P hPrimitive hReduced u D

/-- 任意 global-normal point の realization は同じ canonical no-boundary absolute point。 -/
theorem boundaryDecorationGlobalNormal_realization_eq_absoluteBottom
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {Z : BoundaryDecorationBundle D}
    (hZ : BoundaryDecorationGlobalNormal
      P hPrimitive hReduced u D Z) :
    boundaryDecorationBundleRealization
        P hPrimitive hReduced u D Z =
      canonicalNoBoundaryPoint P hPrimitive hReduced u D := by
  rw [(boundaryDecorationGlobalNormal_iff_eq_bottom
    P hPrimitive hReduced u D Z).1 hZ]
  exact boundaryDecorationBundleRealization_bottom
    P hPrimitive hReduced u D

/-! ## 10. closure package -/

/-- global normalization layer で閉じた内容。 -/
structure BoundaryDecorationGlobalNormalizationClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  termination :
    WellFounded
      (fun W Z : BoundaryDecorationBundle D =>
        BoundaryDecorationGlobalStep
          P hPrimitive hReduced u D Z W)
  every_point_normalizes :
    ∀ Z : BoundaryDecorationBundle D,
      BoundaryDecorationGlobalReachable
        P hPrimitive hReduced u D Z
        (boundaryDecorationBundleBottom D)
  normal_form_exact :
    ∀ Z : BoundaryDecorationBundle D,
      BoundaryDecorationGlobalNormal
          P hPrimitive hReduced u D Z ↔
        Z = boundaryDecorationBundleBottom D
  joinable :
    ∀ Z W : BoundaryDecorationBundle D,
      ∃ V : BoundaryDecorationBundle D,
        BoundaryDecorationGlobalReachable
          P hPrimitive hReduced u D Z V ∧
        BoundaryDecorationGlobalReachable
          P hPrimitive hReduced u D W V
  bottom_zero :
    boundaryDecorationBundleTotalExcess
      P hPrimitive hReduced u D
      (boundaryDecorationBundleBottom D) = 0
  bottom_realizes_absolute :
    boundaryDecorationBundleRealization
        P hPrimitive hReduced u D
        (boundaryDecorationBundleBottom D) =
      canonicalNoBoundaryPoint P hPrimitive hReduced u D

/--
## Boundary Decoration Global Normalization Closure

local one-cell deletion と genuine canonical boundary merge を混ぜた dependent bundle rewrite は
有限・停止・globally joinable で、唯一の normal form は no-boundary all-flat bundle bottom。
その actual realization は fixed `(p,H)` fiber の canonical no-boundary absolute bottom そのもの。
-/
theorem boundaryDecorationGlobalNormalization_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    BoundaryDecorationGlobalNormalizationClosed
      P hPrimitive hReduced u D := by
  exact {
    termination :=
      boundaryDecorationGlobalStep_wellFounded
        P hPrimitive hReduced u D
    every_point_normalizes :=
      boundaryDecorationGlobalReachable_to_bottom
        P hPrimitive hReduced u D
    normal_form_exact :=
      boundaryDecorationGlobalNormal_iff_eq_bottom
        P hPrimitive hReduced u D
    joinable :=
      boundaryDecorationGlobalReachable_joinable
        P hPrimitive hReduced u D
    bottom_zero :=
      boundaryDecorationBundleBottom_totalExcess
        P hPrimitive hReduced u D
    bottom_realizes_absolute :=
      boundaryDecorationBundleRealization_bottom
        P hPrimitive hReduced u D
  }

end RecordFerrers
end Collatz2
