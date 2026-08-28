import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalAreaProduct
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationDeletionSystem
import Mathlib.Order.WellFounded

/-!
# Record–Ferrers Perturbation / Product Decoration Deletion System

`LocalAreaProduct` までで、primitive + StripReduced fixed chord 上の fixed-skeleton
actual state space は

  FixedSkeletonSource P u D
    ≃ LocalDecorationTuple D.lengths
    ≃ LocalAreaTuple D.lengths

と exact に product coordinate 化された。

一方、各 positive length `r` の local factor `LocalDecoration r` には既に

  LocalDecorationCellDeletion

という one-cell downward rewrite があり、

* ordinary Ferrers area が一段で exact に 1 減る
* relation は well-founded
* `localFlatDecoration r` が唯一の normal form
* 全状態が flat へ到達
* 任意二状態が flat で joinable

まで閉じている。

本ファイルでは、この local rewrite を fixed skeleton 全体の asynchronous product rewrite
へ持ち上げる。

一段の product rewrite は exact に次のどちらかである。

* head factor で一回 local one-cell deletion を行い、tail は固定する。
* head factor を固定し、tail product のどこか一成分で一回 deletion を行う。

従って一段では「ちょうど一つの local factor」だけが変化する。

さらに

* product reachability ↔ componentwise local reachability
* product cell count は一段で exact に 1 減少
* product weighted local area は一段で strict に減少
* product relation は terminating
* all-flat tuple が唯一の normal form
* 全 tuple が all-flat tuple へ到達
* global joinability

を閉じる。

最後に `FixedSkeletonSource ≃ LocalDecorationTuple D.lengths` を通じて、この product
dynamics 自体を actual fixed-skeleton state space へ exact transport する。

注意:
ここで actual 側へ transport する rewrite は product coordinate による canonical relation
`FixedSkeletonProductCellDeletion` である。ambient whole-fiber の
`FerrersShape.IsUnitCover` との完全な同値は定義で仮定せず、別の compatibility refinement
として分離可能な形にしている。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-! ## 1. local-decoration tuple 上の asynchronous one-cell product rewrite -/

/--
fixed length list 上の product one-cell deletion。

* `head`: 先頭 local factor だけを一セル削除する。
* `tail`: 先頭 factor を固定し、tail のどこか一 factor を一セル削除する。

したがって構成上、一段で変化する local factor は exact に一つ。
-/
inductive LocalDecorationTupleCellDeletion :
    {rs : List ℕ} →
      LocalDecorationTuple rs →
      LocalDecorationTuple rs →
      Prop
  | head
      {r : ℕ}
      {rs : List ℕ}
      {A B : LocalDecoration r}
      (T : LocalDecorationTuple rs)
      (hAB : LocalDecorationCellDeletion A B) :
      LocalDecorationTupleCellDeletion
        (LocalDecorationTuple.cons A T)
        (LocalDecorationTuple.cons B T)
  | tail
      {r : ℕ}
      {rs : List ℕ}
      (A : LocalDecoration r)
      {T U : LocalDecorationTuple rs}
      (hTU : LocalDecorationTupleCellDeletion T U) :
      LocalDecorationTupleCellDeletion
        (LocalDecorationTuple.cons A T)
        (LocalDecorationTuple.cons A U)

namespace LocalDecorationTuple

/-- product tuple の ordinary Ferrers cell count。termination measure に使う。 -/
def cellCount
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) : ℕ :=
  match T with
  | .nil => 0
  | .cons A U =>
      FerrersShape.area A.ferrersShape + U.cellCount

/--
product tuple の skeleton-weighted local Ferrers area。

`LocalAreaProduct` の `LocalAreaTuple.weightedArea` と同じ量を
concrete local-decoration tuple 上で直接読む。
-/
def weightedArea
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) : ℕ :=
  weightedLocalDecorationArea
    rs (T.blocks.map localDecorationArea)

/-- tuple weighted area は area-product coordinate の weighted area と exact に一致。 -/
theorem weightedArea_eq_toLocalAreaTuple_weightedArea
    {rs : List ℕ}
    (T : LocalDecorationTuple rs) :
    T.weightedArea = T.toLocalAreaTuple.weightedArea := by
  unfold weightedArea LocalAreaTuple.weightedArea
  rw [T.toLocalAreaTuple_values]

end LocalDecorationTuple

namespace LocalDecorationTupleCellDeletion

/-- product one-cell step で total ordinary cell count は exact に 1 減る。 -/
theorem cellCount_succ
    {rs : List ℕ}
    {A B : LocalDecorationTuple rs}
    (h : LocalDecorationTupleCellDeletion A B) :
    A.cellCount = B.cellCount + 1 := by
  induction h with
  | @head r rs A B T hAB =>
      have hArea := hAB.area_succ
      change
        FerrersShape.area A.ferrersShape + T.cellCount =
          FerrersShape.area B.ferrersShape + T.cellCount + 1
      omega
  | @tail r rs A T U hTU ih =>
      change
        FerrersShape.area A.ferrersShape + T.cellCount =
          FerrersShape.area A.ferrersShape + U.cellCount + 1
      omega

/-- product one-cell step は source / target を同一視しない。 -/
theorem tuple_ne
    {rs : List ℕ}
    {A B : LocalDecorationTuple rs}
    (h : LocalDecorationTupleCellDeletion A B) :
    B ≠ A := by
  intro hEq
  subst B
  have hCount := h.cellCount_succ
  omega

/--
product one-cell step で skeleton-weighted local area potential は strict に減る。

ordinary cell count は常に 1 減るが、weighted area の減少幅は changed local cell の
weight に依存するため一般には 1 ではない。
-/
theorem weightedArea_lt
    {rs : List ℕ}
    {A B : LocalDecorationTuple rs}
    (h : LocalDecorationTupleCellDeletion A B) :
    B.weightedArea < A.weightedArea := by
  induction h with
  | @head r rs A B T hAB =>
      have hLocal := hAB.localDecorationArea_lt
      have hPos : 0 < 3 ^ rs.sum := by positivity
      change
        3 ^ rs.sum * localDecorationArea B.word +
            2 ^ minimalDepth r * T.weightedArea <
          3 ^ rs.sum * localDecorationArea A.word +
            2 ^ minimalDepth r * T.weightedArea
      nlinarith
  | @tail r rs A T U hTU ih =>
      have hPos : 0 < 2 ^ minimalDepth r := by positivity
      change
        3 ^ rs.sum * localDecorationArea A.word +
            2 ^ minimalDepth r * U.weightedArea <
          3 ^ rs.sum * localDecorationArea A.word +
            2 ^ minimalDepth r * T.weightedArea
      nlinarith

end LocalDecorationTupleCellDeletion

/-! ## 2. finite product reachability -/

/-- product one-cell rewrite の reflexive-transitive finite reachability。 -/
inductive LocalDecorationTupleDeletionReachable
    {rs : List ℕ} :
    LocalDecorationTuple rs →
      LocalDecorationTuple rs →
      Prop
  | refl (A : LocalDecorationTuple rs) :
      LocalDecorationTupleDeletionReachable A A
  | cons
      {A B C : LocalDecorationTuple rs} :
      LocalDecorationTupleCellDeletion A B →
      LocalDecorationTupleDeletionReachable B C →
      LocalDecorationTupleDeletionReachable A C

namespace LocalDecorationTupleDeletionReachable

/-- product reachability は推移的。 -/
theorem trans
    {rs : List ℕ}
    {A B C : LocalDecorationTuple rs}
    (hAB : LocalDecorationTupleDeletionReachable A B)
    (hBC : LocalDecorationTupleDeletionReachable B C) :
    LocalDecorationTupleDeletionReachable A C := by
  induction hAB with
  | refl =>
      exact hBC
  | cons hStep hTail ih =>
      exact LocalDecorationTupleDeletionReachable.cons
        hStep (ih hBC)

/-- local head reachability は tail を固定して product reachability へ持ち上がる。 -/
theorem head_of_localReachable
    {r : ℕ}
    {rs : List ℕ}
    {A B : LocalDecoration r}
    (T : LocalDecorationTuple rs)
    (hAB : LocalDecorationDeletionReachable A B) :
    LocalDecorationTupleDeletionReachable
      (LocalDecorationTuple.cons A T)
      (LocalDecorationTuple.cons B T) := by
  induction hAB with
  | refl =>
      exact LocalDecorationTupleDeletionReachable.refl _
  | head hStep hTail ih =>
      exact LocalDecorationTupleDeletionReachable.cons
        (LocalDecorationTupleCellDeletion.head T hStep)
        ih

/-- tail product reachability は head factor を固定したまま持ち上がる。 -/
theorem tail_of_reachable
    {r : ℕ}
    {rs : List ℕ}
    (A : LocalDecoration r)
    {T U : LocalDecorationTuple rs}
    (hTU : LocalDecorationTupleDeletionReachable T U) :
    LocalDecorationTupleDeletionReachable
      (LocalDecorationTuple.cons A T)
      (LocalDecorationTuple.cons A U) := by
  induction hTU with
  | refl =>
      exact LocalDecorationTupleDeletionReachable.refl _
  | cons hStep hTail ih =>
      exact LocalDecorationTupleDeletionReachable.cons
        (LocalDecorationTupleCellDeletion.tail A hStep)
        ih

end LocalDecorationTupleDeletionReachable

/-! ## 3. componentwise local reachability -/

/--
各 coordinate ごとの local reachability。

product reachability は asynchronous に one factor ずつ動かすが、
endpoint 条件だけ見れば各 factor が local reachability で結ばれることと同値になる。
-/
inductive LocalDecorationTuplePointwiseReachable :
    {rs : List ℕ} →
      LocalDecorationTuple rs →
      LocalDecorationTuple rs →
      Prop
  | nil :
      LocalDecorationTuplePointwiseReachable
        LocalDecorationTuple.nil
        LocalDecorationTuple.nil
  | cons
      {r : ℕ}
      {rs : List ℕ}
      {A B : LocalDecoration r}
      {T U : LocalDecorationTuple rs}
      (hAB : LocalDecorationDeletionReachable A B)
      (hTU : LocalDecorationTuplePointwiseReachable T U) :
      LocalDecorationTuplePointwiseReachable
        (LocalDecorationTuple.cons A T)
        (LocalDecorationTuple.cons B U)

namespace LocalDecorationTuplePointwiseReachable

/-- pointwise reachability の reflexivity。 -/
theorem refl
    {rs : List ℕ}
    (A : LocalDecorationTuple rs) :
    LocalDecorationTuplePointwiseReachable A A := by
  induction A with
  | nil =>
      exact .nil
  | cons A T ih =>
      exact .cons
        (LocalDecorationDeletionReachable.refl A)
        ih

/-- pointwise reachability の transitivity。 -/
theorem trans
    {rs : List ℕ}
    {A B C : LocalDecorationTuple rs}
    (hAB : LocalDecorationTuplePointwiseReachable A B)
    (hBC : LocalDecorationTuplePointwiseReachable B C) :
    LocalDecorationTuplePointwiseReachable A C := by
  induction hAB with
  | nil =>
      cases hBC
      exact .nil
  | @cons r rs A B T U hHead hTail ih =>
      cases hBC with
      | @cons _ _ _ C _ V hHeadBC hTailBC =>
          exact .cons
            (LocalDecorationDeletionReachable.trans hHead hHeadBC)
            (ih hTailBC)

end LocalDecorationTuplePointwiseReachable

/-- 一回の product deletion は componentwise local reachability を与える。 -/
theorem LocalDecorationTupleCellDeletion.toPointwiseReachable
    {rs : List ℕ}
    {A B : LocalDecorationTuple rs}
    (h : LocalDecorationTupleCellDeletion A B) :
    LocalDecorationTuplePointwiseReachable A B := by
  induction h with
  | @head r rs A B T hAB =>
      exact .cons
        (LocalDecorationDeletionReachable.head
          hAB (LocalDecorationDeletionReachable.refl B))
        (LocalDecorationTuplePointwiseReachable.refl T)
  | @tail r rs A T U hTU ih =>
      exact .cons
        (LocalDecorationDeletionReachable.refl A)
        ih

/-- product reachability なら各 coordinate は local reachability。 -/
theorem LocalDecorationTupleDeletionReachable.toPointwiseReachable
    {rs : List ℕ}
    {A B : LocalDecorationTuple rs}
    (h : LocalDecorationTupleDeletionReachable A B) :
    LocalDecorationTuplePointwiseReachable A B := by
  induction h with
  | refl A =>
      exact LocalDecorationTuplePointwiseReachable.refl A
  | cons hStep hTail ih =>
      exact LocalDecorationTuplePointwiseReachable.trans
        hStep.toPointwiseReachable ih

/-- componentwise local reachability は one-factor-at-a-time product path として実現できる。 -/
theorem LocalDecorationTuplePointwiseReachable.toDeletionReachable
    {rs : List ℕ}
    {A B : LocalDecorationTuple rs}
    (h : LocalDecorationTuplePointwiseReachable A B) :
    LocalDecorationTupleDeletionReachable A B := by
  induction h with
  | nil =>
      exact LocalDecorationTupleDeletionReachable.refl _
  | @cons r rs A B T U hHead hTail ih =>
      have h1 :
          LocalDecorationTupleDeletionReachable
            (LocalDecorationTuple.cons A T)
            (LocalDecorationTuple.cons B T) :=
        LocalDecorationTupleDeletionReachable.head_of_localReachable
          T hHead
      have h2 :
          LocalDecorationTupleDeletionReachable
            (LocalDecorationTuple.cons B T)
            (LocalDecorationTuple.cons B U) :=
        LocalDecorationTupleDeletionReachable.tail_of_reachable
          B ih
      exact h1.trans h2

/--
## Product Reachability Characterization

asynchronous product reachability と componentwise local reachability は exact に同値。
-/
theorem localDecorationTupleDeletionReachable_iff_pointwise
    {rs : List ℕ}
    (A B : LocalDecorationTuple rs) :
    LocalDecorationTupleDeletionReachable A B ↔
      LocalDecorationTuplePointwiseReachable A B := by
  constructor
  · exact fun h => h.toPointwiseReachable
  · exact fun h => h.toDeletionReachable

/-! ## 4. termination -/

/-- product one-cell deletion relation は total ordinary cell count を measure に well-founded。 -/
theorem localDecorationTupleCellDeletion_wellFounded
    (rs : List ℕ) :
    WellFounded
      (fun B A : LocalDecorationTuple rs =>
        LocalDecorationTupleCellDeletion A B) := by
  refine
    (measure
      (fun A : LocalDecorationTuple rs =>
        A.cellCount)).wf.mono ?_
  intro B A hStep
  have h := hStep.cellCount_succ
  change B.cellCount < A.cellCount
  omega

/-! ## 5. all-flat product normal form -/

/-- positive length list に沿った all-flat local-decoration tuple。 -/
def flatLocalDecorationTuple :
    (rs : List ℕ) →
      (∀ r ∈ rs, 0 < r) →
      LocalDecorationTuple rs
  | [], _ =>
      LocalDecorationTuple.nil
  | r :: rs, hPos =>
      LocalDecorationTuple.cons
        (localFlatDecoration r (hPos r (by simp)))
        (flatLocalDecorationTuple
          rs
          (by
            intro s hs
            exact hPos s (by simp [hs])))

/-- product deletion の outgoing edge を持たない状態。 -/
def LocalDecorationTupleDeletionNormal
    {rs : List ℕ}
    (A : LocalDecorationTuple rs) : Prop :=
  ∀ B : LocalDecorationTuple rs,
    ¬ LocalDecorationTupleCellDeletion A B

/-- all-flat tuple は product-normal。 -/
theorem flatLocalDecorationTuple_normal
    (rs : List ℕ)
    (hPos : ∀ r ∈ rs, 0 < r) :
    LocalDecorationTupleDeletionNormal
      (flatLocalDecorationTuple rs hPos) := by
  induction rs with
  | nil =>
      intro B hStep
      cases hStep
  | cons r rs ih =>
      let hr : 0 < r := hPos r (by simp)
      let hTailPos : ∀ s ∈ rs, 0 < s := by
        intro s hs
        exact hPos s (by simp [hs])
      intro B hStep
      change
        LocalDecorationTupleCellDeletion
          (LocalDecorationTuple.cons
            (localFlatDecoration r hr)
            (flatLocalDecorationTuple rs hTailPos))
          B
        at hStep
      cases hStep with
      | head T hLocal =>
          exact (localFlatDecoration_normal r hr) _ hLocal
      | tail A hTail =>
          exact (ih hTailPos) _ hTail

/-- 任意 product tuple は all-flat tuple へ有限回で到達する。 -/
theorem localDecorationTupleDeletionReachable_to_flat
    {rs : List ℕ}
    (hPos : ∀ r ∈ rs, 0 < r)
    (A : LocalDecorationTuple rs) :
    LocalDecorationTupleDeletionReachable
      A (flatLocalDecorationTuple rs hPos) := by
  induction A with
  | nil =>
      exact LocalDecorationTupleDeletionReachable.refl _
  | @cons r rs A T ih =>
      let hr : 0 < r := hPos r (by simp)
      let hTailPos : ∀ s ∈ rs, 0 < s := by
        intro s hs
        exact hPos s (by simp [hs])
      have hHeadLocal :
          LocalDecorationDeletionReachable
            A (localFlatDecoration r hr) :=
        localDecorationDeletionReachable_to_flat hr A
      have hHead :
          LocalDecorationTupleDeletionReachable
            (LocalDecorationTuple.cons A T)
            (LocalDecorationTuple.cons
              (localFlatDecoration r hr) T) :=
        LocalDecorationTupleDeletionReachable.head_of_localReachable
          T hHeadLocal
      have hTailRaw :
          LocalDecorationTupleDeletionReachable
            T (flatLocalDecorationTuple rs hTailPos) :=
        ih hTailPos
      have hTail :
          LocalDecorationTupleDeletionReachable
            (LocalDecorationTuple.cons
              (localFlatDecoration r hr) T)
            (LocalDecorationTuple.cons
              (localFlatDecoration r hr)
              (flatLocalDecorationTuple rs hTailPos)) :=
        LocalDecorationTupleDeletionReachable.tail_of_reachable
          (localFlatDecoration r hr) hTailRaw
      have h := hHead.trans hTail
      simpa [flatLocalDecorationTuple, hr, hTailPos] using h

/-- normal source から reachable な endpoint は source 自身に限る。 -/
theorem LocalDecorationTupleDeletionReachable.eq_of_source_normal
    {rs : List ℕ}
    {A B : LocalDecorationTuple rs}
    (hNormal : LocalDecorationTupleDeletionNormal A)
    (hReach : LocalDecorationTupleDeletionReachable A B) :
    A = B := by
  cases hReach with
  | refl =>
      rfl
  | cons hStep hTail =>
      exact False.elim (hNormal _ hStep)

/-- product normal form は all-flat tuple に限る。 -/
theorem localDecorationTupleDeletionNormal_iff_eq_flat
    {rs : List ℕ}
    (hPos : ∀ r ∈ rs, 0 < r)
    (A : LocalDecorationTuple rs) :
    LocalDecorationTupleDeletionNormal A ↔
      A = flatLocalDecorationTuple rs hPos := by
  constructor
  · intro hNormal
    have hReach :=
      localDecorationTupleDeletionReachable_to_flat hPos A
    exact LocalDecorationTupleDeletionReachable.eq_of_source_normal hNormal hReach
  · intro hEq
    subst A
    exact flatLocalDecorationTuple_normal rs hPos

/-- 任意二つの product tuples は all-flat normal form で joinable。 -/
theorem localDecorationTupleDeletion_joinable
    {rs : List ℕ}
    (hPos : ∀ r ∈ rs, 0 < r)
    (A B : LocalDecorationTuple rs) :
    ∃ C : LocalDecorationTuple rs,
      LocalDecorationTupleDeletionReachable A C ∧
      LocalDecorationTupleDeletionReachable B C := by
  exact ⟨
    flatLocalDecorationTuple rs hPos,
    localDecorationTupleDeletionReachable_to_flat hPos A,
    localDecorationTupleDeletionReachable_to_flat hPos B
  ⟩

/-! ## 6. pure product-system closure -/

/-- fixed positive length list 上の product deletion system closure data。 -/
structure ProductDecorationDeletionSystemClosed
    (rs : List ℕ)
    (hPos : ∀ r ∈ rs, 0 < r) : Prop where
  termination :
    WellFounded
      (fun B A : LocalDecorationTuple rs =>
        LocalDecorationTupleCellDeletion A B)
  reachability_exact :
    ∀ A B : LocalDecorationTuple rs,
      LocalDecorationTupleDeletionReachable A B ↔
        LocalDecorationTuplePointwiseReachable A B
  every_tuple_normalizes :
    ∀ A : LocalDecorationTuple rs,
      LocalDecorationTupleDeletionReachable
        A (flatLocalDecorationTuple rs hPos)
  normal_form_exact :
    ∀ A : LocalDecorationTuple rs,
      LocalDecorationTupleDeletionNormal A ↔
        A = flatLocalDecorationTuple rs hPos
  joinable :
    ∀ A B : LocalDecorationTuple rs,
      ∃ C : LocalDecorationTuple rs,
        LocalDecorationTupleDeletionReachable A C ∧
        LocalDecorationTupleDeletionReachable B C
  weighted_potential_strict :
    ∀ {A B : LocalDecorationTuple rs},
      LocalDecorationTupleCellDeletion A B →
        B.weightedArea < A.weightedArea

/--
## Product Decoration Deletion System closure theorem

fixed positive skeleton 上の local-decoration state space は、各 factor の local one-cell
deletion の asynchronous direct product である。relation は terminating / globally joinable
で、all-flat tuple を唯一の normal form とし、weighted local-area potential は各 edge で
strict に減少する。
-/
theorem productDecorationDeletionSystem_closed
    (rs : List ℕ)
    (hPos : ∀ r ∈ rs, 0 < r) :
    ProductDecorationDeletionSystemClosed rs hPos := by
  refine {
    termination :=
      localDecorationTupleCellDeletion_wellFounded rs
    reachability_exact := ?_
    every_tuple_normalizes := ?_
    normal_form_exact := ?_
    joinable := ?_
    weighted_potential_strict := ?_
  }
  · intro A B
    exact localDecorationTupleDeletionReachable_iff_pointwise A B
  · intro A
    exact localDecorationTupleDeletionReachable_to_flat hPos A
  · intro A
    exact localDecorationTupleDeletionNormal_iff_eq_flat hPos A
  · intro A B
    exact localDecorationTupleDeletion_joinable hPos A B
  · intro A B hStep
    exact hStep.weightedArea_lt

/-! ## 7. fixed-skeleton actual state space へ product dynamics を exact transport -/

/--
actual fixed-skeleton state 上の canonical product one-cell rewrite。

state-space equivalence が抽出する local-decoration tuples の間で
`LocalDecorationTupleCellDeletion` が成立することを定義とする。
-/
noncomputable def FixedSkeletonProductCellDeletion
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X Y : FixedSkeletonSource P u D) : Prop :=
  LocalDecorationTupleCellDeletion
    X.toLocalDecorationTuple
    Y.toLocalDecorationTuple

/-- actual fixed-skeleton states 上の product reachability。 -/
noncomputable def FixedSkeletonProductDeletionReachable
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X Y : FixedSkeletonSource P u D) : Prop :=
  LocalDecorationTupleDeletionReachable
    X.toLocalDecorationTuple
    Y.toLocalDecorationTuple

/-- actual state の product normality。 -/
noncomputable def FixedSkeletonProductDeletionNormal
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X : FixedSkeletonSource P u D) : Prop :=
  LocalDecorationTupleDeletionNormal
    X.toLocalDecorationTuple

/--
fixed-skeleton actual product dynamics の all-flat source。

`fixedSkeletonSourceEquiv` の inverse で all-flat local tuple を actual source に戻す。
-/
noncomputable def fixedSkeletonProductFlatSource
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FixedSkeletonSource P u D :=
  (fixedSkeletonSourceEquiv
      P hPrimitive hReduced u D).symm
    (flatLocalDecorationTuple D.lengths D.lengths_pos)

/-- fixed-skeleton flat source の extracted tuple は all-flat tuple。 -/
@[simp] theorem fixedSkeletonProductFlatSource_toLocalDecorationTuple
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    (fixedSkeletonProductFlatSource
      P hPrimitive hReduced u D).toLocalDecorationTuple =
      flatLocalDecorationTuple D.lengths D.lengths_pos := by
  change
    (fixedSkeletonSourceEquiv
      P hPrimitive hReduced u D)
      ((fixedSkeletonSourceEquiv
        P hPrimitive hReduced u D).symm
        (flatLocalDecorationTuple D.lengths D.lengths_pos)) =
      flatLocalDecorationTuple D.lengths D.lengths_pos
  exact
    (fixedSkeletonSourceEquiv
      P hPrimitive hReduced u D).apply_symm_apply _

namespace FixedSkeletonProductCellDeletion

/-- transported actual product step は nontrivial。 -/
theorem source_ne
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {X Y : FixedSkeletonSource P u D}
    (h : FixedSkeletonProductCellDeletion X Y) :
    Y ≠ X := by
  intro hEq
  subst Y
  exact h.tuple_ne rfl

/-- actual product step で extracted product cell count は exact に 1 減る。 -/
theorem cellCount_succ
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {X Y : FixedSkeletonSource P u D}
    (h : FixedSkeletonProductCellDeletion X Y) :
    X.toLocalDecorationTuple.cellCount =
      Y.toLocalDecorationTuple.cellCount + 1 := by
  unfold FixedSkeletonProductCellDeletion at h
  exact LocalDecorationTupleCellDeletion.cellCount_succ h

/-- actual product step で local-area product weighted potential は strict に減る。 -/
theorem localAreaProduct_weightedArea_lt
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {X Y : FixedSkeletonSource P u D}
    (h : FixedSkeletonProductCellDeletion X Y) :
    (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D Y).weightedArea <
      (fixedSkeletonLocalAreaTuple
        P hPrimitive hReduced u D X).weightedArea := by
  have hWeighted := h.weightedArea_lt
  rw [
    fixedSkeletonLocalAreaTuple_eq
      P hPrimitive hReduced u D X,
    fixedSkeletonLocalAreaTuple_eq
      P hPrimitive hReduced u D Y
  ]
  simpa only [
    LocalDecorationTuple.weightedArea_eq_toLocalAreaTuple_weightedArea
  ] using hWeighted

end FixedSkeletonProductCellDeletion

/-- transported actual product relation も extracted cell count measure で well-founded。 -/
theorem fixedSkeletonProductCellDeletion_wellFounded
    (P : Word.ContractingExponentPair)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    WellFounded
      (fun Y X : FixedSkeletonSource P u D =>
        FixedSkeletonProductCellDeletion X Y) := by
  refine
    (measure
      (fun X : FixedSkeletonSource P u D =>
        X.toLocalDecorationTuple.cellCount)).wf.mono ?_
  intro Y X hStep
  have h := hStep.cellCount_succ
  change
    Y.toLocalDecorationTuple.cellCount <
      X.toLocalDecorationTuple.cellCount
  omega

/-- actual fixed-skeleton reachability は extracted product reachability そのもの。 -/
theorem fixedSkeletonProductDeletionReachable_iff
    {P : Word.ContractingExponentPair}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    (X Y : FixedSkeletonSource P u D) :
    FixedSkeletonProductDeletionReachable X Y ↔
      LocalDecorationTuplePointwiseReachable
        X.toLocalDecorationTuple
        Y.toLocalDecorationTuple := by
  unfold FixedSkeletonProductDeletionReachable
  exact
    localDecorationTupleDeletionReachable_iff_pointwise
      X.toLocalDecorationTuple
      Y.toLocalDecorationTuple

/-- every actual fixed-skeleton source reaches transported all-flat source。 -/
theorem fixedSkeletonProductDeletionReachable_to_flat
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X : FixedSkeletonSource P u D) :
    FixedSkeletonProductDeletionReachable
      X
      (fixedSkeletonProductFlatSource
        P hPrimitive hReduced u D) := by
  unfold FixedSkeletonProductDeletionReachable
  rw [
    fixedSkeletonProductFlatSource_toLocalDecorationTuple
      P hPrimitive hReduced u D
  ]
  exact
    localDecorationTupleDeletionReachable_to_flat
      D.lengths_pos X.toLocalDecorationTuple

/-- transported product normality は「outgoing actual product edge が無い」と exact に同値。 -/
theorem fixedSkeletonProductDeletionNormal_iff_no_outgoing
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X : FixedSkeletonSource P u D) :
    FixedSkeletonProductDeletionNormal X ↔
      ∀ Y : FixedSkeletonSource P u D,
        ¬ FixedSkeletonProductCellDeletion X Y := by
  constructor
  · intro hNormal Y hStep
    exact hNormal _ hStep
  · intro hNo
    unfold FixedSkeletonProductDeletionNormal
    intro U hStep
    let e :=
      fixedSkeletonSourceEquiv
        P hPrimitive hReduced u D
    let Y : FixedSkeletonSource P u D := e.symm U
    have hY :
        Y.toLocalDecorationTuple = U := by
      change e Y = U
      exact e.apply_symm_apply U
    apply hNo Y
    unfold FixedSkeletonProductCellDeletion
    rw [hY]
    exact hStep

/-- transported actual product normal form は all-flat source に限る。 -/
theorem fixedSkeletonProductDeletionNormal_iff_eq_flat
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X : FixedSkeletonSource P u D) :
    FixedSkeletonProductDeletionNormal X ↔
      X =
        fixedSkeletonProductFlatSource
          P hPrimitive hReduced u D := by
  constructor
  · intro hNormal
    have hTuple :
        X.toLocalDecorationTuple =
          flatLocalDecorationTuple D.lengths D.lengths_pos :=
      (localDecorationTupleDeletionNormal_iff_eq_flat
        D.lengths_pos X.toLocalDecorationTuple).1 hNormal
    apply fixedSkeletonSource_eq_of_same_localDecorationTuple
      P hPrimitive hReduced u D
    simpa using hTuple
  · intro hEq
    subst X
    unfold FixedSkeletonProductDeletionNormal
    rw [
      fixedSkeletonProductFlatSource_toLocalDecorationTuple
        P hPrimitive hReduced u D
    ]
    exact
      flatLocalDecorationTuple_normal
        D.lengths D.lengths_pos

/-- any two actual fixed-skeleton sources are joinable at transported all-flat source。 -/
theorem fixedSkeletonProductDeletion_joinable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (X Y : FixedSkeletonSource P u D) :
    ∃ Z : FixedSkeletonSource P u D,
      FixedSkeletonProductDeletionReachable X Z ∧
      FixedSkeletonProductDeletionReachable Y Z := by
  exact ⟨
    fixedSkeletonProductFlatSource
      P hPrimitive hReduced u D,
    fixedSkeletonProductDeletionReachable_to_flat
      P hPrimitive hReduced u D X,
    fixedSkeletonProductDeletionReachable_to_flat
      P hPrimitive hReduced u D Y
  ⟩

/-! ## 8. actual transported closure package -/

/--
fixed-skeleton actual source space に transport した product deletion system。

ambient global Ferrers cover との追加 compatibility を仮定せず、
state-space product equivalence が与える intrinsic product dynamics だけを束ねる。
-/
structure FixedSkeletonProductDecorationDeletionSystemClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  state_space_product :
    FixedSkeletonDecorationEquivalenceClosed
      P hPrimitive hReduced u D
  pure_product_system :
    ProductDecorationDeletionSystemClosed
      D.lengths D.lengths_pos
  transported_termination :
    WellFounded
      (fun Y X : FixedSkeletonSource P u D =>
        FixedSkeletonProductCellDeletion X Y)
  every_source_normalizes :
    ∀ X : FixedSkeletonSource P u D,
      FixedSkeletonProductDeletionReachable
        X
        (fixedSkeletonProductFlatSource
          P hPrimitive hReduced u D)
  normal_form_exact :
    ∀ X : FixedSkeletonSource P u D,
      FixedSkeletonProductDeletionNormal X ↔
        X =
          fixedSkeletonProductFlatSource
            P hPrimitive hReduced u D
  joinable :
    ∀ X Y : FixedSkeletonSource P u D,
      ∃ Z : FixedSkeletonSource P u D,
        FixedSkeletonProductDeletionReachable X Z ∧
        FixedSkeletonProductDeletionReachable Y Z
  weighted_potential_strict :
    ∀ {X Y : FixedSkeletonSource P u D},
      FixedSkeletonProductCellDeletion X Y →
        (fixedSkeletonLocalAreaTuple
            P hPrimitive hReduced u D Y).weightedArea <
          (fixedSkeletonLocalAreaTuple
            P hPrimitive hReduced u D X).weightedArea

/--
## Fixed Skeleton Product Decoration Deletion System closure theorem

fixed-skeleton actual state space は local decoration factors の exact product state space であり、
その canonical product rewrite は one factor at a time の local one-cell deletion である。
この transported dynamics は terminating / globally joinable で、all-flat source を唯一の
normal form とし、`LocalAreaProduct` の weighted potential は各 edge で strict に減少する。
-/
theorem fixedSkeletonProductDecorationDeletionSystem_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FixedSkeletonProductDecorationDeletionSystemClosed
      P hPrimitive hReduced u D := by
  refine {
    state_space_product :=
      fixedSkeletonDecorationEquivalence_closed
        P hPrimitive hReduced u D
    pure_product_system :=
      productDecorationDeletionSystem_closed
        D.lengths D.lengths_pos
    transported_termination :=
      fixedSkeletonProductCellDeletion_wellFounded
        P u D
    every_source_normalizes := ?_
    normal_form_exact := ?_
    joinable := ?_
    weighted_potential_strict := ?_
  }
  · intro X
    exact
      fixedSkeletonProductDeletionReachable_to_flat
        P hPrimitive hReduced u D X
  · intro X
    exact
      fixedSkeletonProductDeletionNormal_iff_eq_flat
        P hPrimitive hReduced u D X
  · intro X Y
    exact
      fixedSkeletonProductDeletion_joinable
        P hPrimitive hReduced u D X Y
  · intro X Y hStep
    exact hStep.localAreaProduct_weightedArea_lt

end RecordFerrers
end Collatz2
