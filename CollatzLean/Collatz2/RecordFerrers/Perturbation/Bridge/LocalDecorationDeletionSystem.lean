import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationCriticalSubshape
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationAreaDecomposition
import Mathlib.Order.WellFounded

/-!
# Record–Ferrers Perturbation / Local Decoration Deletion System

`LocalDecorationCriticalSubshape` により、positive length `r` の local decoration は
critical Ferrers subshape と exact に同一視された。

本ファイルでは local decoration の Ferrers shape を一セルだけ下げる relation を導入し、

* 一段で ordinary Ferrers area が exact に 1 減る
* relation は well-founded
* zero critical shape に対応する flat local decoration が唯一の normal form
* 任意 local decoration はその flat normal form へ到達
* 任意二経路は flat normal form で合流

を閉じる。

weighted affine cost は cell ごとに一般には 1 ではないが、各 edge は strict positive で、
endpoint の local decoration area difference によって決まる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- critical-subshape space の zero element。 -/
def zeroCriticalSubshape (r : ℕ) : CriticalSubshape r :=
  { shape := FerrersShape.zero r
    below := by
      intro i
      simp [FerrersShape.zero, criticalShape] }

/-- positive length `r` の canonical flat local decoration。 -/
def localFlatDecoration
    (r : ℕ)
    (hr : 0 < r) : LocalDecoration r :=
  (LocalDecoration.equivCriticalSubshape r hr).symm
    (zeroCriticalSubshape r)

/-- flat local decoration の Ferrers shape は all-zero。 -/
theorem localFlatDecoration_ferrersShape
    (r : ℕ)
    (hr : 0 < r) :
    (localFlatDecoration r hr).ferrersShape = FerrersShape.zero r := by
  have h :=
    (LocalDecoration.equivCriticalSubshape r hr).apply_symm_apply
      (zeroCriticalSubshape r)
  have hShape := congrArg CriticalSubshape.shape h
  change
    ((LocalDecoration.equivCriticalSubshape r hr)
        (localFlatDecoration r hr)).shape =
      FerrersShape.zero r at hShape
  rw [LocalDecoration.equivCriticalSubshape_shape] at hShape
  exact hShape

/-- local flat decoration は baseline affine translation を持つ。 -/
theorem localFlatDecoration_affineConst
    (r : ℕ)
    (hr : 0 < r) :
    affineConst (localFlatDecoration r hr).word = baseAffineConst r := by
  have hArea :
      weightedArea (localFlatDecoration r hr).ferrersShape = 0 := by
    rw [localFlatDecoration_ferrersShape]
    exact FerrersShape.weightedArea_zero r
  have h := affineConst_eq_base_add_weightedArea
    (localFlatDecoration r hr).toFiberPoint
  change
    affineConst (localFlatDecoration r hr).word =
      baseAffineConst r +
        weightedArea (localFlatDecoration r hr).ferrersShape at h
  rw [hArea, Nat.add_zero] at h
  exact h

/--
source `A` から target `B` へ一つの local Ferrers cell を削る。
relation の向きは downward normalization に合わせて `A -> B`。
-/
def LocalDecorationCellDeletion
    {r : ℕ}
    (A B : LocalDecoration r) : Prop :=
  FerrersShape.IsUnitCover B.ferrersShape A.ferrersShape

namespace LocalDecorationCellDeletion

/-- 一セル削除は Ferrers inclusion で strict downward。 -/
theorem ferrers_down
    {r : ℕ}
    {A B : LocalDecoration r}
    (h : LocalDecorationCellDeletion A B) :
    B.ferrersShape.Le A.ferrersShape :=
  h.1

/-- 一セル削除で ordinary Ferrers area は exact に 1 減る。 -/
theorem area_succ
    {r : ℕ}
    {A B : LocalDecoration r}
    (h : LocalDecorationCellDeletion A B) :
    FerrersShape.area A.ferrersShape =
      FerrersShape.area B.ferrersShape + 1 :=
  FerrersShape.IsUnitCover.area_succ h

/-- 一セル削除は source / target を同一視しない。 -/
theorem decoration_ne
    {r : ℕ}
    {A B : LocalDecoration r}
    (h : LocalDecorationCellDeletion A B) :
    B ≠ A := by
  intro hEq
  subst B
  have hDist := h.2
  simp at hDist

/-- 一セル削除で local weighted decoration area は strict に減る。 -/
theorem localDecorationArea_lt
    {r : ℕ}
    {A B : LocalDecoration r}
    (h : LocalDecorationCellDeletion A B) :
    localDecorationArea B.word < localDecorationArea A.word := by
  have hLe := weightedArea_mono h.1
  have hNeShape : B.ferrersShape ≠ A.ferrersShape := by
    intro hEq
    have hDist := h.2
    rw [hEq] at hDist
    simp at hDist
  have hNeArea :
      weightedArea B.ferrersShape ≠ weightedArea A.ferrersShape := by
    intro hEq
    have hAffine : affineConst B.word = affineConst A.word := by
      have hB := affineConst_eq_base_add_weightedArea B.toFiberPoint
      have hA := affineConst_eq_base_add_weightedArea A.toFiberPoint
      change affineConst B.word = baseAffineConst r + weightedArea B.ferrersShape at hB
      change affineConst A.word = baseAffineConst r + weightedArea A.ferrersShape at hA
      omega
    have hPoint : B.toFiberPoint = A.toFiberPoint :=
      fiberPoint_eq_of_same_affineConst hAffine
    have hShape := congrArg FiberPoint.toFerrersShape hPoint
    exact hNeShape hShape
  have hStrict :
      weightedArea B.ferrersShape < weightedArea A.ferrersShape := by
    omega
  have hB := affineConst_eq_base_add_weightedArea B.toFiberPoint
  have hA := affineConst_eq_base_add_weightedArea A.toFiberPoint
  change affineConst B.word = baseAffineConst r + weightedArea B.ferrersShape at hB
  change affineConst A.word = baseAffineConst r + weightedArea A.ferrersShape at hA
  unfold localDecorationArea
  rw [B.length_eq, A.length_eq]
  omega

end LocalDecorationCellDeletion

/-- non-flat local decoration には必ず一セル downward step が存在する。 -/
theorem exists_localDecorationCellDeletion_of_ne_flat
    {r : ℕ}
    (hr : 0 < r)
    (A : LocalDecoration r)
    (hNe : A ≠ localFlatDecoration r hr) :
    ∃ B : LocalDecoration r, LocalDecorationCellDeletion A B := by
  have hFlatShape := localFlatDecoration_ferrersShape r hr
  have hShapeNe : A.ferrersShape ≠ FerrersShape.zero r := by
    intro hZero
    apply hNe
    apply (LocalDecoration.equivCriticalSubshape r hr).injective
    apply CriticalSubshape.ext
    change
      A.ferrersShape =
        (localFlatDecoration r hr).ferrersShape
    rw [hFlatShape]
    exact hZero
  have hZeroLe :
      (FerrersShape.zero r).Le A.ferrersShape := by
    intro i
    simp [FerrersShape.zero]
  rcases FerrersShape.exists_unit_predecessor_between
      hZeroLe hShapeNe.symm with
    ⟨C, hZeroC, hCA, hCover⟩
  let S : CriticalSubshape r :=
    { shape := C
      below :=
        FerrersShape.le_trans hCA A.ferrersShape_critical }
  let B : LocalDecoration r :=
    (LocalDecoration.equivCriticalSubshape r hr).symm S
  have hBShape : B.ferrersShape = C := by
    have h :=
      (LocalDecoration.equivCriticalSubshape r hr).apply_symm_apply S
    have hShape := congrArg CriticalSubshape.shape h
    change
      ((LocalDecoration.equivCriticalSubshape r hr) B).shape = C
      at hShape
    rw [LocalDecoration.equivCriticalSubshape_shape] at hShape
    exact hShape
  refine ⟨B, ?_⟩
  unfold LocalDecorationCellDeletion
  rw [hBShape]
  exact hCover

/-- local one-cell deletion の reflexive-transitive finite reachability。 -/
inductive LocalDecorationDeletionReachable
    {r : ℕ} : LocalDecoration r → LocalDecoration r → Prop
  | refl (A : LocalDecoration r) :
      LocalDecorationDeletionReachable A A
  | head
      {A B C : LocalDecoration r} :
      LocalDecorationCellDeletion A B →
      LocalDecorationDeletionReachable B C →
      LocalDecorationDeletionReachable A C

namespace LocalDecorationDeletionReachable

/-- reachability は推移的。 -/
theorem trans
    {r : ℕ}
    {A B C : LocalDecoration r}
    (hAB : LocalDecorationDeletionReachable A B)
    (hBC : LocalDecorationDeletionReachable B C) :
    LocalDecorationDeletionReachable A C := by
  induction hAB with
  | refl => exact hBC
  | head hStep hTail ih =>
      exact LocalDecorationDeletionReachable.head hStep (ih hBC)

/-- reachable なら Ferrers shape は downward。 -/
theorem ferrers_down
    {r : ℕ}
    {A B : LocalDecoration r}
    (h : LocalDecorationDeletionReachable A B) :
    B.ferrersShape.Le A.ferrersShape := by
  induction h with
  | refl => exact FerrersShape.le_refl _
  | head hStep hTail ih =>
      exact FerrersShape.le_trans ih hStep.ferrers_down

end LocalDecorationDeletionReachable

/-- local deletion relation は ordinary area 測度で well-founded。 -/
theorem localDecorationCellDeletion_wellFounded
    (r : ℕ) :
    WellFounded
      (fun B A : LocalDecoration r =>
        LocalDecorationCellDeletion A B) := by
  refine (measure (fun A : LocalDecoration r =>
    FerrersShape.area A.ferrersShape)).wf.mono ?_
  intro B A hStep
  have h :=
    LocalDecorationCellDeletion.area_succ hStep
  change
    FerrersShape.area B.ferrersShape <
      FerrersShape.area A.ferrersShape
  omega

/-- 任意 local decoration は canonical flat local decoration へ有限回で到達する。 -/
theorem localDecorationDeletionReachable_to_flat
    {r : ℕ}
    (hr : 0 < r)
    (A : LocalDecoration r) :
    LocalDecorationDeletionReachable A (localFlatDecoration r hr) := by
  induction A using (measure (fun D : LocalDecoration r =>
    FerrersShape.area D.ferrersShape)).wf.induction with
  | h A ih =>
      by_cases hEq : A = localFlatDecoration r hr
      · subst A
        exact LocalDecorationDeletionReachable.refl _
      · rcases exists_localDecorationCellDeletion_of_ne_flat hr A hEq with
          ⟨B, hStep⟩
        have hLt :
            FerrersShape.area B.ferrersShape <
              FerrersShape.area A.ferrersShape := by
          have hs := hStep.area_succ
          omega
        exact LocalDecorationDeletionReachable.head hStep (ih B hLt)

/-- outgoing one-cell deletion を持たない local decoration。 -/
def LocalDecorationDeletionNormal
    {r : ℕ}
    (A : LocalDecoration r) : Prop :=
  ∀ B : LocalDecoration r, ¬ LocalDecorationCellDeletion A B

/-- flat local decoration は normal。 -/
theorem localFlatDecoration_normal
    (r : ℕ)
    (hr : 0 < r) :
    LocalDecorationDeletionNormal (localFlatDecoration r hr) := by
  intro B hStep
  have hArea :=
    LocalDecorationCellDeletion.area_succ hStep
  have hZeroArea :
      FerrersShape.area (FerrersShape.zero r) = 0 := by
    unfold FerrersShape.area
    apply Finset.sum_eq_zero
    intro k hk
    have hkLt : k < r := Finset.mem_range.mp hk
    simp [FerrersShape.zero, FerrersShape.atNat, hkLt]
  rw [localFlatDecoration_ferrersShape r hr, hZeroArea] at hArea
  omega

/-- local normal form は canonical flat decoration に限る。 -/
theorem localDecorationDeletionNormal_iff_eq_flat
    {r : ℕ}
    (hr : 0 < r)
    (A : LocalDecoration r) :
    LocalDecorationDeletionNormal A ↔
      A = localFlatDecoration r hr := by
  constructor
  · intro hNormal
    by_contra hNe
    rcases exists_localDecorationCellDeletion_of_ne_flat hr A hNe with
      ⟨B, hStep⟩
    exact hNormal B hStep
  · intro hEq
    subst A
    exact localFlatDecoration_normal r hr

/-- 任意二つの local decorations は flat normal form で joinable。 -/
theorem localDecorationDeletion_joinable
    {r : ℕ}
    (hr : 0 < r)
    (A B : LocalDecoration r) :
    ∃ C : LocalDecoration r,
      LocalDecorationDeletionReachable A C ∧
      LocalDecorationDeletionReachable B C := by
  exact ⟨localFlatDecoration r hr,
    localDecorationDeletionReachable_to_flat hr A,
    localDecorationDeletionReachable_to_flat hr B⟩

/-- local deletion system の closure package。 -/
structure LocalDecorationDeletionSystemClosed
    (r : ℕ)
    (hr : 0 < r) : Prop where
  termination :
    WellFounded
      (fun B A : LocalDecoration r =>
        LocalDecorationCellDeletion A B)
  every_decoration_normalizes :
    ∀ A : LocalDecoration r,
      LocalDecorationDeletionReachable A (localFlatDecoration r hr)
  normal_form_exact :
    ∀ A : LocalDecoration r,
      LocalDecorationDeletionNormal A ↔
        A = localFlatDecoration r hr
  joinable :
    ∀ A B : LocalDecoration r,
      ∃ C : LocalDecoration r,
        LocalDecorationDeletionReachable A C ∧
        LocalDecorationDeletionReachable B C

/--
## Local Decoration Deletion System closure theorem

positive fixed length の local decoration space は、zero critical Ferrers shape を唯一の
normal form とする finite-height / terminating / globally joinable one-cell deletion system を持つ。
-/
theorem localDecorationDeletionSystem_closed
    (r : ℕ)
    (hr : 0 < r) :
    LocalDecorationDeletionSystemClosed r hr := by
  refine {
    termination := localDecorationCellDeletion_wellFounded r
    every_decoration_normalizes := ?_
    normal_form_exact := ?_
    joinable := ?_
  }
  · intro A
    exact localDecorationDeletionReachable_to_flat hr A
  · intro A
    exact localDecorationDeletionNormal_iff_eq_flat hr A
  · intro A B
    exact localDecorationDeletion_joinable hr A B

end RecordFerrers
end Collatz2
