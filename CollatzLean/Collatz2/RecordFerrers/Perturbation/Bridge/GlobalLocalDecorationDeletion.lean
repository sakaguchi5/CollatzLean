import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.LocalDecorationDeletionSystem
import CollatzLean.Collatz2.RecordFerrers.Perturbation.Bridge.ArithmeticDecoratedDeletionSystem
import Mathlib.Order.WellFounded

/-!
# Record–Ferrers Perturbation / Global Local Decoration Deletion

local level では one-cell deletion system が閉じた。
本ファイルではそれを actual fixed fiber の genuine `FiberPoint` へ持ち上げる。

重要なのは、単なる「source 以下の Ferrers shape」を全部許すのではなく、

  canonical flat top ≤ x ≤ actual source

という closed Ferrers interval に state space を制限することである。
この区間内では flat top より下の boundary geometry は一切削れない。
従って一セル deletion は source と flat top の差、すなわち decoration cells だけを消す。

主結果:

* interval 内の非-flat actual point には必ず genuine one-cell deletion が存在
* ordinary Ferrers area により termination
* canonical flat top が interval 内の唯一の normal form
* actual source は finite one-cell chain で flat top へ到達
* 各 edge の genuine affine cost は strict positive
* trace total cost は endpoint difference のみで決まり path-independent
* source→flat-top の任意 trace cost は exact に `decorationGap`
* 従って total cost は `2 * localWeightedDecorationArea`

となる。

これにより上段

  actual source -> canonical flat top

も下段 Boolean deletion と同様に genuine finite positive rewrite system になる。

なお本ファイルは「flat-top interval 内の一セル」という意味で局所化している。
各一セルの support をさらに、そのセルを含む canonical record block の open interval へ
縮める `BlockReplacement` refinement は別補題として追加可能である。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- contracting exponent pair を FirstCrossing lattice の chord condition として読む。 -/
theorem ContractingExponentPair.contractingChord
    (P : Word.ContractingExponentPair) :
    ContractingChord P.oddCount P.twoDepth := by
  simpa [ContractingChord] using P.contracting

/--
source point `u` の Ferrers shape 以下にある shape を、同じ fixed fiber の actual point へ復号する。
-/
def fiberPointOfFerrersSubshape
    {p H : ℕ}
    (u : FiberPoint p H)
    (hp : 0 < p)
    (S : FerrersShape p)
    (hSu : S.Le u.toFerrersShape) : FiberPoint p H := by
  let FS : FiberShape p H :=
    { shape := S
      p_pos := hp
      p_le_H := by
        have h := FiberPoint.oddSteps_le_twoSteps_of_valid u.valid
        rw [u.oddSteps_eq, u.twoSteps_eq] at h
        exact h
      first_zero := by
        have h0 := hSu ⟨0, hp⟩
        have hu0 := u.toFerrersShape_first_zero hp
        rw [hu0] at h0
        omega
      bounded := by
        intro i
        exact (hSu i).trans (u.toFerrersShape_bounded i) }
  exact FS.toFiberPoint

/-- subshape decoder は指定した Ferrers shape を exact に持つ。 -/
theorem fiberPointOfFerrersSubshape_shape
    {p H : ℕ}
    (u : FiberPoint p H)
    (hp : 0 < p)
    (S : FerrersShape p)
    (hSu : S.Le u.toFerrersShape) :
    (fiberPointOfFerrersSubshape u hp S hSu).toFerrersShape = S := by
  unfold fiberPointOfFerrersSubshape
  exact FiberShape.toFerrersShape_toFiberPoint _

/-- source が FirstCrossing なら任意の actual subshape decoder も FirstCrossing。 -/
theorem fiberPointOfFerrersSubshape_firstCrossing
    {p H : ℕ}
    (u : FiberPoint p H)
    (hp : 0 < p)
    (hContract : ContractingChord p H)
    (hFu : FirstCrossing u.word)
    (S : FerrersShape p)
    (hSu : S.Le u.toFerrersShape) :
    FirstCrossing (fiberPointOfFerrersSubshape u hp S hSu).word := by
  apply firstCrossing_downward hp hContract hFu
  rw [fiberPointOfFerrersSubshape_shape]
  exact hSu

/-! ## 1. actual→flat-top decoration interval -/

/--
上段 decoration normalization が動く exact state space。
flat top より上、original actual source より下で、FirstCrossing である actual points。
-/
def InDecorationInterval
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (x : FiberPoint P.oddCount P.twoDepth) : Prop :=
  FiberPoint.FerrersLe
      (canonicalFlatTop P hPrimitive hReduced u D) x ∧
    FiberPoint.FerrersLe x u ∧
    FirstCrossing x.word

/-- original actual source 自身は decoration interval の上端。 -/
theorem source_mem_decorationInterval
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    InDecorationInterval P hPrimitive hReduced u D u := by
  refine ⟨
    canonicalFlatTop_ferrersLe_source
      P hPrimitive hReduced u D,
    FerrersShape.le_refl _,
    D.whole_firstCrossing
  ⟩

/-- canonical flat top は decoration interval の下端。 -/
theorem flatTop_mem_decorationInterval
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    InDecorationInterval P hPrimitive hReduced u D
      (canonicalFlatTop P hPrimitive hReduced u D) := by
  have hLe := canonicalFlatTop_ferrersLe_source
    P hPrimitive hReduced u D
  have hContract :
      ContractingChord P.oddCount P.twoDepth :=
    ContractingExponentPair.contractingChord P
  have hFirst :
      FirstCrossing (canonicalFlatTop P hPrimitive hReduced u D).word := by
    exact firstCrossing_downward
      P.oddCount_pos
      hContract
      D.whole_firstCrossing
      hLe
  exact ⟨FerrersShape.le_refl _, hLe, hFirst⟩

/--
flat top と original source が同じ column を持つ cut は interval 全体で frozen。
従って decoration normalization はその cut を動かせない。
-/
theorem decorationInterval_frozen_column
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {x : FiberPoint P.oddCount P.twoDepth}
    (hx : InDecorationInterval P hPrimitive hReduced u D x)
    (i : Fin P.oddCount)
    (hFrozen :
      (canonicalFlatTop P hPrimitive hReduced u D).toFerrersShape.column i =
        u.toFerrersShape.column i) :
    x.toFerrersShape.column i =
      u.toFerrersShape.column i := by
  have hLower := hx.1 i
  have hUpper := hx.2.1 i
  omega

/-! ## 2. one-cell actual decoration deletion -/

/--
interval 内で source `x` から target `y` へ一つの decoration cell だけを削る。
`target_interval` により flat top より下へは絶対に進まない。
-/
structure ActualLocalFerrersCellDeletion
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (x y : FiberPoint P.oddCount P.twoDepth) : Prop where
  source_interval :
    InDecorationInterval P hPrimitive hReduced u D x
  target_interval :
    InDecorationInterval P hPrimitive hReduced u D y
  unit_cover :
    FerrersShape.IsUnitCover y.toFerrersShape x.toFerrersShape

namespace ActualLocalFerrersCellDeletion

/-- one-cell actual deletion は Ferrers inclusion で downward。 -/
theorem ferrers_down
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y) :
    y.toFerrersShape.Le x.toFerrersShape :=
  A.unit_cover.1

/-- one-cell actual deletion は source / target を同一視しない。 -/
theorem point_ne
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y) :
    y ≠ x := by
  intro hEq
  subst y
  have hDist := A.unit_cover.2
  simp at hDist

/-- one-cell actual deletion では ordinary Ferrers area が exact に 1 減る。 -/
theorem area_succ
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y) :
    FerrersShape.area x.toFerrersShape =
      FerrersShape.area y.toFerrersShape + 1 :=
  FerrersShape.IsUnitCover.area_succ A.unit_cover

/-- one-cell actual deletion では genuine affine potential が strict に減る。 -/
theorem affineConst_lt
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y) :
    affineConst y.word < affineConst x.word := by
  have hAreaLe := weightedArea_mono A.ferrers_down
  have hAffineLe : affineConst y.word ≤ affineConst x.word := by
    rw [affineConst_eq_base_add_weightedArea,
        affineConst_eq_base_add_weightedArea]
    exact Nat.add_le_add_left hAreaLe _
  have hAffineNe : affineConst y.word ≠ affineConst x.word := by
    intro hEq
    have hPoint : y = x := fiberPoint_eq_of_same_affineConst hEq
    exact A.point_ne hPoint
  omega

/-- 一セル actual decoration deletion の genuine affine cost。 -/
def cost
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (_A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y) : ℕ :=
  affineConst x.word - affineConst y.word

/-- every actual decoration-cell edge has positive affine cost。 -/
theorem cost_pos
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y) :
    0 < A.cost := by
  unfold cost
  have h := A.affineConst_lt
  omega

/-- interval の frozen column は one-cell step の前後で不変。 -/
theorem preserves_frozen_column
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (A : ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y)
    (i : Fin P.oddCount)
    (hFrozen :
      (canonicalFlatTop P hPrimitive hReduced u D).toFerrersShape.column i =
        u.toFerrersShape.column i) :
    y.toFerrersShape.column i = x.toFerrersShape.column i := by
  have hx := decorationInterval_frozen_column
    P hPrimitive hReduced u D A.source_interval i hFrozen
  have hy := decorationInterval_frozen_column
    P hPrimitive hReduced u D A.target_interval i hFrozen
  exact hy.trans hx.symm

/--
同一 fixed fiber の任意の二点は、whole interval `[0,p]` を support とする
`BlockReplacement` で結ばれる。

この whole-fiber specialization では区間外は terminal endpoints `0,p` だけであり、
両 endpoint height は fixed-fiber 条件から自動的に一致する。
従って内部の deformation の性質は一切要求しない。

局所性を表す実質的な情報は、proper subinterval
`BlockReplacement x y start stop`
（`0 < start` または `stop < p`）で初めて現れる。
-/
theorem blockReplacement_zero_terminal
    {P : Word.ContractingExponentPair}
    {x y : FiberPoint P.oddCount P.twoDepth} :
    BlockReplacement x y 0 P.oddCount := by
  refine {
    start_lt_stop := P.oddCount_pos
    stop_le_terminal := le_rfl
    outside := ?_
  }
  intro k hkp hOutside
  rcases hOutside with hk0 | hpk
  · have hk : k = 0 := by omega
    subst k
    unfold profileDisplacement
    simp
  · have hk : k = P.oddCount := by omega
    subst k
    unfold profileDisplacement
    simp

end ActualLocalFerrersCellDeletion

/-! ## 3. existence / termination / normal form -/

/--
decoration interval 内の canonical flat top でない actual point には、
Ferrers shape をちょうど一セルだけ下げる actual local deletion が必ず存在する。

得られる target は同じ decoration interval に留まり、
FirstCrossing も保持される。
-/
theorem exists_actualLocalFerrersCellDeletion_of_ne_flatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (x : FiberPoint P.oddCount P.twoDepth)
    (hx : InDecorationInterval P hPrimitive hReduced u D x)
    (hNe : x ≠ canonicalFlatTop P hPrimitive hReduced u D) :
    ∃ y : FiberPoint P.oddCount P.twoDepth,
      ActualLocalFerrersCellDeletion
        P hPrimitive hReduced u D x y := by
  let f := canonicalFlatTop P hPrimitive hReduced u D
  have hShapeNe : f.toFerrersShape ≠ x.toFerrersShape := by
    intro hEq
    apply hNe
    exact FiberPoint.toFerrersShape_injective hEq.symm
  rcases FerrersShape.exists_unit_predecessor_between
      hx.1 hShapeNe with
    ⟨C, hFlatC, hCx, hCover⟩
  have hCu : C.Le u.toFerrersShape :=
    FerrersShape.le_trans hCx hx.2.1
  let y : FiberPoint P.oddCount P.twoDepth :=
    fiberPointOfFerrersSubshape u P.oddCount_pos C hCu
  have hyShape : y.toFerrersShape = C :=
    fiberPointOfFerrersSubshape_shape
      u P.oddCount_pos C hCu
  have hyFirst : FirstCrossing y.word :=
    fiberPointOfFerrersSubshape_firstCrossing
      u
      P.oddCount_pos
      (ContractingExponentPair.contractingChord P)
      D.whole_firstCrossing
      C
      hCu
  have hyInterval :
      InDecorationInterval P hPrimitive hReduced u D y := by
    refine ⟨?_, ?_, hyFirst⟩
    · change
        (canonicalFlatTop P hPrimitive hReduced u D).toFerrersShape.Le
          y.toFerrersShape
      rw [hyShape]
      exact hFlatC
    · change
        y.toFerrersShape.Le u.toFerrersShape
      rw [hyShape]
      exact hCu
  refine ⟨y, ?_⟩
  refine {
    source_interval := hx
    target_interval := hyInterval
    unit_cover := ?_
  }
  rw [hyShape]
  exact hCover

/-- actual decoration one-cell deletion の finite reachability。 -/
inductive ActualLocalFerrersDeletionReachable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FiberPoint P.oddCount P.twoDepth →
    FiberPoint P.oddCount P.twoDepth → Prop
  | refl (x : FiberPoint P.oddCount P.twoDepth) :
      ActualLocalFerrersDeletionReachable
        P hPrimitive hReduced u D x x
  | tail
      {x y z : FiberPoint P.oddCount P.twoDepth} :
      ActualLocalFerrersDeletionReachable
        P hPrimitive hReduced u D x y →
      ActualLocalFerrersCellDeletion
        P hPrimitive hReduced u D y z →
      ActualLocalFerrersDeletionReachable
        P hPrimitive hReduced u D x z

namespace ActualLocalFerrersDeletionReachable

/-- reachability は推移的。 -/
theorem trans
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y z : FiberPoint P.oddCount P.twoDepth}
    (hxy : ActualLocalFerrersDeletionReachable
      P hPrimitive hReduced u D x y)
    (hyz : ActualLocalFerrersDeletionReachable
      P hPrimitive hReduced u D y z) :
    ActualLocalFerrersDeletionReachable
      P hPrimitive hReduced u D x z := by
  induction hyz with
  | refl => exact hxy
  | tail hAB hBC ih =>
      exact ActualLocalFerrersDeletionReachable.tail ih hBC

/-- reachable endpoint は Ferrers inclusion で source 以下。 -/
theorem ferrers_down
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (h : ActualLocalFerrersDeletionReachable
      P hPrimitive hReduced u D x y) :
    y.toFerrersShape.Le x.toFerrersShape := by
  induction h with
  | refl => exact FerrersShape.le_refl _
  | tail hReach hStep ih =>
      exact FerrersShape.le_trans hStep.ferrers_down ih

end ActualLocalFerrersDeletionReachable

/-- relative decoration deletion relation は ordinary Ferrers area で well-founded。 -/
theorem actualLocalFerrersCellDeletion_wellFounded
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    WellFounded
      (fun y x : FiberPoint P.oddCount P.twoDepth =>
        ActualLocalFerrersCellDeletion
          P hPrimitive hReduced u D x y) := by
  refine (measure (fun x : FiberPoint P.oddCount P.twoDepth =>
    FerrersShape.area x.toFerrersShape)).wf.mono ?_
  intro y x hStep
  have h := hStep.area_succ
  change
    FerrersShape.area y.toFerrersShape <
      FerrersShape.area x.toFerrersShape
  omega

/-- interval の任意 point は canonical flat top へ有限回で到達する。 -/
theorem actualLocalFerrersDeletionReachable_to_flatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (x : FiberPoint P.oddCount P.twoDepth)
    (hx : InDecorationInterval P hPrimitive hReduced u D x) :
    ActualLocalFerrersDeletionReachable
      P hPrimitive hReduced u D x
      (canonicalFlatTop P hPrimitive hReduced u D) := by
  revert hx
  induction x using (measure (fun z : FiberPoint P.oddCount P.twoDepth =>
    FerrersShape.area z.toFerrersShape)).wf.induction with
  | h x ih =>
      intro hx
      by_cases hEq : x = canonicalFlatTop P hPrimitive hReduced u D
      · subst x
        exact ActualLocalFerrersDeletionReachable.refl _
      · rcases exists_actualLocalFerrersCellDeletion_of_ne_flatTop
          P hPrimitive hReduced u D x hx hEq with
          ⟨y, hStep⟩
        have hLt :
            FerrersShape.area y.toFerrersShape <
              FerrersShape.area x.toFerrersShape := by
          have hs := hStep.area_succ
          omega
        have hYFlat := ih y hLt hStep.target_interval
        have hXY : ActualLocalFerrersDeletionReachable
            P hPrimitive hReduced u D x y :=
          ActualLocalFerrersDeletionReachable.tail
            (ActualLocalFerrersDeletionReachable.refl x) hStep
        exact ActualLocalFerrersDeletionReachable.trans hXY hYFlat

/-- original actual source は genuine one-cell decoration deletions で flat top へ到達。 -/
theorem actualLocalFerrersDeletionReachable_source_to_flatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ActualLocalFerrersDeletionReachable
      P hPrimitive hReduced u D u
      (canonicalFlatTop P hPrimitive hReduced u D) :=
  actualLocalFerrersDeletionReachable_to_flatTop
    P hPrimitive hReduced u D u
    (source_mem_decorationInterval P hPrimitive hReduced u D)

/-- interval 内で outgoing decoration deletion を持たないこと。 -/
def ActualLocalFerrersDeletionNormal
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (x : FiberPoint P.oddCount P.twoDepth) : Prop :=
  ∀ y : FiberPoint P.oddCount P.twoDepth,
    ¬ ActualLocalFerrersCellDeletion
      P hPrimitive hReduced u D x y

/-- flat top は relative decoration system の normal form。 -/
theorem canonicalFlatTop_actualLocalFerrersDeletionNormal
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ActualLocalFerrersDeletionNormal
      P hPrimitive hReduced u D
      (canonicalFlatTop P hPrimitive hReduced u D) := by
  intro y hStep
  have hLower := hStep.target_interval.1
  have hUpper := hStep.ferrers_down
  have hShape :
      y.toFerrersShape =
        (canonicalFlatTop P hPrimitive hReduced u D).toFerrersShape :=
    FerrersShape.le_antisymm hUpper hLower
  have hDist := hStep.unit_cover.2
  rw [hShape] at hDist
  simp at hDist

/-- interval 内の normal form は canonical flat top に限る。 -/
theorem actualLocalFerrersDeletionNormal_iff_eq_flatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (x : FiberPoint P.oddCount P.twoDepth)
    (hx : InDecorationInterval P hPrimitive hReduced u D x) :
    ActualLocalFerrersDeletionNormal
        P hPrimitive hReduced u D x ↔
      x = canonicalFlatTop P hPrimitive hReduced u D := by
  constructor
  · intro hNormal
    by_contra hNe
    rcases exists_actualLocalFerrersCellDeletion_of_ne_flatTop
      P hPrimitive hReduced u D x hx hNe with ⟨y, hStep⟩
    exact hNormal y hStep
  · intro hEq
    subst x
    exact canonicalFlatTop_actualLocalFerrersDeletionNormal
      P hPrimitive hReduced u D

/-- interval の任意二点は flat top で joinable。 -/
theorem actualLocalFerrersDeletion_joinable
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    (x y : FiberPoint P.oddCount P.twoDepth)
    (hx : InDecorationInterval P hPrimitive hReduced u D x)
    (hy : InDecorationInterval P hPrimitive hReduced u D y) :
    ∃ z : FiberPoint P.oddCount P.twoDepth,
      ActualLocalFerrersDeletionReachable
        P hPrimitive hReduced u D x z ∧
      ActualLocalFerrersDeletionReachable
        P hPrimitive hReduced u D y z := by
  exact ⟨canonicalFlatTop P hPrimitive hReduced u D,
    actualLocalFerrersDeletionReachable_to_flatTop
      P hPrimitive hReduced u D x hx,
    actualLocalFerrersDeletionReachable_to_flatTop
      P hPrimitive hReduced u D y hy⟩

/-! ## 4. arithmetic trace cost -/

/-- actual decoration-cell trace と各 genuine affine loss の総和。 -/
inductive ActualLocalFerrersTraceCost
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    FiberPoint P.oddCount P.twoDepth →
    FiberPoint P.oddCount P.twoDepth → ℕ → Prop
  | refl (x : FiberPoint P.oddCount P.twoDepth) :
      ActualLocalFerrersTraceCost
        P hPrimitive hReduced u D x x 0
  | tail
      {x y z : FiberPoint P.oddCount P.twoDepth}
      {c : ℕ} :
      ActualLocalFerrersTraceCost
        P hPrimitive hReduced u D x y c →
      (A : ActualLocalFerrersCellDeletion
        P hPrimitive hReduced u D y z) →
      ActualLocalFerrersTraceCost
        P hPrimitive hReduced u D x z (c + A.cost)

namespace ActualLocalFerrersTraceCost

/-- trace endpoint affine potential は source 以下。 -/
theorem affine_le
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    {c : ℕ}
    (T : ActualLocalFerrersTraceCost
      P hPrimitive hReduced u D x y c) :
    affineConst y.word ≤ affineConst x.word := by
  induction T with
  | refl => exact le_rfl
  | tail hTrace A ih =>
      exact (Nat.le_of_lt A.affineConst_lt).trans ih

/-- trace cost は endpoint affine difference に exact に一致する。 -/
theorem eq_endpoint_difference
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    {c : ℕ}
    (T : ActualLocalFerrersTraceCost
      P hPrimitive hReduced u D x y c) :
    c = affineConst x.word - affineConst y.word := by
  induction T with
  | refl => simp
  | @tail y z c hTrace A ih =>
      have hyx : affineConst y.word ≤ affineConst x.word :=
        affine_le hTrace
      have hzy : affineConst z.word ≤ affineConst y.word :=
        Nat.le_of_lt A.affineConst_lt
      rw [ih]
      unfold ActualLocalFerrersCellDeletion.cost
      omega

/-- 同じ endpoints の decoration-cell traces は総 cost が一意。 -/
theorem path_independent
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    {c d : ℕ}
    (Tc : ActualLocalFerrersTraceCost
      P hPrimitive hReduced u D x y c)
    (Td : ActualLocalFerrersTraceCost
      P hPrimitive hReduced u D x y d) :
    c = d := by
  calc
    c = affineConst x.word - affineConst y.word := Tc.eq_endpoint_difference
    _ = d := Td.eq_endpoint_difference.symm

end ActualLocalFerrersTraceCost

/-- reachability には cost trace が存在する。 -/
theorem exists_actualLocalFerrersTraceCost_of_reachable
    {P : Word.ContractingExponentPair}
    {hPrimitive : P.IsPrimitive}
    {hReduced : P.StripReduced}
    {u : FiberPoint P.oddCount P.twoDepth}
    {D : RecordDecomposition u 1}
    {x y : FiberPoint P.oddCount P.twoDepth}
    (h : ActualLocalFerrersDeletionReachable
      P hPrimitive hReduced u D x y) :
    ∃ c : ℕ,
      ActualLocalFerrersTraceCost
        P hPrimitive hReduced u D x y c := by
  induction h with
  | refl =>
      exact ⟨0, ActualLocalFerrersTraceCost.refl _⟩
  | tail hReach A ih =>
      rcases ih with ⟨c, hTrace⟩
      exact ⟨c + A.cost, ActualLocalFerrersTraceCost.tail hTrace A⟩

/--
## 主定理: 任意 source→flat-top one-cell trace の総 cost は `decorationGap`。
-/
theorem actualLocalFerrersTraceCost_to_flatTop_eq_decorationGap
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {c : ℕ}
    (T : ActualLocalFerrersTraceCost
      P hPrimitive hReduced u D u
      (canonicalFlatTop P hPrimitive hReduced u D) c) :
    c = decorationGap P hPrimitive hReduced u D := by
  have hEnd := T.eq_endpoint_difference
  have hAffine := affineConst_eq_flatTop_add_decorationGap
    P hPrimitive hReduced u D
  omega

/-- canonical source→flat-top one-cell trace exists with exact `decorationGap` cost。 -/
theorem exists_actualLocalFerrersTraceCost_to_flatTop
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    ActualLocalFerrersTraceCost
      P hPrimitive hReduced u D u
      (canonicalFlatTop P hPrimitive hReduced u D)
      (decorationGap P hPrimitive hReduced u D) := by
  have hReach := actualLocalFerrersDeletionReachable_source_to_flatTop
    P hPrimitive hReduced u D
  rcases exists_actualLocalFerrersTraceCost_of_reachable hReach with
    ⟨c, hTrace⟩
  have hEq := actualLocalFerrersTraceCost_to_flatTop_eq_decorationGap
    P hPrimitive hReduced u D hTrace
  simpa [hEq] using hTrace

/-- source→flat-top trace cost は local weighted decoration area の exact 2 倍。 -/
theorem actualLocalFerrersTraceCost_to_flatTop_eq_two_mul_localWeightedDecorationArea
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1)
    {c : ℕ}
    (T : ActualLocalFerrersTraceCost
      P hPrimitive hReduced u D u
      (canonicalFlatTop P hPrimitive hReduced u D) c) :
    c = 2 * localWeightedDecorationArea P u D := by
  rw [actualLocalFerrersTraceCost_to_flatTop_eq_decorationGap
    P hPrimitive hReduced u D T]
  exact decorationGap_eq_two_mul_localWeightedDecorationArea
    P hPrimitive hReduced u D

/-! ## 5. closure package -/

/-- global actual local-decoration one-cell system の closure data。 -/
structure GlobalLocalDecorationDeletionClosed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) : Prop where
  termination :
    WellFounded
      (fun y x : FiberPoint P.oddCount P.twoDepth =>
        ActualLocalFerrersCellDeletion
          P hPrimitive hReduced u D x y)
  source_interval :
    InDecorationInterval P hPrimitive hReduced u D u
  flat_interval :
    InDecorationInterval P hPrimitive hReduced u D
      (canonicalFlatTop P hPrimitive hReduced u D)
  source_normalizes :
    ActualLocalFerrersDeletionReachable
      P hPrimitive hReduced u D u
      (canonicalFlatTop P hPrimitive hReduced u D)
  interval_normal_form_exact :
    ∀ x : FiberPoint P.oddCount P.twoDepth,
      InDecorationInterval P hPrimitive hReduced u D x →
      (ActualLocalFerrersDeletionNormal
          P hPrimitive hReduced u D x ↔
        x = canonicalFlatTop P hPrimitive hReduced u D)
  canonical_trace :
    ActualLocalFerrersTraceCost
      P hPrimitive hReduced u D u
      (canonicalFlatTop P hPrimitive hReduced u D)
      (decorationGap P hPrimitive hReduced u D)
  trace_cost_exact :
    ∀ {c : ℕ},
      ActualLocalFerrersTraceCost
          P hPrimitive hReduced u D u
          (canonicalFlatTop P hPrimitive hReduced u D) c →
        c = decorationGap P hPrimitive hReduced u D
  trace_cost_area_exact :
    ∀ {c : ℕ},
      ActualLocalFerrersTraceCost
          P hPrimitive hReduced u D u
          (canonicalFlatTop P hPrimitive hReduced u D) c →
        c = 2 * localWeightedDecorationArea P u D

/--
## Global Local Decoration Deletion closure theorem

actual source→canonical flat top の上段は、flat-top interval に閉じた genuine one-cell
Ferrers rewrite system として finite-height / terminating であり、flat top が interval 内の
唯一の normal form である。任意 source→flat-top trace の genuine affine cost は
path-independent で `decorationGap = 2 * localWeightedDecorationArea` に exact に一致する。
-/
theorem globalLocalDecorationDeletion_closed
    (P : Word.ContractingExponentPair)
    (hPrimitive : P.IsPrimitive)
    (hReduced : P.StripReduced)
    (u : FiberPoint P.oddCount P.twoDepth)
    (D : RecordDecomposition u 1) :
    GlobalLocalDecorationDeletionClosed
      P hPrimitive hReduced u D := by
  refine {
    termination := actualLocalFerrersCellDeletion_wellFounded
      P hPrimitive hReduced u D
    source_interval := source_mem_decorationInterval
      P hPrimitive hReduced u D
    flat_interval := flatTop_mem_decorationInterval
      P hPrimitive hReduced u D
    source_normalizes := actualLocalFerrersDeletionReachable_source_to_flatTop
      P hPrimitive hReduced u D
    interval_normal_form_exact := ?_
    canonical_trace := exists_actualLocalFerrersTraceCost_to_flatTop
      P hPrimitive hReduced u D
    trace_cost_exact := ?_
    trace_cost_area_exact := ?_
  }
  · intro x hx
    exact actualLocalFerrersDeletionNormal_iff_eq_flatTop
      P hPrimitive hReduced u D x hx
  · intro c T
    exact actualLocalFerrersTraceCost_to_flatTop_eq_decorationGap
      P hPrimitive hReduced u D T
  · intro c T
    exact actualLocalFerrersTraceCost_to_flatTop_eq_two_mul_localWeightedDecorationArea
      P hPrimitive hReduced u D T

end RecordFerrers
end Collatz2
