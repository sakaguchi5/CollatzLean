import CollatzLean.Collatz2.RecordFerrers.Reconstruction.TranslationCoordinates
import CollatzLean.Collatz2.RecordFerrers.Lattice.MetricCompletion
import Mathlib.Order.WellFounded

/-!
# Record–Ferrers Perturbation / Local Decoration Critical Subshape

fixed length `r` の valid minimal local block は、terminal depth を
`minimalDepth r` に固定した FirstCrossing fiber の一点である。

したがって positive length では既存の universal equivalence

  FirstCrossingFiber r (minimalDepth r) ≃ CriticalSubshape r

を通じて、local decoration 自体を critical Ferrers subshape と exact に同一視できる。

さらに本ファイルでは Ferrers inclusion `A ≤ B` の間を one-cell cover で埋める
unit-chain existence を補う。これにより local decoration の Ferrers shape を
一セルずつ flat bottom へ降ろすための純粋な combinatorial substrate が得られる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- minimal terminal depth は contracting chord を与える。 -/
theorem minimalDepth_contractingChord
    (r : ℕ)
    (hr : 0 < r) :
    ContractingChord r (minimalDepth r) := by
  have h := (ContractingExponentPair.criticalUpperPair r hr).contracting
  simpa [ContractingChord, minimalDepth] using h

namespace LocalDecoration

/-- local decoration を exact fixed local fiber の point として読む。 -/
def toFiberPoint
    {r : ℕ}
    (D : LocalDecoration r) :
    FiberPoint r (minimalDepth r) :=
  { word := D.word
    valid := D.validMinimal.valid
    oddSteps_eq := D.length_eq
    twoSteps_eq := by
      have h := D.validMinimal.toMinimalBlock.minimalDepth
      rw [D.length_eq] at h
      simpa [minimalDepth] using h }

/-- local decoration は local FirstCrossing fiber の一点。 -/
def toFirstCrossingFiber
    {r : ℕ}
    (D : LocalDecoration r) :
    FirstCrossingFiber r (minimalDepth r) :=
  ⟨D.toFiberPoint, D.validMinimal.toMinimalBlock.firstCrossing⟩

/-- fixed local FirstCrossing point から valid minimal local decoration を戻す。 -/
def ofFirstCrossingFiber
    {r : ℕ}
    (X : FirstCrossingFiber r (minimalDepth r)) :
    LocalDecoration r :=
  { word := X.1.word
    validMinimal :=
      { toMinimalBlock :=
          { firstCrossing := X.2
            minimalDepth := by
              have h := X.1.twoSteps_eq
              rw [X.1.oddSteps_eq]
              simpa [minimalDepth] using h }
        valid := X.1.valid }
    length_eq := X.1.oddSteps_eq }

/--
local decoration と minimal-depth FirstCrossing fiber の exact equivalence。
-/
def equivFirstCrossingFiber
    (r : ℕ) :
    LocalDecoration r ≃ FirstCrossingFiber r (minimalDepth r) where
  toFun := toFirstCrossingFiber
  invFun := ofFirstCrossingFiber
  left_inv := by
    intro D
    apply LocalDecoration.ext
    rfl
  right_inv := by
    intro X
    apply Subtype.ext
    apply FiberPoint.toFerrersShape_injective
    rfl

/--
## 主定理 1

positive local length `r` では local decoration space は universal critical Ferrers
subshape space と exact に同値。
-/
def equivCriticalSubshape
    (r : ℕ)
    (hr : 0 < r) :
    LocalDecoration r ≃ CriticalSubshape r :=
  (equivFirstCrossingFiber r).trans
    (FirstCrossingFiber.equivCriticalSubshape
      hr (minimalDepth_contractingChord r hr))

/-- local decoration の underlying Ferrers profile。 -/
def ferrersShape
    {r : ℕ}
    (D : LocalDecoration r) : FerrersShape r :=
  D.toFiberPoint.toFerrersShape

/-- local decoration の Ferrers profile は critical roof 以下。 -/
theorem ferrersShape_critical
    {r : ℕ}
    (D : LocalDecoration r) :
    IsCriticalSubshape D.ferrersShape := by
  have hr : 0 < r := by
    have h := D.validMinimal.toMinimalBlock.oddSteps_pos
    rw [D.length_eq] at h
    exact h
  have hContract := minimalDepth_contractingChord r hr
  exact
    (firstCrossing_iff_criticalSubshape D.toFiberPoint hr hContract).1
      D.validMinimal.toMinimalBlock.firstCrossing

/-- equivalence の critical shape は `ferrersShape` そのもの。 -/
theorem equivCriticalSubshape_shape
    {r : ℕ}
    (hr : 0 < r)
    (D : LocalDecoration r) :
    (equivCriticalSubshape r hr D).shape = D.ferrersShape := by
  rfl

end LocalDecoration

/-! ## Ferrers one-cell completion -/

namespace FerrersShape

/--
`A < B` の最初の strict column を一セル下げると、`A ≤ C < B` の one-cell predecessor が得られる。
-/
theorem exists_unit_predecessor_between
    {p : ℕ}
    {A B : FerrersShape p}
    (hAB : A.Le B)
    (hNe : A ≠ B) :
    ∃ C : FerrersShape p,
      A.Le C ∧ C.Le B ∧ IsUnitCover C B := by
  have hStrict : ∃ i : Fin p, A.column i < B.column i := by
    by_contra hNo
    have hBA : B.Le A := by
      intro i
      apply Nat.le_of_not_gt
      intro hlt
      exact hNo ⟨i, hlt⟩
    exact hNe (FerrersShape.le_antisymm hAB hBA)
  let S : Finset (Fin p) :=
    Finset.univ.filter (fun i => A.column i < B.column i)
  have hSNonempty : S.Nonempty := by
    rcases hStrict with ⟨i, hi⟩
    exact ⟨i, by simp [S, hi]⟩
  let i : Fin p := S.min' hSNonempty
  have hiMem : i ∈ S := Finset.min'_mem S hSNonempty
  have hiStrict : A.column i < B.column i := by
    simpa [S] using hiMem
  have hiPos : 0 < B.column i := by omega
  let C : FerrersShape p :=
    { column := fun j => if j = i then B.column j - 1 else B.column j
      mono := by
        intro a b hab
        by_cases hai : a = i
        · subst a
          by_cases hbi : b = i
          · subst b
            rfl
          · simp [hbi]
            have hmono := B.mono hab
            omega
        · by_cases hbi : b = i
          · subst b
            simp only [hai, ↓reduceIte]
            have habLt : a < i := lt_of_le_of_ne hab hai
            have hAiBi : A.column a = B.column a := by
              apply Nat.le_antisymm (hAB a)
              apply Nat.le_of_not_gt
              intro haStrict
              have haMem : a ∈ S := by
                simp [S, haStrict]
              have hMin : i ≤ a := Finset.min'_le S a haMem
              exact (not_le_of_gt habLt) hMin
            have hAmono : A.column a ≤ A.column i := A.mono (Nat.le_of_lt habLt)
            rw [← hAiBi]
            omega
          · simp only [hai, ↓reduceIte, hbi]
            exact B.mono hab }
  have hAC : A.Le C := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [C]
      omega
    · simp only [hji, ↓reduceIte, C]
      exact hAB j
  have hCB : C.Le B := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [C]
    · simp [C, hji]
  have hArea : area B = area C + 1 := by
    unfold area
    have hiRange : i.1 ∈ Finset.range p := Finset.mem_range.mpr i.isLt
    calc
      Finset.sum (Finset.range p) (fun k => B.atNat k)
          = Finset.sum (Finset.range p) (fun k =>
              C.atNat k + if k = i.1 then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hkLt : k < p := Finset.mem_range.mp hk
              by_cases hki : k = i.1
              · subst k
                simp [FerrersShape.atNat, i.isLt, C]
                omega
              · have hFin : (⟨k, hkLt⟩ : Fin p) ≠ i := by
                  intro hEq
                  exact hki (congrArg Fin.val hEq)
                simp [FerrersShape.atNat, hkLt, C, hFin, hki]
      _ = Finset.sum (Finset.range p) (fun k => C.atNat k) +
            Finset.sum (Finset.range p) (fun k => if k = i.1 then 1 else 0) := by
              rw [Finset.sum_add_distrib]
      _ = Finset.sum (Finset.range p) (fun k => C.atNat k) + 1 := by
              simp [hiRange]
  have hCover : IsUnitCover C B :=
    isUnitCover_of_le_area_succ hCB hArea
  exact ⟨C, hAC, hCB, hCover⟩

namespace UnitChain

/-- unit chains の連結。 -/
theorem trans
    {p : ℕ}
    {A B C : FerrersShape p}
    {m n : ℕ}
    (hAB : UnitChain A B m)
    (hBC : UnitChain B C n) :
    UnitChain A C (m + n) := by
  induction hAB with
  | refl A =>
      simpa using hBC
  | @cons A B D k hHead hTail ih =>
      have hRest := ih hBC
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        UnitChain.cons hHead hRest

end UnitChain

/--
## 主定理 2

任意の comparable Ferrers shapes `A ≤ B` は one-cell cover の有限列で結ばれる。
既存 `UnitChain.distance_eq_steps` と合わせると、その長さは endpoint distance に一致する。
-/
theorem exists_unitChain_of_le
    {p : ℕ}
    {A B : FerrersShape p}
    (hAB : A.Le B) :
    ∃ n : ℕ, UnitChain A B n := by
  revert hAB
  induction B using (measure area).wf.induction with
  | h B ih =>
      intro hAB
      by_cases hEq : A = B
      · subst B
        exact ⟨0, UnitChain.refl A⟩
      · rcases exists_unit_predecessor_between hAB hEq with
          ⟨C, hAC, hCB, hCover⟩
        have hAreaLt : area C < area B := by
          have hSucc := hCover.area_succ
          omega
        rcases ih C hAreaLt hAC with ⟨n, hChain⟩
        have hLast : UnitChain C B 1 := by
          simpa using UnitChain.cons hCover (UnitChain.refl B)
        exact ⟨n + 1, UnitChain.trans hChain hLast⟩

/-- zero shape から任意 shape へ one-cell chain が存在する。 -/
theorem exists_unitChain_from_zero
    {p : ℕ}
    (A : FerrersShape p) :
    ∃ n : ℕ, UnitChain (zero p) A n := by
  apply exists_unitChain_of_le
  intro i
  simp [zero]

end FerrersShape

end RecordFerrers
end Collatz2
