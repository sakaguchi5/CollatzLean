import CollatzLean.CollatzSecondLayer3.SpecialC3ShadowTower
import CollatzLean.CollatzFirstLayer.CommonWordDifference

import Mathlib.Tactic.Ring

/-!
# Special C3 seed間のalignmentとsource interval基礎分類

最終collision定理へ入る前の比較用APIを用意する。
centerの2進alignment、shadow exponent prefix一致、source intervalの
before/overlap三分岐だけを扱い、collisionや矛盾は主張しない。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData

/-- 二つのseed centerが深さmまで2進一致する。 -/
def CentersAlignedToDepth
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k m : ℕ) : Prop :=
  (2 : ℤ) ^ m ∣ R.center k - R.center j

/-- centerは自身と任意深さでaligned。 -/
theorem centersAlignedToDepth_refl
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j m : ℕ) :
    R.CentersAlignedToDepth j j m := by
  refine ⟨0, ?_⟩
  ring

/-- center alignmentは対称。 -/
theorem centersAlignedToDepth_symm
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k m : ℕ}
    (h : R.CentersAlignedToDepth j k m) :
    R.CentersAlignedToDepth k j m := by
  rcases h with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  calc
    R.center j - R.center k
        = -(R.center k - R.center j) := by ring
    _ = -((2 : ℤ) ^ m * z) := by rw [hz]
    _ = (2 : ℤ) ^ m * (-z) := by ring

/-- 深いalignmentは浅いalignmentを含む。 -/
theorem centersAlignedToDepth_mono
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k m n : ℕ}
    (hmn : m ≤ n)
    (h : R.CentersAlignedToDepth j k n) :
    R.CentersAlignedToDepth j k m := by
  rcases h with ⟨z, hz⟩
  refine ⟨(2 : ℤ) ^ (n - m) * z, ?_⟩
  have hn : n = m + (n - m) := by omega
  rw [hn, pow_add] at hz
  calc
    R.center k - R.center j
        = ((2 : ℤ) ^ m * (2 : ℤ) ^ (n - m)) * z := hz
    _ = (2 : ℤ) ^ m * ((2 : ℤ) ^ (n - m) * z) := by ring

/-- exact center一致は任意深さのalignmentを与える。 -/
theorem centersAlignedToDepth_of_center_eq
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (h : R.center j = R.center k)
    (m : ℕ) :
    R.CentersAlignedToDepth j k m := by
  refine ⟨0, ?_⟩
  rw [← h]
  ring

/-- 二つのseedのshadow exponent prefixが長さnまで一致する。 -/
def ShadowPrefixesAgreeToDepth
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k n : ℕ) : Prop :=
  ∀ t : ℕ, t < n →
    R.shadowExponent j t = R.shadowExponent k t

/-- shadow prefix一致は反射的。 -/
theorem shadowPrefixesAgreeToDepth_refl
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) :
    R.ShadowPrefixesAgreeToDepth j j n := by
  intro t _
  rfl

/-- shadow prefix一致は対称。 -/
theorem shadowPrefixesAgreeToDepth_symm
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k n : ℕ}
    (h : R.ShadowPrefixesAgreeToDepth j k n) :
    R.ShadowPrefixesAgreeToDepth k j n := by
  intro t ht
  exact (h t ht).symm

/-- 長いshadow prefix一致は短いprefix一致を含む。 -/
theorem shadowPrefixesAgreeToDepth_mono
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k m n : ℕ}
    (hmn : m ≤ n)
    (h : R.ShadowPrefixesAgreeToDepth j k n) :
    R.ShadowPrefixesAgreeToDepth j k m := by
  intro t ht
  exact h t (lt_of_lt_of_le ht hmn)

/-- j番目のsource intervalの左端。 -/
def sourceIntervalStart
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j : ℕ) : ℕ :=
  R.start j

/-- j番目のsource intervalの右端。半開区間として扱う。 -/
def sourceIntervalEnd
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j : ℕ) : ℕ :=
  R.start j + R.length j

/-- j番目のsource intervalがk番目より前に終わる。 -/
def SourceIntervalBefore
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : Prop :=
  R.sourceIntervalEnd j ≤ R.sourceIntervalStart k

/-- 二つの半開source intervalが真に重なる。 -/
def SourceIntervalsOverlap
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) : Prop :=
  R.sourceIntervalStart j < R.sourceIntervalEnd k ∧
    R.sourceIntervalStart k < R.sourceIntervalEnd j

/-- interval overlapは対称。 -/
theorem sourceIntervalsOverlap_symm
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k : ℕ}
    (h : R.SourceIntervalsOverlap j k) :
    R.SourceIntervalsOverlap k j :=
  ⟨h.2, h.1⟩

/--
任意の二source intervalは、jが前、kが前、または真のoverlapの三枝に入る。
-/
theorem sourceInterval_before_or_before_or_overlap
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k : ℕ) :
    R.SourceIntervalBefore j k ∨
      R.SourceIntervalBefore k j ∨
      R.SourceIntervalsOverlap j k := by
  by_cases hjk :
      R.sourceIntervalEnd j ≤ R.sourceIntervalStart k
  · exact Or.inl hjk
  · by_cases hkj :
        R.sourceIntervalEnd k ≤ R.sourceIntervalStart j
    · exact Or.inr (Or.inl hkj)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)

end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
