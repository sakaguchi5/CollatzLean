import CollatzLean.CollatzSecondLayer3.SpecialC3OverlapCommonSegment
import CollatzLean.CollatzFirstLayer.NegativeShadowAlignment

/-!
# Special C3 shadow magnitude alignmentからprefix一致へ

root center alignmentではなく、negative shadow dynamicsを直接支配する
shadow magnitudeの2進alignmentを用いる。
初回exact exponent 1 re-anchoring後のmagnitudeが深く一致すれば、
累積shadow 2進depthがそのalignment depth未満の範囲で、
二seedの自動shadow exponent prefixはexactに一致する。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

namespace FutureMinimumSpecialC3TowerData

/--
二seedの最初のre-anchoring後shadow magnitudeが方向付きで深さ`m`まで一致する。
-/
noncomputable def ShadowMagnitudesOrderedAlignedToDepth
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j k m : ℕ) : Prop :=
  OrderedMagnitudeAlignedToDepth
    (R.shadowMagnitudeAt j 0)
    (R.shadowMagnitudeAt k 0)
    m

/-- magnitude alignmentは自身について任意深さで成立。 -/
theorem shadowMagnitudesOrderedAlignedToDepth_refl
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j m : ℕ) :
    R.ShadowMagnitudesOrderedAlignedToDepth j j m :=
  orderedMagnitudeAlignedToDepth_refl _ _

/-- 深いmagnitude alignmentは浅いものを含む。 -/
theorem shadowMagnitudesOrderedAlignedToDepth_mono
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k m n : ℕ}
    (hmn : m ≤ n)
    (h : R.ShadowMagnitudesOrderedAlignedToDepth j k n) :
    R.ShadowMagnitudesOrderedAlignedToDepth j k m :=
  orderedMagnitudeAlignedToDepth_mono hmn h

/-- j番目shadow towerの最初のn自動stepが消費する総2進depth。 -/
noncomputable def shadowExtensionTwoSteps
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    (j n : ℕ) : ℕ :=
  (R.shadowTower j).extensionTwoSteps n

/--
初期shadow magnitudeが深さ`M`までalignedなら、j側の累積depthが`M`未満の間、
二seedの自動shadow extension wordは一致する。
-/
theorem shadowExtensionWord_eq_of_magnitude_alignment
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k M n : ℕ}
    (hAlign : R.ShadowMagnitudesOrderedAlignedToDepth j k M)
    (hDepth : R.shadowExtensionTwoSteps j n < M) :
    R.shadowExtensionWord j n = R.shadowExtensionWord k n := by
  exact
    (R.shadowTower j).extensionWord_eq_of_ordered_alignment
      (R.shadowTower k) M n hAlign hDepth

/--
同じ仮定の下で、既存のpointwise prefix一致predicateも得られる。
-/
theorem shadowPrefixesAgreeToDepth_of_magnitude_alignment
    {O : OddOrbit}
    (R : FutureMinimumSpecialC3TowerData O)
    {j k M n : ℕ}
    (hAlign : R.ShadowMagnitudesOrderedAlignedToDepth j k M)
    (hDepth : R.shadowExtensionTwoSteps j n < M) :
    R.ShadowPrefixesAgreeToDepth j k n := by
  intro t ht
  have hle : t + 1 ≤ n := by omega
  have hMono := (R.shadowTower j).extensionTwoSteps_mono hle
  have hDepthT :
      R.shadowExtensionTwoSteps j (t + 1) < M := by
    unfold shadowExtensionTwoSteps at hDepth ⊢
    exact lt_of_le_of_lt hMono hDepth
  exact
    (R.shadowTower j).exponent_eq_of_ordered_alignment
      (R.shadowTower k) M t hAlign hDepthT

end FutureMinimumSpecialC3TowerData
end CollatzSecondLayer3
