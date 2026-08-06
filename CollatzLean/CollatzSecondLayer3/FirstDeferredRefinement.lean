import CollatzLean.CollatzSecondLayer3.FirstDeferredSubsequenceClassification

/-!
# first-deferred refinement

`FirstDeferredTowerRefinementPrinciple`という外部入力は使用しない。
first-deferred towerのrefinementは、次の四段階の実定理として構成される。

1. polynomial terminal部分towerからPolynomial Special C3 towerを構成する。
2. no-critical finite normalizationのcapture数をcritical shellで抑える。
3. super-polynomial no-critical towerからlong synchronized plateau towerを構成する。
4. 任意のfirst-deferred towerを前三種類の部分towerへ無条件に分類する。

固定多項式の指数優越はLean内定理として閉じているため、外部入力には取らない。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore

/--
first-deferred towerをPolynomial Special C3 / critical capture / long plateauへ
実定理としてrefineする。
-/
theorem firstDeferredTower_refinement
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit)
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (T : FirstDeferredNormalizationTowerData D) :
    Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty (CriticalCaptureTowerData hGap O) ∨
      Nonempty (LongSynchronizedPlateauTowerData hGap O) := by
  rcases firstDeferred_subsequence_classification T with
    hPolynomial | hCritical | hSuper
  · rcases hPolynomial with ⟨P⟩
    exact Or.inl ⟨P.toPolynomialSpecialC3Tower⟩
  · exact Or.inr (Or.inl hCritical)
  · rcases hSuper with ⟨S⟩
    exact Or.inr
      (Or.inr ⟨S.toLongSynchronizedPlateauTower⟩)

end CollatzSecondLayer3
