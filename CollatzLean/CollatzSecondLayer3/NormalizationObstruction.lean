import CollatzLean.CollatzSecondLayer3.PreparedNormalizationTower

/-!
# persistent captureから得られるactual normalization obstruction

第三対象をfirst-crossing由来の膨張prefixで水増しせず、
persistent captureの各選択項と、そこから実際に構成されたnormalization outcomeを
そのまま正の数学対象として保存する。

この対象は補集合を含まない。また各項について、

* actual captured q-window
* capture直後も継続する正差window
* first deferredを持つ有限normalization、または
* deferredなしのeventual synchronization

を実データとして持つ。
-/

namespace CollatzSecondLayer2

/-- persistent captureから実際に生成されたnormalization tower。 -/
structure NormalizationGeneratedObstructionTowerData (O : OddOrbit) where
  crossing : MovingFirstCrossingData O
  prepared : PolynomialPreparedFullWindowFamily crossing
  source : PreparedCaptureNormalizationTowerData prepared

/-- towerの第`j`項のactual開始位置。 -/
def NormalizationGeneratedObstructionTowerData.start
    {O : OddOrbit}
    (D : NormalizationGeneratedObstructionTowerData O)
    (j : ℕ) : ℕ :=
  D.prepared.start (D.source.select j)

/-- towerの第`j`項のwindow長。 -/
def NormalizationGeneratedObstructionTowerData.windowLength
    {O : OddOrbit}
    (D : NormalizationGeneratedObstructionTowerData O)
    (j : ℕ) : ℕ :=
  D.crossing.crossingLength (D.source.select j)

/-- 各選択項のcapture gapは正。 -/
theorem NormalizationGeneratedObstructionTowerData.captureGap_pos
    {O : OddOrbit}
    (D : NormalizationGeneratedObstructionTowerData O)
    (j : ℕ) :
    0 < O.exponent (D.start j) - (D.source.captured j).depth := by
  exact Nat.sub_pos_of_lt (D.source.captured j).captured

/-- 各選択項ではcapture直後の正差windowがactualに構成される。 -/
noncomputable def NormalizationGeneratedObstructionTowerData.nextDifference
    {O : OddOrbit}
    (D : NormalizationGeneratedObstructionTowerData O)
    (j : ℕ) :
    O.WindowDifferenceData (D.start j + 1) (D.windowLength j) := by
  simpa [NormalizationGeneratedObstructionTowerData.start,
    NormalizationGeneratedObstructionTowerData.windowLength] using
    (D.source.captured j).nextDifferenceData

/-- 指定軌道上にnormalization obstruction towerが存在すること。 -/
def HasNormalizationGeneratedObstructionTowerOn (O : OddOrbit) : Prop :=
  Nonempty (NormalizationGeneratedObstructionTowerData O)

/-- 非有界odd-only軌道上にnormalization obstruction towerが存在すること。 -/
def HasNormalizationGeneratedObstructionTower : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧ HasNormalizationGeneratedObstructionTowerOn O

namespace PolynomialPreparedFullWindowFamily

/-- persistent captureからnormalization obstruction towerを構成する。 -/
noncomputable def toNormalizationGeneratedObstructionTower
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (P : PolynomialPreparedFullWindowFamily F)
    (h : P.HasPersistentCapture) :
    NormalizationGeneratedObstructionTowerData O where
  crossing := F
  prepared := P
  source := P.normalizationTower h

end PolynomialPreparedFullWindowFamily
end CollatzSecondLayer2
