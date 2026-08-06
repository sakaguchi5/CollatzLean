import CollatzLean.CollatzSecondLayer3.PositiveReduction

/-!
# 標準構成由来を保持するnormalization obstruction

既存の`NormalizationGeneratedObstructionTowerData`は、無条件三分岐の正の
raw対象として残す。一方、後段のrefinementではprepared familyが実際に
`polynomialPreparedFullWindowFamily hGap crossing`から構成されたという由来が
必要になる。

このファイルでは、その由来を型に保持した強化版第三対象を追加し、既存raw型への
忘却写像と、強化版を使う無条件三分岐を証明する。
-/

namespace CollatzSecondLayer2

/--
標準polynomial preparationから実際に構成されたnormalization obstruction tower。

`prepared`を任意のfamilyとして保存せず、標準構成を型の中で固定することで、
first-crossing・同期境界・critical shellの由来を後段で失わない。
-/
structure StandardNormalizationGeneratedObstructionTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) where
  crossing : MovingFirstCrossingData O
  source : PreparedCaptureNormalizationTowerData
    (polynomialPreparedFullWindowFamily hGap crossing)

namespace StandardNormalizationGeneratedObstructionTowerData

/-- towerが使用する標準prepared family。 -/
noncomputable def prepared
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    PolynomialPreparedFullWindowFamily D.crossing :=
  polynomialPreparedFullWindowFamily hGap D.crossing

/-- 第`j`項のactual prepared開始位置。 -/
noncomputable def start
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ) : ℕ :=
  (polynomialPreparedFullWindowFamily hGap D.crossing).start
    (D.source.select j)

/-- 第`j`項のwindow長。 -/
def windowLength
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ) : ℕ :=
  D.crossing.crossingLength (D.source.select j)

/-- 強化版towerを既存のraw normalization obstructionへ忘却する。 -/
noncomputable def forget
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    NormalizationGeneratedObstructionTowerData O where
  crossing := D.crossing
  prepared := polynomialPreparedFullWindowFamily hGap D.crossing
  source := D.source

/-- 各項のwindow長は無限大へ進む。 -/
theorem lengths_tend_to_infinity
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < D.windowLength j := by
  intro M
  simpa [windowLength] using D.source.lengths_tend_to_infinity M

/-- 各選択項はactual captureを持つ。 -/
def captured
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ) :
    O.CapturedWindowAt (D.start j) (D.windowLength j) := by
  simpa [start, windowLength] using D.source.captured j

end StandardNormalizationGeneratedObstructionTowerData

/-- persistent captureから標準構成由来を保持した第三対象を構成する。 -/
noncomputable def standardNormalizationObstructionOfPersistent
    (hGap : TwoThreeGapPolynomialBound)
    {O : OddOrbit} {F : MovingFirstCrossingData O}
    (hPersistent :
      (polynomialPreparedFullWindowFamily hGap F).HasPersistentCapture) :
    StandardNormalizationGeneratedObstructionTowerData hGap O where
  crossing := F
  source :=
    (polynomialPreparedFullWindowFamily hGap F).normalizationTower
      hPersistent

/-- 指定軌道上の標準構成由来normalization obstruction。 -/
def HasStandardNormalizationGeneratedObstructionTowerOn
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) : Prop :=
  Nonempty (StandardNormalizationGeneratedObstructionTowerData hGap O)

/-- 非有界軌道上の標準構成由来normalization obstruction。 -/
def HasStandardNormalizationGeneratedObstructionTower
    (hGap : TwoThreeGapPolynomialBound) : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧
      HasStandardNormalizationGeneratedObstructionTowerOn hGap O

/-- 標準prepared familyの、由来を失わない無条件二分岐。 -/
theorem standardPreparedFullWindow_positive_dichotomy
    (hGap : TwoThreeGapPolynomialBound)
    {O : OddOrbit} (F : MovingFirstCrossingData O) :
    Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty
        (StandardNormalizationGeneratedObstructionTowerData hGap O) := by
  let P : PolynomialPreparedFullWindowFamily F :=
    polynomialPreparedFullWindowFamily hGap F
  rcases P.persistentCapture_or_polynomialSpecialC3 with
    hPersistent | hSpecial
  · exact Or.inr
      ⟨standardNormalizationObstructionOfPersistent hGap hPersistent⟩
  · exact Or.inl hSpecial

/--
一つの非有界odd-only軌道を、由来を保持した強化版第三対象を含む三枝へ
無条件に還元する。
-/
theorem unboundedOrbit_standard_positive_trichotomy_on
    (hGap : TwoThreeGapPolynomialBound)
    (O : OddOrbit) (hU : O.Unbounded) :
    Nonempty (AnchoredOneSidedMeanderData O) ∨
      Nonempty (PolynomialSpecialC3TowerData O) ∨
      Nonempty
        (StandardNormalizationGeneratedObstructionTowerData hGap O) := by
  classical
  let S : O.FutureMinimumSequence := O.futureMinimumSequence hU
  by_cases hM : ∃ j : ℕ, MeanderAt O (S.index j)
  · rcases hM with ⟨j, hj⟩
    exact Or.inl
      ⟨{
        unbounded := hU
        anchor := S.index j
        futureMinimum := S.futureMinimum j
        meander := hj
      }⟩
  · let F : MovingFirstCrossingData O :=
      movingFirstCrossingData_of_no_meander O hU S hM
    rcases standardPreparedFullWindow_positive_dichotomy hGap F with
      hSpecial | hNormalization
    · exact Or.inr (Or.inl hSpecial)
    · exact Or.inr (Or.inr hNormalization)

/-- 強化版無条件三分岐の存在命題。 -/
theorem unbounded_odd_orbit_standard_positive_trichotomy
    (hGap : TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasAnchoredOneSidedMeander ∨
      HasPolynomialSpecialC3Tower ∨
      HasStandardNormalizationGeneratedObstructionTower hGap := by
  rintro ⟨O, hU⟩
  rcases
      unboundedOrbit_standard_positive_trichotomy_on hGap O hU with
    hM | hSpecial | hNormalization
  · exact Or.inl ⟨O, hM⟩
  · exact Or.inr (Or.inl ⟨O, hU, hSpecial⟩)
  · exact Or.inr (Or.inr ⟨O, hU, hNormalization⟩)

/-- 強化版第三対象は既存raw第三対象へ忘却できる。 -/
theorem standardNormalization_implies_raw
    (hGap : TwoThreeGapPolynomialBound) :
    HasStandardNormalizationGeneratedObstructionTower hGap →
      HasNormalizationGeneratedObstructionTower := by
  rintro ⟨O, hU, ⟨D⟩⟩
  exact ⟨O, hU, ⟨D.forget⟩⟩

end CollatzSecondLayer2
