import CollatzLean.CollatzSecondLayer2.NoCriticalDiscountedSpecialC3
import CollatzLean.CollatzSecondLayer2.ShortPositiveShadowExclusion

/-!
# Special C3 obstructionの最終統合

従来の中央枝は

* polynomial Special C3
* discounted Special C3

の二形を保存していた。

first-critical terminalから得られるactual Special C3 towerを、
生成履歴を忘れた純粋な
`CriticalTerminalSpecialC3TowerData`へ移し、第三形として同じ中央枝へ統合する。

このファイルは具体的なfirst-critical towerから共通数学対象への忘却写像だけを担う。
no-critical側の構成定理とterminal側の構成定理を互いにimportさせないため、
import依存は一方向のままである。
-/

namespace CollatzSecondLayer2

/--
first-critical terminalに由来するsuper-polynomial Special C3 tower。

`FirstCriticalTransitionTowerData`そのものは保存せず、moving first-crossing上の
位置表示、actual Special C3、長さ発散、terminal endpointのsuper-polynomial性だけを
純粋な数学対象として保存する。
-/
structure CriticalTerminalSpecialC3TowerData (O : OddOrbit) where
  crossing : MovingFirstCrossingData O
  select : ℕ → ℕ
  select_strict : StrictMono select
  offset : ℕ → ℕ
  special : ∀ j : ℕ,
    SpecialC3At O
      (crossing.minima.index (select j) + offset j)
      (crossing.crossingLength (select j))
  terminalSuperPolynomial : ∀ K A : ℕ,
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      K * (crossing.crossingLength (select j) + 1) ^ A <
        O.value
          (crossing.minima.index (select j) + offset j +
            crossing.crossingLength (select j))
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < crossing.crossingLength (select j)

/--
Special C3 obstructionの最終三形。

* `polynomial`: endpointが固定多項式以下
* `discounted`: `2^q * endpoint`が`poly(q) * 3^q`以下
* `criticalTerminal`: endpointが全固定多項式を最終的に超えるfirst-critical terminal
-/
inductive UnifiedSpecialC3ObstructionTowerData (O : OddOrbit) : Type
  | polynomial (data : PolynomialSpecialC3TowerData O)
  | discounted (data : DiscountedSpecialC3TowerData O)
  | criticalTerminal (data : CriticalTerminalSpecialC3TowerData O)

/-- 指定軌道上の統合済みSpecial C3 obstruction。 -/
def HasUnifiedSpecialC3ObstructionTowerOn (O : OddOrbit) : Prop :=
  Nonempty (UnifiedSpecialC3ObstructionTowerData O)

/-- 非有界軌道上の統合済みSpecial C3 obstruction。 -/
def HasUnifiedSpecialC3ObstructionTower : Prop :=
  ∃ O : OddOrbit,
    O.Unbounded ∧ HasUnifiedSpecialC3ObstructionTowerOn O

namespace PolynomialSpecialC3TowerData

/-- Polynomial Special C3を統合中央枝へ入れる。 -/
def toUnifiedObstruction
    {O : OddOrbit}
    (R : PolynomialSpecialC3TowerData O) :
    UnifiedSpecialC3ObstructionTowerData O :=
  .polynomial R

end PolynomialSpecialC3TowerData

namespace DiscountedSpecialC3TowerData

/-- Discounted Special C3を統合中央枝へ入れる。 -/
def toUnifiedObstruction
    {O : OddOrbit}
    (R : DiscountedSpecialC3TowerData O) :
    UnifiedSpecialC3ObstructionTowerData O :=
  .discounted R

end DiscountedSpecialC3TowerData

namespace CriticalTerminalSpecialC3TowerData

/-- Critical-terminal Special C3を統合中央枝へ入れる。 -/
def toUnifiedObstruction
    {O : OddOrbit}
    (R : CriticalTerminalSpecialC3TowerData O) :
    UnifiedSpecialC3ObstructionTowerData O :=
  .criticalTerminal R

end CriticalTerminalSpecialC3TowerData

namespace SpecialC3ObstructionTowerData

/-- 従来のpolynomial/discounted中央枝を新しい三形中央枝へ忘却する。 -/
def toUnified
    {O : OddOrbit}
    (R : SpecialC3ObstructionTowerData O) :
    UnifiedSpecialC3ObstructionTowerData O := by
  cases R with
  | polynomial P => exact .polynomial P
  | discounted D => exact .discounted D

end SpecialC3ObstructionTowerData

namespace TerminalSpecialC3TransitionTowerData

/-- terminal tower第`j`項が由来するmoving first-crossing添字。 -/
noncomputable def unifiedCrossingSelect
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : TerminalSpecialC3TransitionTowerData hGap O)
    (j : ℕ) : ℕ :=
  T.source.firstDeferred.crossingIndex
    (T.source.select (T.select j))

/-- terminal Special C3の元first-crossing内offset。 -/
noncomputable def unifiedOffset
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : TerminalSpecialC3TransitionTowerData hGap O)
    (j : ℕ) : ℕ :=
  (polynomialPreparedFullWindowFamily
      hGap T.source.source.crossing).offset
        (T.unifiedCrossingSelect j) +
    T.source.firstDeferred.terminalTime
      (T.source.select (T.select j))

/-- terminal towerから得るcrossing選択列は狭義単調。 -/
theorem unifiedCrossingSelect_strict
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : TerminalSpecialC3TransitionTowerData hGap O) :
    StrictMono T.unifiedCrossingSelect := by
  intro a b hab
  change
    T.source.source.source.select
        (T.source.firstDeferred.select
          (T.source.select (T.select a))) <
      T.source.source.source.select
        (T.source.firstDeferred.select
          (T.source.select (T.select b)))
  exact T.source.source.source.select_strict
    (T.source.firstDeferred.select_strict
      (T.source.select_strict
        (T.select_strict hab)))

/-- terminal tower各項をmoving first-crossing表示のactual Special C3へ移す。 -/
noncomputable def unifiedSpecial
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : TerminalSpecialC3TransitionTowerData hGap O)
    (j : ℕ) :
    SpecialC3At O
      (T.source.source.crossing.minima.index
          (T.unifiedCrossingSelect j) +
        T.unifiedOffset j)
      (T.source.source.crossing.crossingLength
        (T.unifiedCrossingSelect j)) := by
  classical
  have hNonempty := T.special j
  exact Classical.choice (by
    simpa [
      FirstCriticalTransitionTowerData.TerminalSpecialC3At,
      unifiedCrossingSelect,
      unifiedOffset,
      FirstCriticalTransitionTowerData.start,
      FirstCriticalTransitionTowerData.windowLength,
      FirstDeferredNormalizationTowerData.start,
      FirstDeferredNormalizationTowerData.windowLength,
      FirstDeferredNormalizationTowerData.crossingIndex,
      StandardNormalizationGeneratedObstructionTowerData.start,
      StandardNormalizationGeneratedObstructionTowerData.windowLength,
      PolynomialPreparedFullWindowFamily.start,
      Nat.add_assoc
    ] using hNonempty)

/-- terminal towerで選び直したwindow長も無限大へ進む。 -/
theorem unifiedLengths_tend_to_infinity
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : TerminalSpecialC3TransitionTowerData hGap O) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M <
        T.source.source.crossing.crossingLength
          (T.unifiedCrossingSelect j) := by
  intro M
  let select : ℕ → ℕ :=
    fun j => T.source.select (T.select j)
  have hselect : StrictMono select := by
    intro a b hab
    exact T.source.select_strict (T.select_strict hab)
  obtain ⟨J, hJ⟩ :=
    T.source.firstDeferred.selected_lengths_tend_to_infinity
      select hselect M
  refine ⟨J, ?_⟩
  intro j hj
  have h := hJ j hj
  simpa [
    select,
    unifiedCrossingSelect,
    FirstDeferredNormalizationTowerData.crossingIndex,
    FirstDeferredNormalizationTowerData.windowLength,
    StandardNormalizationGeneratedObstructionTowerData.windowLength
  ] using h

/-- terminal endpointのsuper-polynomial性をmoving first-crossing表示へ移す。 -/
theorem unifiedTerminalSuperPolynomial
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : TerminalSpecialC3TransitionTowerData hGap O) :
    ∀ K A : ℕ,
      ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
        K *
            (T.source.source.crossing.crossingLength
                (T.unifiedCrossingSelect j) + 1) ^ A <
          O.value
            (T.source.source.crossing.minima.index
                (T.unifiedCrossingSelect j) +
              T.unifiedOffset j +
              T.source.source.crossing.crossingLength
                (T.unifiedCrossingSelect j)) := by
  intro K A
  obtain ⟨J, hJ⟩ := T.source.terminalSuperPolynomial K A
  refine ⟨J, ?_⟩
  intro j hj
  have hindex : j ≤ T.select j :=
    nat_le_strictMono_apply T.select T.select_strict j
  have h := hJ (T.select j) (le_trans hj hindex)
  simpa [
    unifiedCrossingSelect,
    unifiedOffset,
    FirstCriticalTransitionTowerData.windowLength,
    FirstDeferredNormalizationTowerData.crossingIndex,
    FirstDeferredNormalizationTowerData.start,
    FirstDeferredNormalizationTowerData.terminalTime,
    FirstDeferredNormalizationTowerData.terminalEndpoint,
    FirstDeferredNormalizationTowerData.windowLength,
    StandardNormalizationGeneratedObstructionTowerData.start,
    StandardNormalizationGeneratedObstructionTowerData.windowLength,
    PolynomialPreparedFullWindowFamily.start,
    Nat.add_assoc
  ] using h

/-- terminal Special C3 transition towerを純粋なcritical-terminal towerへ忘却する。 -/
noncomputable def toCriticalTerminalSpecialC3Tower
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : TerminalSpecialC3TransitionTowerData hGap O) :
    CriticalTerminalSpecialC3TowerData O where
  crossing := T.source.source.crossing
  select := T.unifiedCrossingSelect
  select_strict := T.unifiedCrossingSelect_strict
  offset := T.unifiedOffset
  special := T.unifiedSpecial
  terminalSuperPolynomial := T.unifiedTerminalSuperPolynomial
  lengths_tend_to_infinity := T.unifiedLengths_tend_to_infinity

/-- terminal Special C3 transition towerを統合中央枝へ吸収する。 -/
noncomputable def toUnifiedObstruction
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : TerminalSpecialC3TransitionTowerData hGap O) :
    UnifiedSpecialC3ObstructionTowerData O :=
  .criticalTerminal T.toCriticalTerminalSpecialC3Tower

end TerminalSpecialC3TransitionTowerData

end CollatzSecondLayer2
