import CollatzLean.CollatzSecondLayer3.UnifiedSpecialC3Obstruction

/-!
# 生成履歴を忘れた最終obstruction

first-crossingやfirst-criticalのsourceを保持せず、最終的な局所数学情報と
長さ発散だけを保存する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- source-independent Special C3列の成長profile。 -/
inductive GenericSpecialC3GrowthProfile
    (O : OddOrbit) (start length : ℕ → ℕ) : Type
  | polynomial
      (K A : ℕ)
      (bound : ∀ j : ℕ,
        O.value (start j + length j) ≤ K * (length j + 1) ^ A)
  | discounted
      (K A : ℕ)
      (bound : ∀ j : ℕ,
        2 ^ length j * O.value (start j + length j) ≤
          (K * (length j + 1) ^ A) * 3 ^ length j)
  | superPolynomial
      (bound : ∀ K A : ℕ,
        ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
          K * (length j + 1) ^ A < O.value (start j + length j))

/-- 生成経路を持たないSpecial C3 obstruction tower。 -/
structure GenericSpecialC3TowerData (O : OddOrbit) where
  start : ℕ → ℕ
  length : ℕ → ℕ
  special : ∀ j : ℕ, SpecialC3At O (start j) (length j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < length j
  growth : GenericSpecialC3GrowthProfile O start length

/-- source-independentな一つのdeep lower-replay terminal。 -/
structure GenericDeepLowerReplayAt
    (O : OddOrbit) (start length : ℕ) where
  lowerReplay :
    LowerNaturalRunReplayData
      (O.segmentWord start length)
      (O.value start)
      (O.value (start + length))
  modulus_deep :
    2 ^ (length + 1) ≤ residueModulus (O.segmentWord start length)

/-- 生成経路を持たないdeep lower-replay tower。 -/
structure GenericDeepLowerReplayTowerData (O : OddOrbit) where
  start : ℕ → ℕ
  length : ℕ → ℕ
  deep : ∀ j : ℕ, GenericDeepLowerReplayAt O (start j) (length j)
  lengths_tend_to_infinity :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j → M < length j

namespace PolynomialSpecialC3TowerData

noncomputable def toGeneric
    {O : OddOrbit} (R : PolynomialSpecialC3TowerData O) :
    GenericSpecialC3TowerData O where
  start := fun j => R.crossing.minima.index (R.select j) + R.offset j
  length := fun j => R.crossing.crossingLength (R.select j)
  special := R.special
  lengths_tend_to_infinity := R.lengths_tend_to_infinity
  growth := .polynomial R.K R.A (by
    intro j
    simpa using R.endpointBound j)

end PolynomialSpecialC3TowerData

namespace DiscountedSpecialC3TowerData

noncomputable def toGeneric
    {O : OddOrbit} (R : DiscountedSpecialC3TowerData O) :
    GenericSpecialC3TowerData O where
  start := fun j => R.crossing.minima.index (R.select j) + R.offset j
  length := fun j => R.crossing.crossingLength (R.select j)
  special := R.special
  lengths_tend_to_infinity := R.lengths_tend_to_infinity
  growth := .discounted R.K R.A (by
    intro j
    simpa using R.scaledEndpointBound j)

end DiscountedSpecialC3TowerData

namespace CriticalTerminalSpecialC3TowerData

noncomputable def toGeneric
    {O : OddOrbit} (R : CriticalTerminalSpecialC3TowerData O) :
    GenericSpecialC3TowerData O where
  start := fun j => R.crossing.minima.index (R.select j) + R.offset j
  length := fun j => R.crossing.crossingLength (R.select j)
  special := R.special
  lengths_tend_to_infinity := R.lengths_tend_to_infinity
  growth := .superPolynomial (by
    intro K A
    simpa using R.terminalSuperPolynomial K A)

end CriticalTerminalSpecialC3TowerData

namespace UnifiedSpecialC3ObstructionTowerData

noncomputable def toGeneric
    {O : OddOrbit} (R : UnifiedSpecialC3ObstructionTowerData O) :
    GenericSpecialC3TowerData O := by
  cases R with
  | polynomial P => exact P.toGeneric
  | discounted D => exact D.toGeneric
  | criticalTerminal C => exact C.toGeneric

end UnifiedSpecialC3ObstructionTowerData

namespace DeepLowerReplayTerminalTowerData

noncomputable def toGeneric
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (T : DeepLowerReplayTerminalTowerData hGap O) :
    GenericDeepLowerReplayTowerData O where
  start := fun j => T.source.terminalStart (T.select j)
  length := fun j => T.source.windowLength (T.select j)

  deep := fun j => by
    refine { lowerReplay := ?_, modulus_deep := ?_ }
    · simpa [FirstCriticalTransitionTowerData.terminalWord] using
        (T.deep j).lowerReplay
    · simpa [FirstCriticalTransitionTowerData.terminalWord] using
        (T.deep j).modulus_deep

  lengths_tend_to_infinity := by
    have hselectStrict :
        StrictMono (fun j => T.source.select (T.select j)) :=
      T.source.select_strict.comp T.select_strict
    simpa [FirstCriticalTransitionTowerData.windowLength] using
      T.source.firstDeferred.selected_lengths_tend_to_infinity
        (fun j => T.source.select (T.select j))
        hselectStrict

end DeepLowerReplayTerminalTowerData

/-- 非有界軌道上のgeneric Special C3 obstruction。 -/
def HasGenericSpecialC3Tower : Prop :=
  ∃ O : OddOrbit, O.Unbounded ∧ Nonempty (GenericSpecialC3TowerData O)

/-- 非有界軌道上のgeneric deep lower-replay obstruction。 -/
def HasGenericDeepLowerReplayTower : Prop :=
  ∃ O : OddOrbit, O.Unbounded ∧
    Nonempty (GenericDeepLowerReplayTowerData O)

end CollatzSecondLayer3
