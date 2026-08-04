import CollatzLean.CollatzSecondLayer.SynchronizationTransport
import CollatzLean.CollatzSecondLayer.RotationDriftStaircase
import CollatzLean.CollatzSecondLayer.Reduction

/-!
# 隣接chainによる非有界軌道の新還元

旧第三bridgeの独立terminal packet列を通らず、Cylinder Upgradeが実際に作る
整合cylinder列から一本の隣接ordered chainを直接構成する。

残る分岐は

* one-sided meander
* chain alternativeが任意に遠く残る
* prepared depthが非有界なchain Special C3
* bounded-depth long-sync rotation chain

である。
-/

namespace CollatzSecondLayer

/-- chain alternativeが存在すること。 -/
def HasPersistentOrderedChainAlternative : Prop :=
  ∃ O : OddOrbit,
  ∃ S : CoherentC3CylinderSequence O,
  ∃ C : InfiniteOrderedTerminalChain S,
    HasPersistentChainAlternative C

/-- 隣接chain上でprepared depthが任意に大きくなるSpecial C3 tail。 -/
structure ArbitrarilyDeepChainSpecialData
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S) where
  specialTail : EventuallyChainSpecialData C
  depths_unbounded :
    ∀ M : ℕ, ∃ n : ℕ,
      specialTail.start ≤ n ∧
      M < (chainAnalysisPacket C n).carry.d

/-- prepared depth非有界な隣接Special C3 chainが存在すること。 -/
def HasArbitrarilyDeepOrderedChainSpecial : Prop :=
  ∃ O : OddOrbit,
  ∃ S : CoherentC3CylinderSequence O,
  ∃ C : InfiniteOrderedTerminalChain S,
    Nonempty (ArbitrarilyDeepChainSpecialData C)

/-- bounded-depth long-sync rotation chainが存在すること。 -/
def HasBoundedDepthLongSyncRotation : Prop :=
  ∃ O : OddOrbit,
  ∃ S : CoherentC3CylinderSequence O,
  ∃ C : InfiniteOrderedTerminalChain S,
    Nonempty (BoundedDepthLongSyncRotationData C)

/--
eventually Special chainは、depth非有界または一様有界のどちらかへ分岐する。
-/
theorem chainSpecial_depth_unbounded_or_bounded
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    (E : EventuallyChainSpecialData C) :
    Nonempty (ArbitrarilyDeepChainSpecialData C) ∨
      ∃ B : ℕ, ∀ n : ℕ,
        E.start ≤ n →
        (chainAnalysisPacket C n).carry.d ≤ B := by
  classical
  by_cases hbounded :
      ∃ B : ℕ, ∀ n : ℕ,
        E.start ≤ n →
        (chainAnalysisPacket C n).carry.d ≤ B
  · exact Or.inr hbounded
  · left
    have hunbounded :
        ∀ M : ℕ, ∃ n : ℕ,
          E.start ≤ n ∧
          M < (chainAnalysisPacket C n).carry.d := by
      push Not at hbounded
      exact hbounded
    exact ⟨⟨E, hunbounded⟩⟩

/--
Baker型gap入力と初等的指数優越を用いた、隣接chain版の四分岐還元。
旧`InfiniteTerminalExtractionObstruction`は現れない。
-/
theorem unbounded_orbit_chain_reduction
    (hBaker : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower) :
    HasUnboundedOddOrbit →
      HasOneSidedMeander ∨
      HasPersistentOrderedChainAlternative ∨
      HasArbitrarilyDeepOrderedChainSpecial ∨
      HasBoundedDepthLongSyncRotation := by
  rintro ⟨O, hO⟩
  rcases movingCompactnessPrinciple O hO with ⟨D⟩
  rcases firstCrossingSequence_or_meander D with hMeander | hCrossing
  · exact Or.inl ⟨O, hO, hMeander⟩
  · rcases hCrossing with ⟨F⟩
    rcases coherentCylinderUpgrade_of_arithmetic hBaker hPow O F with ⟨S⟩
    let C : InfiniteOrderedTerminalChain S :=
      InfiniteOrderedTerminalChain.ofCoherent S
    rcases persistentAlternative_or_eventuallySpecial C with
      hAlternative | hEventually
    · exact Or.inr (Or.inl ⟨O, S, C, hAlternative⟩)
    · rcases hEventually with ⟨E⟩
      rcases chainSpecial_depth_unbounded_or_bounded E with
        hDeep | hBounded
      · exact Or.inr (Or.inr (Or.inl ⟨O, S, C, hDeep⟩))
      · rcases hBounded with ⟨B, hB⟩
        let L : ChainSynchronizationLaw C :=
          chainSynchronizationLawOfEventuallySpecial E
        let R : BoundedDepthLongSyncRotationData C :=
          boundedDepthLongSyncRotationData_of_law
            hPow L B (by
              intro n hn
              exact hB n hn)
        exact Or.inr (Or.inr (Or.inr ⟨O, S, C, ⟨R⟩⟩))

/--
新四分岐をすべて排除できれば非有界odd-only軌道は存在しない。
-/
theorem no_unbounded_orbit_of_chain_exclusions
    (hBaker : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    (hMeander : ¬ HasOneSidedMeander)
    (hAlternative : ¬ HasPersistentOrderedChainAlternative)
    (hDeep : ¬ HasArbitrarilyDeepOrderedChainSpecial)
    (hRotation : ¬ HasBoundedDepthLongSyncRotation) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_orbit_chain_reduction hBaker hPow hU with
    h | h | h | h
  · exact hMeander h
  · exact hAlternative h
  · exact hDeep h
  · exact hRotation h

/--
record block圧縮原理まで受け取れば、bounded rotation枝をstaircaseへ送れる。
-/
theorem rotationStaircase_of_unbounded_of_no_first_three
    (hBaker : TwoThreeGapPolynomialBound)
    (hPow : PolynomialBelowTwoPower)
    (hRecord : RecordBlockCompressionPrinciple)
    (hMeander : ¬ HasOneSidedMeander)
    (hAlternative : ¬ HasPersistentOrderedChainAlternative)
    (hDeep : ¬ HasArbitrarilyDeepOrderedChainSpecial) :
    HasUnboundedOddOrbit → HasRotationDriftStaircase := by
  intro hU
  rcases unbounded_orbit_chain_reduction hBaker hPow hU with
    h | h | h | hRotation
  · exact False.elim (hMeander h)
  · exact False.elim (hAlternative h)
  · exact False.elim (hDeep h)
  · rcases hRotation with ⟨O, S, C, ⟨R⟩⟩
    exact hRecord O S C R

end CollatzSecondLayer
