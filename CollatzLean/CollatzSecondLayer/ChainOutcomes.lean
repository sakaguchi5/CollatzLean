import CollatzLean.CollatzSecondLayer.OrderedTerminalChain
import CollatzLean.CollatzSecondLayer.InfiniteBranches

/-!
# ordered terminal chainの有限分岐と無限tail分岐

各chain項からprepared carryを自動構成し、alternativeが任意に遠く現れるか、
ある位置以後の全項がSpecial C3になるかへ分岐する。
任意部分列を先に取らないため、隣接関係は失われない。
-/

namespace CollatzSecondLayer

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- chainの第`n`項に付随する解析packet。 -/
structure ChainAnalysisPacket
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) where
  ordered : OrderedDifferenceData (C.pair n)

namespace ChainAnalysisPacket

/-- chain packetのterminal pair。 -/
def criticalPair
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (_P : ChainAnalysisPacket C n) : TerminalPairData :=
  C.pair n

/-- 下側endpointの実軌道位置。 -/
def lowerOrbit
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (_P : ChainAnalysisPacket C n) :
    TerminalLowerOrbitEmbedding O (C.pair n) where
  index := C.endpointPosition n
  value_eq := C.lowerEndpointValue n

/-- ordered差分からprepared carryを構成する。 -/
noncomputable def prepared
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (P : ChainAnalysisPacket C n) :
    PreparedCarryData O P.criticalPair :=
  PreparedCarryData.ofOrbit P.ordered P.lowerOrbit

/-- prepared first-carry比較。 -/
noncomputable def carry
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (P : ChainAnalysisPacket C n) : CarryComparison :=
  P.prepared.toCarryComparison

/-- carryのterminal由来。 -/
noncomputable def carryOrigin
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (P : ChainAnalysisPacket C n) :
    CarryOrigin O P.criticalPair P.carry :=
  ⟨P.prepared, rfl⟩

/-- suffixのcanonical replay座標。 -/
def replayCoordinate
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (P : ChainAnalysisPacket C n) :
    CanonicalReplayCoordinate
      P.criticalPair.R P.criticalPair.YA P.criticalPair.YAR :=
  canonicalReplayCoordinate_of_runs
    P.criticalPair.runR P.criticalPair.R_nonempty

/-- suffix開始値のreplay quotient。 -/
def replayQuotient
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (P : ChainAnalysisPacket C n) : ℕ :=
  P.replayCoordinate.quotient

end ChainAnalysisPacket

/-- chainから標準packetを自動構成する。 -/
noncomputable def chainAnalysisPacket
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (n : ℕ) : ChainAnalysisPacket C n :=
  ⟨C.ordered n⟩

/-- chain上の有限alternative exit。 -/
inductive ChainAlternativeExitAt
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (P : ChainAnalysisPacket C n) : Type
  | captureSuccess (h : CapturedCarry P.carry)
  | lowerNaturalReplay
      (h : LowerNaturalRunReplayData
        P.criticalPair.R P.criticalPair.YA P.criticalPair.YAR)
  | positivePredecessorShadow
      (h : 0 < predecessorShadow P.criticalPair.R)

/-- 隣接chain上に残る修正後Special C3項。 -/
structure ChainSpecialC3At
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (P : ChainAnalysisPacket C n) : Type where
  deferredCarry : DeferredCarry P.carry
  canonicalBoundary : P.replayQuotient = 0
  negativePredecessorShadow :
    predecessorShadow P.criticalPair.R < 0

/-- 各chain項はalternativeかSpecial C3へ落ちる。 -/
theorem chainAnalysisOutcome_nonempty
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    {C : InfiniteOrderedTerminalChain S}
    {n : ℕ}
    (P : ChainAnalysisPacket C n) :
    Nonempty (ChainAlternativeExitAt P ⊕ ChainSpecialC3At P) := by
  rcases carryComparison_split P.carry with hcap | hdefer
  · exact ⟨Sum.inl (ChainAlternativeExitAt.captureSuccess hcap)⟩
  · by_cases hq : P.replayQuotient = 0
    · rcases lt_trichotomy
          (predecessorShadow P.criticalPair.R) 0 with
        hneg | hzero | hpos
      · exact ⟨Sum.inr ⟨hdefer, hq, hneg⟩⟩
      · exact False.elim
          ((predecessorShadow_zero_impossible P.criticalPair.R) hzero)
      · exact ⟨Sum.inl
          (ChainAlternativeExitAt.positivePredecessorShadow hpos)⟩
    · have hqpos : 0 < P.replayQuotient :=
        Nat.pos_of_ne_zero hq
      exact ⟨Sum.inl
        (ChainAlternativeExitAt.lowerNaturalReplay
          (P.replayCoordinate.lowerNaturalRunReplay
            P.criticalPair.runR hqpos))⟩

/-- alternative exitが任意に遠い位置で現れること。 -/
def HasPersistentChainAlternative
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ,
    N ≤ n ∧
    Nonempty
      (ChainAlternativeExitAt (chainAnalysisPacket C n))

/-- ある位置以後の全chain項がSpecial C3であること。 -/
structure EventuallyChainSpecialData
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S) where
  start : ℕ
  special : ∀ n : ℕ, start ≤ n →
    ChainSpecialC3At (chainAnalysisPacket C n)

/--
persistent alternativeが成立しないなら、
ある位置以後ではalternative exitが存在しない。
-/
theorem eventually_noAlternative_of_not_persistent
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (hAlt : ¬ HasPersistentChainAlternative C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ¬ Nonempty
        (ChainAlternativeExitAt (chainAnalysisPacket C n)) := by
  classical
  unfold HasPersistentChainAlternative at hAlt
  push Not at hAlt
  rcases hAlt with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn hNonempty
  rcases hNonempty with ⟨hExit⟩
  exact (hN n hn).false hExit

/--
あるcutoff以後でalternative exitが存在しなければ、
そのcutoff以後の全項はSpecial C3側のoutcomeになる。
-/
theorem eventuallySpecial_of_noAlternative_after
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n →
      ¬ Nonempty
        (ChainAlternativeExitAt (chainAnalysisPacket C n))) :
    Nonempty (EventuallyChainSpecialData C) := by
  classical
  refine ⟨{
    start := N
    special := ?_
  }⟩
  intro n hn
  let houtcome :=
    Classical.choice
      (chainAnalysisOutcome_nonempty
        (chainAnalysisPacket C n))
  rcases houtcome with hExit | hSpecial
  · exact False.elim (hN n hn ⟨hExit⟩)
  · exact hSpecial


/--
persistent alternativeが成立しないなら、
最終的にchainの全項がSpecial C3になる。
-/
theorem eventuallySpecial_of_not_persistent
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S)
    (hAlt : ¬ HasPersistentChainAlternative C) :
    Nonempty (EventuallyChainSpecialData C) := by
  obtain ⟨N, hN⟩ :=
    eventually_noAlternative_of_not_persistent C hAlt
  exact eventuallySpecial_of_noAlternative_after C N hN


/--
alternativeが任意に遠く残るか、
最終的に全項がSpecial C3になる。
-/
theorem persistentAlternative_or_eventuallySpecial
    {O : OddOrbit}
    {S : CoherentC3CylinderSequence O}
    (C : InfiniteOrderedTerminalChain S) :
    HasPersistentChainAlternative C ∨
      Nonempty (EventuallyChainSpecialData C) := by
  classical
  by_cases hAlt : HasPersistentChainAlternative C
  · exact Or.inl hAlt
  · exact Or.inr
      (eventuallySpecial_of_not_persistent C hAlt)

end CollatzSecondLayer
