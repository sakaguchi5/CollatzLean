import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSharedCostTwoBand
import CollatzLean.Collatz2.CSTMicro.MultiCorner.TerminalLastTwoExposedNormalForm
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBExposedPredecessorRealization
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.MinimalBadCellCostObstruction

/-!
# restarted branch 用 actual Shared-Cost pair の branch-independent assembly

既存 `ActualAttachedSharedCostPairAssembly` のうち、attached 幾何に依存しない部分を
`LastTwoExposedNormalForm` まで弱めて取り出す。

previous / terminal の二つが exposed であることだけから actual predecessor step 二本を得て、
同じ upper bad word に属する二つの cell を `AttachedSharedCostPair` の純算術へ渡す。

構造名 `AttachedSharedCostPair` は既存 API 名を再利用しているだけで、
このファイルの assembly 自体は attached placement を仮定しない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
last-two exposed normal form だけから actual first-passage predecessor step 二本を得る。
attached / restarted のどちらも仮定しない。
-/
theorem exists_lastTwoNormalFormActualPredecessorSteps
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)) :
    ∃ lower0 lower1 : ParityWord,
      ∃ S0 : FerrersStep lower0 M.word,
        ∃ S1 : FerrersStep lower1 M.word,
          IsFirstPassageWord lower0 ∧
          IsFirstPassageWord lower1 ∧
          S0.edge.rankCut = N.previous ∧
          S1.edge.rankCut = N.terminal := by
  let P := M.toPureBProfileObstruction hL
  have E0 : P.IsExposedPredecessorIndex N.previous :=
    (P.mem_exposedPredecessorSet_iff).1 N.previous_mem
  have E1 : P.IsExposedPredecessorIndex N.terminal :=
    (P.mem_exposedPredecessorSet_iff).1 N.terminal_mem
  obtain ⟨lower0, S0, hFP0, hRank0⟩ :=
    M.exists_actualPredecessor_of_exposedIndex hL E0
  obtain ⟨lower1, S1, hFP1, hRank1⟩ :=
    M.exists_actualPredecessor_of_exposedIndex hL E1
  exact ⟨lower0, lower1, S0, S1, hFP0, hFP1, hRank0, hRank1⟩

/--
branch-independent な last-two actual cells を Shared-Cost pair に束ねる入力。

cell exact identity 自体は field にせず、既存の generic Farey identity から構成時に証明する。
残す field は same-upper-word bookkeeping と positivity だけである。
-/
structure LastTwoSharedCostActualPairAssemblyInput
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)) where
  lower0 : ParityWord
  lower1 : ParityWord

  step0 : FerrersStep lower0 M.word
  step1 : FerrersStep lower1 M.word

  lower0_firstPassage : IsFirstPassageWord lower0
  lower1_firstPassage : IsFirstPassageWord lower1

  rank0_eq : step0.edge.rankCut = N.previous
  rank1_eq : step1.edge.rankCut = N.terminal

  shared_modulus :
    (step1.edge.modulus : ℤ) = (step0.edge.modulus : ℤ)

  shared_gap :
    step1.edge.toFareyCellPacket.G = step0.edge.toFareyCellPacket.G

  affine_decomposition :
    (affineConst M.word : ℤ) =
      step0.edge.toFareyCellPacket.G *
          (leastRepresentative M.word : ℤ) +
        (step0.edge.modulus : ℤ) * (M.actual.q : ℤ)

  modulus_pos : 0 < (step0.edge.modulus : ℤ)
  gap_pos : 0 < step0.edge.toFareyCellPacket.G

  extra_pos :
    0 <
      (affineConst M.word : ℤ) +
        (step0.edge.deltaB : ℤ) +
        (step1.edge.deltaB : ℤ)

namespace LastTwoSharedCostActualPairAssemblyInput

/-- branch-independent actual two-cell data から Shared-Cost pair を構成する。 -/
noncomputable def toPair
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N) :
    AttachedSharedCostPair := by
  refine
    { modulus := (D.step0.edge.modulus : ℤ)
      gap := D.step0.edge.toFareyCellPacket.G
      affineB := (affineConst M.word : ℤ)
      normalizedQ := (M.actual.q : ℤ)
      representative := (leastRepresentative M.word : ℤ)
      cost0 := D.step0.edge.fareyCellCost
      cost1 := D.step1.edge.fareyCellCost
      delta0 := (D.step0.edge.deltaR : ℤ)
      delta1 := (D.step1.edge.deltaR : ℤ)
      weight0 := (D.step0.edge.deltaB : ℤ)
      weight1 := (D.step1.edge.deltaB : ℤ)
      modulus_pos := D.modulus_pos
      gap_pos := D.gap_pos
      affine_decomposition := D.affine_decomposition
      cell0_exact := ?_
      cell1_exact := ?_
      extra_pos := D.extra_pos }
  · have h0 :=
      D.step0.edge.twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB
    simpa [AdjacentFerrersSwap.modulus] using h0
  · have h1 :=
      D.step1.edge.twoPow_length_mul_fareyCellCost_eq_gap_mul_deltaR_add_deltaB
    have h1' :
        (D.step1.edge.modulus : ℤ) * D.step1.edge.fareyCellCost =
          D.step1.edge.toFareyCellPacket.G * (D.step1.edge.deltaR : ℤ) +
            (D.step1.edge.deltaB : ℤ) := by
      simpa [AdjacentFerrersSwap.modulus] using h1
    rw [D.shared_modulus, D.shared_gap] at h1'
    exact h1'

/-- 構成した pair の actual 座標。 -/
theorem toPair_actual_coordinates
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N) :
    let A := D.toPair
    A.affineB = (affineConst M.word : ℤ) ∧
    A.normalizedQ = (M.actual.q : ℤ) ∧
    A.representative = (leastRepresentative M.word : ℤ) ∧
    A.cost0 = D.step0.edge.fareyCellCost ∧
    A.cost1 = D.step1.edge.fareyCellCost ∧
    A.delta0 = (D.step0.edge.deltaR : ℤ) ∧
    A.delta1 = (D.step1.edge.deltaR : ℤ) ∧
    A.weight0 = (D.step0.edge.deltaB : ℤ) ∧
    A.weight1 = (D.step1.edge.deltaB : ℤ) := by
  simp [toPair]

/--
構成した pair の二つの cost は、同じ gap に対する二つの Farey residue の complement。
-/
theorem toPair_costs_eq_gap_sub_residues
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N) :
    let A := D.toPair
    A.cost0 = A.gap - D.step0.edge.toFareyCellPacket.residue ∧
      A.cost1 = A.gap - D.step1.edge.toFareyCellPacket.residue := by
  simp [
    toPair,
    AdjacentFerrersSwap.fareyCellCost,
    D.shared_gap
  ]

/--
representative threshold が non-strict に成立すれば、
actual last-two Farey residues は strict two-band bound を満たす。
-/
theorem residueSum_lt_gap_add_normalizedQ_of_threshold_le
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (hThreshold :
      D.toPair.representativeThreshold ≤ D.toPair.deltaSum) :
    (D.step0.edge.toFareyCellPacket.residue +
        D.step1.edge.toFareyCellPacket.residue) <
      D.toPair.gap + D.toPair.normalizedQ := by
  have hCost := D.toPair_costs_eq_gap_sub_residues
  exact
    D.toPair.defectSum_lt_gap_add_normalizedQ_of_threshold_le
      D.step0.edge.toFareyCellPacket.residue
      D.step1.edge.toFareyCellPacket.residue
      hCost.1 hCost.2 hThreshold

end LastTwoSharedCostActualPairAssemblyInput

/--
branch-independent actual Shared-Cost pair assembly の残余 obligation。

二本の predecessor の存在は既に閉じているため、ここに残るのは
shared modulus / gap、bad affine decomposition、positivity の bookkeeping である。
-/
def ActualLastTwoSharedCostPairAssemblyObligation
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)) : Prop :=
  Nonempty (LastTwoSharedCostActualPairAssemblyInput M hL N)

/-- assembly obligation が閉じれば branch-independent actual pair が存在する。 -/
theorem exists_actualLastTwoSharedCostPair
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL))
    (H : ActualLastTwoSharedCostPairAssemblyObligation M hL N) :
    ∃ _A : AttachedSharedCostPair, True := by
  rcases H with ⟨D⟩
  exact ⟨D.toPair, trivial⟩

end MultiCorner
end CSTMicro
end Collatz2
