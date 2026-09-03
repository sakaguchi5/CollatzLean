import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedCaseIIEndpointBalance
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedActualSharedCostPairAssembly
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedCaseIIEndpointReduction

/-!
# Case II endpoint `s=c`: actual last-two cells まで降ろした reduction

abstract `D0,D1` を actual previous / terminal の Farey residue に固定する。

このファイルで新たな未証明事実を theorem として置くことはしない。
Shared-Cost の二重 normalized defect 候補を endpoint quantity と同一視する部分だけを
`...BridgeCandidate` という `Prop` として明示し、その bridge が得られた場合に何が
自動的に閉じるかを証明する。

`s=c` の exact endpoint balance により、次の二つの bridge 表現は同値になる。

1. affine mass 形

   M q_* = A_c + 2^(beta(b)-1+width)

2. actual state surplus 形

   M q_* = 2^beta(c) Z_c + 2^(beta(b)-1+width) - 3^c(y-q)

さらに右辺は exact に `3^width * affineSeed` であり strict positive。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace RestartedTerminalGeometryPacket

/--
Case II endpoint `s=c` に残る actual exact bridge の affine-mass 表現。

これは「証明済み bridge」ではなく、残余 obligation を一個の equality に固定するための
候補命題である。
-/
def CaseIIEndpointActualMassBridgeCandidate
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N) : Prop :=
  (M.toPureBProfileObstruction hL).criticalizationStart =
      (M.toPureBProfileObstruction hL).terminalCriticalStart ∧
    D.toPair.modulus *
        D.toPair.doubleNormalizedQCandidate
          D.step0.edge.toFareyCellPacket.residue
          D.step1.edge.toFareyCellPacket.residue =
      ((profileAffineNumerator
          (M.toPureBProfileObstruction hL).terminalCriticalStart
          (M.toPureBProfileObstruction hL).h +
        2 ^ (beattyIndex S.b - 1 + S.width) : ℕ) : ℤ)

/--
同じ残余 bridge を actual criticalization state の surplus で書いた候補命題。

右辺は `s=c` exact endpoint balance により affine-mass 表現と一致する。
-/
def CaseIIEndpointActualSurplusBridgeCandidate
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N) : Prop :=
  let P := M.toPureBProfileObstruction hL
  P.criticalizationStart = P.terminalCriticalStart ∧
    D.toPair.modulus *
        D.toPair.doubleNormalizedQCandidate
          D.step0.edge.toFareyCellPacket.residue
          D.step1.edge.toFareyCellPacket.residue =
      (2 : ℤ) ^ beattyIndex P.terminalCriticalStart *
          P.criticalizationStartStateInt +
        (2 : ℤ) ^ (beattyIndex S.b - 1 + S.width) -
        (3 : ℤ) ^ P.terminalCriticalStart *
          (P.y - (P.q : ℤ))

/--
`s=c` exact balance により、affine-mass bridge と actual-state surplus bridge は同値。
-/
theorem actualMassBridgeCandidate_iff_actualSurplusBridgeCandidate
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    S.CaseIIEndpointActualMassBridgeCandidate D ↔
      S.CaseIIEndpointActualSurplusBridgeCandidate D := by
  let P := M.toPureBProfileObstruction hL
  constructor
  · intro H
    rcases H with ⟨hsEq, hMass⟩
    refine ⟨hsEq, ?_⟩
    have hEndpoint :=
      caseIIEndpoint_exactAffineBalance hStart hsEq
    push_cast at hMass
    linarith
  · intro H
    rcases H with ⟨hsEq, hSurplus⟩
    refine ⟨hsEq, ?_⟩
    have hEndpoint :=
      caseIIEndpoint_exactAffineBalance hStart hsEq
    push_cast
    linarith

/--
affine-mass bridge candidate が証明できれば、abstract positive-factor bridge を得る。
係数は exact に `3^width`。
-/
theorem caseIIEndpointAffineSharedCostBridge_of_actualMassBridgeCandidate
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (H : S.CaseIIEndpointActualMassBridgeCandidate D) :
    S.CaseIIEndpointAffineSharedCostBridge
      D.toPair
      D.step0.edge.toFareyCellPacket.residue
      D.step1.edge.toFareyCellPacket.residue := by
  rcases H with ⟨hsEq, hMass⟩
  refine ⟨hsEq, (3 : ℤ) ^ S.width, ?_, ?_⟩
  · positivity
  · calc
      D.toPair.modulus *
          D.toPair.doubleNormalizedQCandidate
            D.step0.edge.toFareyCellPacket.residue
            D.step1.edge.toFareyCellPacket.residue =
        ((profileAffineNumerator
            (M.toPureBProfileObstruction hL).terminalCriticalStart
            (M.toPureBProfileObstruction hL).h +
          2 ^ (beattyIndex S.b - 1 + S.width) : ℕ) : ℤ) := hMass
      _ =
        (3 : ℤ) ^ S.width * (S.affineSeed : ℤ) :=
          S.affineEndpointMass_cast_eq_threePow_mul_affineSeed

/--
actual-state surplus bridge candidate からも同じ abstract bridge を得る。
-/
theorem caseIIEndpointAffineSharedCostBridge_of_actualSurplusBridgeCandidate
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    (H : S.CaseIIEndpointActualSurplusBridgeCandidate D) :
    S.CaseIIEndpointAffineSharedCostBridge
      D.toPair
      D.step0.edge.toFareyCellPacket.residue
      D.step1.edge.toFareyCellPacket.residue := by
  have hMass : S.CaseIIEndpointActualMassBridgeCandidate D :=
    (S.actualMassBridgeCandidate_iff_actualSurplusBridgeCandidate
      D hStart).2 H
  exact
    S.caseIIEndpointAffineSharedCostBridge_of_actualMassBridgeCandidate
      D hMass

/--
affine-mass bridge candidate が閉じれば、actual two residues に対する strict `(R)` が得られる。
-/
theorem actualResidueSum_lt_gap_add_normalizedQ_of_massBridgeCandidate
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (H : S.CaseIIEndpointActualMassBridgeCandidate D) :
    D.step0.edge.toFareyCellPacket.residue +
        D.step1.edge.toFareyCellPacket.residue <
      D.toPair.gap + D.toPair.normalizedQ := by
  have hBridge :=
    S.caseIIEndpointAffineSharedCostBridge_of_actualMassBridgeCandidate D H
  exact
    S.defectSum_lt_gap_add_normalizedQ_of_caseIIEndpointBridge
      D.toPair
      D.step0.edge.toFareyCellPacket.residue
      D.step1.edge.toFareyCellPacket.residue
      hBridge

/-- actual-state surplus bridge candidate から strict `(R)` を得る。 -/
theorem actualResidueSum_lt_gap_add_normalizedQ_of_surplusBridgeCandidate
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    (H : S.CaseIIEndpointActualSurplusBridgeCandidate D) :
    D.step0.edge.toFareyCellPacket.residue +
        D.step1.edge.toFareyCellPacket.residue <
      D.toPair.gap + D.toPair.normalizedQ := by
  have hBridge :=
    S.caseIIEndpointAffineSharedCostBridge_of_actualSurplusBridgeCandidate
      D hStart H
  exact
    S.defectSum_lt_gap_add_normalizedQ_of_caseIIEndpointBridge
      D.toPair
      D.step0.edge.toFareyCellPacket.residue
      D.step1.edge.toFareyCellPacket.residue
      hBridge

/--
別経路として actual representative threshold を直接証明できても strict `(R)` は閉じる。
この定理は endpoint bridge と carry-threshold bridge の二経路を分離する。
-/
theorem actualResidueSum_lt_gap_add_normalizedQ_of_threshold_le
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (_S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (_hsEq :
      (M.toPureBProfileObstruction hL).criticalizationStart =
        (M.toPureBProfileObstruction hL).terminalCriticalStart)
    (hThreshold :
      D.toPair.representativeThreshold ≤ D.toPair.deltaSum) :
    D.step0.edge.toFareyCellPacket.residue +
        D.step1.edge.toFareyCellPacket.residue <
      D.toPair.gap + D.toPair.normalizedQ := by
  exact D.residueSum_lt_gap_add_normalizedQ_of_threshold_le hThreshold

end RestartedTerminalGeometryPacket

end MultiCorner
end CSTMicro
end Collatz2
