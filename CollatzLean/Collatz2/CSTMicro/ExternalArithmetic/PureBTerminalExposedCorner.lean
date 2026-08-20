import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBExposedPredecessorRealization

/-!
# Pure B: terminal noncritical top is exposed

Stage 9C で actual terminal top cell は genuine first-passage predecessor として構成された。
前段の exposed-index dictionary を使い、その rank cut `c-1` が `E(B)` に必ず入ることを固定する。

従って actual minimal B では exposed predecessor set は空ではない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/-- actual minimal B の terminal cut `c-1` は exposed。 -/
theorem terminalPred_isExposed
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    P.IsExposedPredecessorIndex (P.terminalCriticalStart - 1) := by
  let P := M.toPureBProfileObstruction hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  have hcPos : 0 < P.terminalCriticalStart := by
    have hLe := P.criticalizationStart_le_terminalCriticalStart
    omega
  obtain ⟨lower, S, hLowerFP, hPos, hLeft, hOdd⟩ :=
    M.exists_terminalTopCellActualPredecessor R hL
  have hLeftP :
      S.edge.fareyLeftExponent =
        P.terminalCriticalStart := by
    simpa [P] using hLeft
  have hSucc :
      S.edge.rankCut + 1 =
        P.terminalCriticalStart := by
    simpa [
      AdjacentFerrersSwap.fareyLeftExponent,
      AdjacentFerrersSwap.rankCut
    ] using hLeftP
  have hRank :
      S.edge.rankCut =
        P.terminalCriticalStart - 1 := by
    calc
      S.edge.rankCut
          = (S.edge.rankCut + 1) - 1 := by
              simp
      _ = P.terminalCriticalStart - 1 := by
            rw [hSucc]
  have hActual :
      HasActualExposedPredecessorAt M (P.terminalCriticalStart - 1) :=
    ⟨lower, S, hLowerFP, hRank⟩
  have hPure :=
    (M.exposedIndex_iff_actualPredecessor hL).2 hActual
  simpa [P] using hPure

/-- terminal exposed cut は exposed set に属する。 -/
theorem terminalPred_mem_exposedPredecessorSet
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    let P := M.toPureBProfileObstruction hL
    P.terminalCriticalStart - 1 ∈ P.exposedPredecessorSet := by
  let P := M.toPureBProfileObstruction hL
  rw [P.mem_exposedPredecessorSet_iff]
  simpa [P] using M.terminalPred_isExposed R hL

/-- actual minimal B の exposed predecessor set は nonempty。 -/
theorem exposedPredecessorSet_nonempty
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).exposedPredecessorSet.Nonempty := by
  let P := M.toPureBProfileObstruction hL
  exact ⟨P.terminalCriticalStart - 1,
    by simpa [P] using M.terminalPred_mem_exposedPredecessorSet R hL⟩

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
