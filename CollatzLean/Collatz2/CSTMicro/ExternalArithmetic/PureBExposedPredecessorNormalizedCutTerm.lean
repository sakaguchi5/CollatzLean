import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBExposedPredecessorDeltaB
import CollatzLean.Collatz2.CSTMicro.CarryGeometry.GeneralPredecessorRankCellBridge

/-!
# Pure B exposed predecessor: normalized cut term と `deltaB`

一般の upper first-passage adjacent Ferrers cell について既に成立している

  normalizedCutTerm(rankCut) = 3 * deltaB

を、actual minimal bad word の exposed predecessor cut `k` へ lossless に移す。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/--
actual exposed predecessor cut `k` では normalized cut term は exact に `3 * deltaB`。
-/
theorem exposedPredecessor_normalizedCutTerm_eq_three_mul_deltaB
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (E : (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex k)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hRank : S.edge.rankCut = k) :
    Collatz2.Word.normalizedCutTerm
        (exponentWordOfParity M.word) k =
      3 * S.edge.deltaB := by
  have _hk := E.lt_m
  have _hDelta :=
    M.exposedPredecessor_deltaB_eq_profileCornerMonomial
      hL E S hRank
  have hEdgeUpperFP : IsFirstPassageWord S.edge.upperWord := by
    exact
      Eq.mp
        (congrArg IsFirstPassageWord S.upper_eq)
        M.word_firstPassage
  have hCore :=
    S.edge.normalizedCutTerm_rankCut_eq_three_mul_deltaB hEdgeUpperFP
  have hRankWord :
      S.edge.rankUpperExponentWord = exponentWordOfParity M.word := by
    unfold AdjacentFerrersSwap.rankUpperExponentWord
    exact (congrArg exponentWordOfParity S.upper_eq).symm
  rw [hRankWord, hRank] at hCore
  exact hCore

end MinimalActualABObstructionPacket
end ExternalArithmetic
end CSTMicro
end Collatz2
