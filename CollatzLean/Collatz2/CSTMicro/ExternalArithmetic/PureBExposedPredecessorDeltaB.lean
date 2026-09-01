import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBExposedPredecessorRealization

/-!
# Pure B exposed predecessor: `deltaB` と profile corner monomial

actual minimal bad word `M.word` に入る exposed predecessor cell を rank cut `k` で読む。

pure profile と actual exponent word の checkpoint bridge、および
adjacent Ferrers cell の座標を合わせると

  position = profileCheckpoint h k,
  oddCount(rightContext) = m - k - 1

である。従って affine change `deltaB` は exact に

  deltaB = 2^(profileCheckpoint h k) * 3^(m-k-1)

となる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/--
exposed predecessor cell の `deltaB` は、同じ cut の Pure-B corner monomial と一致する。
-/
theorem exposedPredecessor_deltaB_eq_profileCornerMonomial
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (E : (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex k)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hRank : S.edge.rankCut = k) :
    S.edge.deltaB =
      2 ^ profileCheckpoint (M.toPureBProfileObstruction hL).h k *
        3 ^ ((M.toPureBProfileObstruction hL).m - k - 1) := by
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  have hk : k < P.m := by
    simpa [P] using E.lt_m
  have hEdgeUpperFP : IsFirstPassageWord S.edge.upperWord := by
    exact
      Eq.mp
        (congrArg IsFirstPassageWord S.upper_eq)
        M.word_firstPassage
  have hRankWord :
      S.edge.rankUpperExponentWord = w := by
    unfold AdjacentFerrersSwap.rankUpperExponentWord
    exact (congrArg exponentWordOfParity S.upper_eq).symm
  have hProfileCheckpoint :
      profileCheckpoint P.h k =
        Collatz2.Word.prefixTwoDepth w k := by
    calc
      profileCheckpoint P.h k
          = P.profileEndpointCheckpoint k := by
              symm
              exact P.profileEndpointCheckpoint_of_lt hk
      _ = Collatz2.Word.prefixTwoDepth w k := by
            simpa [P, w] using
              M.profileEndpointCheckpoint_eq_actualPrefixTwoDepth
                hL (Nat.le_of_lt hk)
  have hAtCut :=
    S.edge.prefixTwoDepth_rankCut_eq_position hEdgeUpperFP
  have hPosition :
      S.edge.position = profileCheckpoint P.h k := by
    calc
      S.edge.position
          = Collatz2.Word.prefixTwoDepth
              S.edge.rankUpperExponentWord S.edge.rankCut := hAtCut.symm
      _ = Collatz2.Word.prefixTwoDepth w k := by
            rw [hRankWord, hRank]
      _ = profileCheckpoint P.h k := hProfileCheckpoint.symm
  have hOddTotal : S.edge.oddTotal = P.m := by
    calc
      S.edge.oddTotal = oddCount S.edge.upperWord :=
        S.edge.upperWord_oddCount.symm
      _ = oddCount M.word := by
        rw [← S.upper_eq]
      _ = P.m := by
        symm
        simpa [P] using
          M.toPureBProfileObstruction_m_eq_wordOddCount hL
  have hRight :
      oddCount S.edge.rightContext = P.m - k - 1 := by
    unfold AdjacentFerrersSwap.oddTotal at hOddTotal
    unfold AdjacentFerrersSwap.rankCut at hRank
    omega
  change
    S.edge.deltaB =
      2 ^ profileCheckpoint P.h k * 3 ^ (P.m - k - 1)
  unfold AdjacentFerrersSwap.deltaB
  rw [hPosition, hRight]

end MinimalActualABObstructionPacket
end ExternalArithmetic
end CSTMicro
end Collatz2
