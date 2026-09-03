import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalAffineNumerator
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedActualSharedCostPairAssembly
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBExposedPredecessorDeltaB

/-!
# restarted actual cells と profile affine column の weight bridge

actual exposed predecessor cell の `deltaB` は global scale `m` で

  2^checkpoint(k) * 3^(m-k-1)

である。一方 restarted endpoint `c` までの local affine column は

  2^checkpoint(k) * 3^(c-k-1)

である。

`k<c` なら両者の差は共通 suffix factor `3^(m-c)` だけである。
特に terminal exposed cell `t=c-1` では local 3-power が消え、
checkpoint line により

  2 * deltaB_t = 3^(m-c) * 2^(beta(b)-1+width)

が exact に出る。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
`c` より左の actual exposed cell weight を、`c` scale の local affine column と
共通 terminal suffix factor に分解する。
-/
theorem exposedPredecessor_deltaB_eq_threePow_terminalSuffix_mul_localColumn
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (E : (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex k)
    {lower : ParityWord}
    (T : FerrersStep lower M.word)
    (hRank : T.edge.rankCut = k)
    (hkC :
      k < (M.toPureBProfileObstruction hL).terminalCriticalStart) :
    T.edge.deltaB =
      3 ^ ((M.toPureBProfileObstruction hL).m -
          (M.toPureBProfileObstruction hL).terminalCriticalStart) *
        (2 ^ profileCheckpoint (M.toPureBProfileObstruction hL).h k *
          3 ^ ((M.toPureBProfileObstruction hL).terminalCriticalStart - k - 1)) := by
  let P := M.toPureBProfileObstruction hL
  have hDelta :=
    M.exposedPredecessor_deltaB_eq_profileCornerMonomial
      hL E T hRank
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hkC' : k < P.terminalCriticalStart := by
    simpa [P] using hkC
  have hExp :
      P.m - k - 1 =
        (P.m - P.terminalCriticalStart) +
          (P.terminalCriticalStart - k - 1) := by
    omega
  change
    T.edge.deltaB =
      3 ^ (P.m - P.terminalCriticalStart) *
        (2 ^ profileCheckpoint P.h k *
          3 ^ (P.terminalCriticalStart - k - 1))
  rw [hDelta, hExp, pow_add]
  ring

namespace LastTwoSharedCostActualPairAssemblyInput

/-- previous exposed actual cell の global `deltaB` を local `c` column へ戻す。 -/
theorem step0_deltaB_eq_threePow_terminalSuffix_mul_localColumn
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N) :
    D.step0.edge.deltaB =
      3 ^ ((M.toPureBProfileObstruction hL).m -
          (M.toPureBProfileObstruction hL).terminalCriticalStart) *
        (2 ^ profileCheckpoint
            (M.toPureBProfileObstruction hL).h N.previous *
          3 ^ ((M.toPureBProfileObstruction hL).terminalCriticalStart -
            N.previous - 1)) := by
  let P := M.toPureBProfileObstruction hL
  have E0 : P.IsExposedPredecessorIndex N.previous :=
    (P.mem_exposedPredecessorSet_iff).1 N.previous_mem
  have hkC : N.previous < P.terminalCriticalStart := by
    have hPrevTerm := N.previous_lt_terminal
    have hTermEq :
        N.terminal = P.terminalCriticalStart - 1 := by
      simpa [P] using S.terminal_eq
    have hcPos : 0 < P.terminalCriticalStart := by
      simpa [P] using S.terminalCriticalStart_pos
    omega
  simpa [P] using
    exposedPredecessor_deltaB_eq_threePow_terminalSuffix_mul_localColumn
      M hL E0 D.step0 D.rank0_eq hkC

/--
terminal exposed actual cell の weight と restarted boundary mass の exact bridge。

  2 * deltaB_terminal
    = 3^(m-c) * 2^(beta(b)-1+width).
-/
theorem two_mul_step1_deltaB_eq_threePow_terminalSuffix_mul_boundaryMass
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N) :
    2 * D.step1.edge.deltaB =
      3 ^ ((M.toPureBProfileObstruction hL).m -
          (M.toPureBProfileObstruction hL).terminalCriticalStart) *
        2 ^ (beattyIndex S.b - 1 + S.width) := by
  let P := M.toPureBProfileObstruction hL
  have E1 : P.IsExposedPredecessorIndex N.terminal :=
    (P.mem_exposedPredecessorSet_iff).1 N.terminal_mem
  have hDelta :=
    M.exposedPredecessor_deltaB_eq_profileCornerMonomial
      hL E1 D.step1 D.rank1_eq
  have hcPos : 0 < P.terminalCriticalStart :=
    S.terminalCriticalStart_pos
  have hbC : S.b < P.terminalCriticalStart :=
    S.b_lt_terminalCriticalStart
  have htEq : N.terminal = P.terminalCriticalStart - 1 :=
    S.terminal_eq
  have hbT : S.b ≤ N.terminal := by
    omega
  have htC : N.terminal < P.terminalCriticalStart := by
    omega
  have hCheckpoint := S.checkpoint_line hbT htC
  have hcEq : P.terminalCriticalStart = S.b + S.width :=
    S.terminalCriticalStart_eq_b_add_width
  have hCheckpointSucc :
      profileCheckpoint P.h N.terminal + 1 =
        beattyIndex S.b - 1 + S.width := by
    rw [hCheckpoint]
    omega
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hRightExp :
      P.m - N.terminal - 1 =
        P.m - P.terminalCriticalStart := by
    omega
  change
    2 * D.step1.edge.deltaB =
      3 ^ (P.m - P.terminalCriticalStart) *
        2 ^ (beattyIndex S.b - 1 + S.width)
  rw [hDelta, hRightExp]
  calc
    2 *
        (2 ^ profileCheckpoint P.h N.terminal *
          3 ^ (P.m - P.terminalCriticalStart)) =
      2 ^ (profileCheckpoint P.h N.terminal + 1) *
        3 ^ (P.m - P.terminalCriticalStart) := by
          rw [pow_succ]
          ring
    _ =
      2 ^ (beattyIndex S.b - 1 + S.width) *
        3 ^ (P.m - P.terminalCriticalStart) := by
          rw [hCheckpointSucc]
    _ =
      3 ^ (P.m - P.terminalCriticalStart) *
        2 ^ (beattyIndex S.b - 1 + S.width) := by
          ring

end LastTwoSharedCostActualPairAssemblyInput

end MultiCorner
end CSTMicro
end Collatz2
