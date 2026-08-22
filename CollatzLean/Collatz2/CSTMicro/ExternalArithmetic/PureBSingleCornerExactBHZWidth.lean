import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BHZCriticalOneShortSelectorExact
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTailExactOneShort
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerCriticalizationRun

set_option linter.style.emptyLine false

/-!
# Pure B single-corner: exact BHZ denominator band による width bound

single-corner の dyadic scale `ell` に対し

  N = 19 + 15*ell

を置く。critical continued-fraction denominator が

  P_j <= N < P_(j+1)

を満たす band にあるとする。

exact BHZ one-short selector を level `j` に適用すると、任意 phase で

  P_(j+1) <= r <= P_(j+1) + P_(j+2)

を満たす one-short root が得られる。したがって前ファイルの exact terminal
localization から

  m - criticalizationStart
    <= 2 * (P_(j+1) + P_(j+2))

となる。

さらに既存の single-corner criticalization-run bound

  criticalizationStart - b <= 18 + 15*ell

を足し合わせ、degree 196 の polynomial majorant を一切経由せず

  m - b
    <= 2 * (P_(j+1) + P_(j+2)) + (18 + 15*ell)

を得る。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/--
exact BHZ denominator band から single-corner の全 terminal width を直接評価する。

`hBandLower` は `N` が指定 band に属することを記録するために statement に残す。
root の下界にはより強い `P_(j+1) <= r` が selector から直接入る。
-/
theorem singleCorner_m_sub_b_le_exactBHZBand
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {ell j : ℕ}
    (hmSize :
      (M.toPureBProfileObstruction hL).m + 1 ≤ 2 ^ ell)
    (hj : 2 ≤ j)
    (hBandLower :
      criticalPowerP j ≤ 19 + 15 * ell)
    (hBandUpper :
      19 + 15 * ell < criticalPowerP (j + 1)) :
    (M.toPureBProfileObstruction hL).m - S.b ≤
      2 * (criticalPowerP (j + 1) + criticalPowerP (j + 2)) +
        (18 + 15 * ell) := by
  let P := M.toPureBProfileObstruction hL
  let s : ℕ := P.criticalizationStart - 1
  let B : CriticalBHZPhasePacket s :=
    actualBHZCriticalCanonicalPacket s

  rcases
      actualBHZCritical_exists_oneShort_between_q_and_q_add_q_succ
        B hj with
    ⟨r, hQjr, hrUpper, hOneShort⟩

  have hQj :
      criticalBHZq j = criticalPowerP (j + 1) := rfl
  have hQj1 :
      criticalBHZq (j + 1) = criticalPowerP (j + 2) := by
    unfold criticalBHZq
    congr 1

  have hNr : 19 + 15 * ell ≤ r := by
    rw [hQj] at hQjr
    omega

  have hrUpper' :
      r ≤ criticalPowerP (j + 1) + criticalPowerP (j + 2) := by
    rw [hQj, hQj1] at hrUpper
    exact hrUpper

  have hy : 0 ≤ P.y := by
    simpa [P] using M.toPureBProfileObstruction_y_nonneg hL

  have hStartPos : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL

  have hTail :
      P.m - P.criticalizationStart ≤ 2 * r := by
    exact
      P.criticalizationTail_le_twice_oneShortRoot
        R hy hStartPos
        (by simpa [P] using hmSize)
        hNr
        (by simpa [s] using hOneShort)

  have hTailExact :
      P.m - P.criticalizationStart ≤
        2 * (criticalPowerP (j + 1) + criticalPowerP (j + 2)) := by
    exact le_trans hTail (Nat.mul_le_mul_left 2 hrUpper')

  have hLeft :=
    M.singleCorner_criticalizationStart_sub_b_le_dyadic15
      R hL S hmSize

  have hStartLe : P.criticalizationStart ≤ P.m :=
    P.criticalizationStart_spec.1

  -- `hBandLower` は band の完全な記録として保持する。
  have _hBandRecorded :
      criticalPowerP j ≤ 19 + 15 * ell := hBandLower

  dsimp [P] at hTailExact hLeft hStartLe ⊢
  omega

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
