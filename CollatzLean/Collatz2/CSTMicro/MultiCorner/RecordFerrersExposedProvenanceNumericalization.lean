import CollatzLean.Collatz2.CSTMicro.MultiCorner.RecordFerrersExposedProvenance
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBExposedPredecessorDeltaB

/-!
# RecordFerrers exposed provenance の数値化

一つの exposed cut `k` では provenance が

  h(k) = localDefect + glueCarry

を保持する。

また actual Ferrers predecessor cell の affine gap は

  deltaB = 2^(profileCheckpoint h k) * 3^(m-k-1)

である。

`profileCheckpoint h k + h(k) = beattyIndex k` を合わせると、provenance が担う
2-adic depth を `deltaB` に戻した量は exact に

  2^(localDefect + glueCarry) * deltaB
    = 2^(beattyIndex k) * 3^(m-k-1)

となる。

注意: このファイルは「内部-cut telescope の endpoint correction」とこの monomial が
同じ量であることまでは主張しない。その同定には Ferrers telescope の境界値と
actual exposed cell を結ぶ追加 bridge が必要である。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace RecordFerrersCutProvenance

/--
provenance の `localDefect + glueCarry` は、profile checkpoint から Beatty roof までの
不足 depth そのもの。
-/
theorem profileCheckpoint_add_localDefect_add_glueCarry_eq_beatty
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k)
    (hk : k < P.m) :
    profileCheckpoint P.h k + Q.localDefect + Q.glueCarry =
      beattyIndex k := by
  have hDepth := P.admissible.depth_le hk
  have hFactor := Q.factorization
  unfold profileCheckpoint
  omega

/--
exposed cut なら上の checkpoint identity を直接使える wrapper。
-/
theorem profileCheckpoint_add_localDefect_add_glueCarry_eq_beatty_of_exposed
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k)
    (E : P.IsExposedPredecessorIndex k) :
    profileCheckpoint P.h k + Q.localDefect + Q.glueCarry =
      beattyIndex k :=
  Q.profileCheckpoint_add_localDefect_add_glueCarry_eq_beatty E.lt_m

/--
actual minimal-B の exposed predecessor cell で provenance を数値化する exact identity。

provenance の不足 depth `localDefect + glueCarry` を `deltaB` の 2-power に掛け戻すと、
cut `k` の Beatty weight を持つ一セル monomialになる。
-/
theorem twoPow_provenance_mul_exposedDeltaB_eq_beattyCellMonomial
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (Q : RecordFerrersCutProvenance
      (M.toPureBProfileObstruction hL) k)
    (E : (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex k)
    {lower : ParityWord}
    (S : FerrersStep lower M.word)
    (hRank : S.edge.rankCut = k) :
    2 ^ (Q.localDefect + Q.glueCarry) * S.edge.deltaB =
      2 ^ beattyIndex k *
        3 ^ ((M.toPureBProfileObstruction hL).m - k - 1) := by
  let P := M.toPureBProfileObstruction hL
  have hDelta :=
    M.exposedPredecessor_deltaB_eq_profileCornerMonomial
      hL E S hRank
  have hBeatty :
      profileCheckpoint P.h k + Q.localDefect + Q.glueCarry =
        beattyIndex k := by
    simpa [P] using
      Q.profileCheckpoint_add_localDefect_add_glueCarry_eq_beatty_of_exposed E
  have hExponent :
      Q.localDefect + Q.glueCarry + profileCheckpoint P.h k =
        beattyIndex k := by
    omega
  calc
    2 ^ (Q.localDefect + Q.glueCarry) * S.edge.deltaB
        =
      2 ^ (Q.localDefect + Q.glueCarry) *
        (2 ^ profileCheckpoint P.h k * 3 ^ (P.m - k - 1)) := by
          rw [hDelta]
    _ =
      (2 ^ (Q.localDefect + Q.glueCarry) *
          2 ^ profileCheckpoint P.h k) *
        3 ^ (P.m - k - 1) := by
          ring
    _ =
      2 ^ (Q.localDefect + Q.glueCarry + profileCheckpoint P.h k) *
        3 ^ (P.m - k - 1) := by
          rw [← pow_add]
    _ = 2 ^ beattyIndex k * 3 ^ (P.m - k - 1) := by
          rw [hExponent]
    _ =
      2 ^ beattyIndex k *
        3 ^ ((M.toPureBProfileObstruction hL).m - k - 1) := by
          rfl

end RecordFerrersCutProvenance

end MultiCorner
end CSTMicro
end Collatz2
