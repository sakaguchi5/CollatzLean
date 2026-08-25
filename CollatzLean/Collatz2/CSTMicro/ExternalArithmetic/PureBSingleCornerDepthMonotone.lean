import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleExposedCornerRigidity
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerBeattyTwoStep

/-!
# Pure B single-corner: depth monotonicity

single exposed corner packet では support `[b,c)` 上の checkpoint が

  p_k = beattyIndex b - 1 + (k - b)

という affine line に固定される。
Beatty index 自体は rank を一つ進むごとに少なくとも一つ増えるので、

  h_k = beattyIndex k - p_k

は `[b,c)` 上で単調非減少になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction.SingleExposedCornerRigidityPacket

/-- support 内の adjacent columns では depth は減らない。 -/
theorem depth_mono_succ
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {k : ℕ}
    (hbk : S.b ≤ k)
    (hk1c : k + 1 < P.terminalCriticalStart) :
    P.h k ≤ P.h (k + 1) := by
  have hkC : k < P.terminalCriticalStart := by
    omega
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hkM : k < P.m :=
    lt_of_lt_of_le hkC hcLeM
  have hk1M : k + 1 < P.m :=
    lt_of_lt_of_le hk1c hcLeM
  have hDepthK := P.admissible.depth_le hkM
  have hDepthK1 := P.admissible.depth_le hk1M
  have hLineK := S.checkpoint_line k hbk hkC
  have hLineK1 := S.checkpoint_line (k + 1) (by omega) hk1c
  have hBeatty := beattyIndex_lt_succ k
  unfold profileCheckpoint at hLineK hLineK1
  omega

/--
任意の `b ≤ k ≤ l < c` で depth は単調。

checkpoint line の差は exact に `l-k`、一方 Beatty index の増分は少なくとも `l-k`
なので、残差 height は減り得ない。
-/
theorem depth_mono
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {k l : ℕ}
    (hbk : S.b ≤ k)
    (hkl : k ≤ l)
    (hlc : l < P.terminalCriticalStart) :
    P.h k ≤ P.h l := by
  have hkC : k < P.terminalCriticalStart :=
    lt_of_le_of_lt hkl hlc
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hkM : k < P.m :=
    lt_of_lt_of_le hkC hcLeM
  have hlM : l < P.m :=
    lt_of_lt_of_le hlc hcLeM
  have hDepthK := P.admissible.depth_le hkM
  have hDepthL := P.admissible.depth_le hlM
  have hLineK := S.checkpoint_line k hbk hkC
  have hLineL := S.checkpoint_line l (le_trans hbk hkl) hlc
  have hEq : k + (l - k) = l :=
    Nat.add_sub_of_le hkl
  have hBeatty := beattyIndex_add_le k (l - k)
  rw [hEq] at hBeatty
  unfold profileCheckpoint at hLineK hLineL
  omega

/-- support 内の depth difference は Beatty excessそのもの。 -/
theorem depth_difference_eq_beatty_excess
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {k l : ℕ}
    (hbk : S.b ≤ k)
    (hkl : k ≤ l)
    (hlc : l < P.terminalCriticalStart) :
    beattyIndex l - beattyIndex k =
      (l - k) + (P.h l - P.h k) := by
  have hkC : k < P.terminalCriticalStart :=
    lt_of_le_of_lt hkl hlc
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hkM : k < P.m :=
    lt_of_lt_of_le hkC hcLeM
  have hlM : l < P.m :=
    lt_of_lt_of_le hlc hcLeM
  have hMono := S.depth_mono hbk hkl hlc
  have hLineK := S.checkpoint_line k hbk hkC
  have hLineL := S.checkpoint_line l (le_trans hbk hkl) hlc
  have hCheckpoint :
      profileCheckpoint P.h l =
        profileCheckpoint P.h k + (l - k) := by
    rw [hLineL, hLineK]
    omega
  exact
    P.admissible.depthDifference_eq_of_checkpoint_add
      hkM hlM hkl hMono hCheckpoint

end PureBProfileObstruction.SingleExposedCornerRigidityPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
