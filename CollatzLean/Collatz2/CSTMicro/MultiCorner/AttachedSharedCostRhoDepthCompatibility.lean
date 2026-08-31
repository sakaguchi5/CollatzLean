import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalTailDepthCoordinates
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedSharedCostCheckpoint

/-!
# MultiCorner attached branch: rho / width / entrance-depth compatibility

Shared-Cost 側では

* straight transport の `width`, `rho`,
* entrance Hensel 側の `width`, `entranceDepth`

が純算術 packet の独立変数として保持されている。
一方 actual `AttachedTwoCornerPacket` では、これらは同じ terminal corridor の
幾何量から決まる。

このファイルでは、その対応を壊さずに戻す。

主な内容は次の三本。

1. previous exposed corner の excess carry

     rho = carryRunGap(previous) - 1

2. straight width

     W = terminal - previous

3. endpoint depth identity

     beta(previous) + W + rho + h(terminal)
       = beta(terminal) + h(previous)

さらに `AttachedSharedCostCheckpoint` 自体へ field を追加して既存 constructor を壊す代わりに、
actual geometry との compatibility packet を外付けする。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
previous exposed corner の carry gap から straight baseline `1` を除いた excess。

abstract Shared-Cost transport に現れる `rho` の actual 幾何版である。
-/
noncomputable def previousCarryExcess
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) : ℕ :=
  carryRunGap
      P P.terminalCriticalStart A.normalForm.previous - 1

/-- previous exposed corner は nonstraight なので excess は正。 -/
theorem previousCarryExcess_pos
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    0 < A.previousCarryExcess := by
  unfold previousCarryExcess
  have hGap := A.two_le_previous_carryRunGap
  omega

/--
`rho` を baseline `1` と足し戻すと actual previous carry gap に戻る。
Nat subtraction の truncation は `gap >= 2` により起こらない。
-/
theorem previousCarryExcess_add_one
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    A.previousCarryExcess + 1 =
      carryRunGap
        P P.terminalCriticalStart A.normalForm.previous := by
  unfold previousCarryExcess
  have hGap := A.two_le_previous_carryRunGap
  omega

/--
previous checkpoint から straight Hensel start への一段は
`rho + 1` だけ進む。

  q(previous) + rho + 1 = q(straightStart)

ここで `q(k) = beta(k) - h(k)`。
-/
theorem previousCarryExcess_checkpoint_identity
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    profileCheckpoint P.h A.normalForm.previous +
          A.previousCarryExcess + 1 =
      profileCheckpoint P.h A.straightHenselStart := by
  have hpC :
      A.normalForm.previous < P.terminalCriticalStart :=
    A.previous_mem_arithmeticCorridor.2
  have hpsC :
      A.normalForm.previous + 1 < P.terminalCriticalStart :=
    A.previous_succ_lt_terminalCriticalStart
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hGap :=
    carryCheckpoint_add_carryRunGap_eq_succ
      P hpC hcM
  rw [carryCheckpoint_of_lt P hpC] at hGap
  rw [carryCheckpoint_of_lt P hpsC] at hGap
  rw [← A.previousCarryExcess_add_one] at hGap
  unfold straightHenselStart
  omega

/--
previous corner の excess carry と straight entrance depth を exact に結ぶ局所式。

  beta(p) + rho + 1 + h(s) = beta(s) + h(p)

ここで `p = previous`, `s = straightHenselStart`。
-/
theorem previousCarryExcess_depth_identity
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    beattyIndex A.normalForm.previous +
          A.previousCarryExcess + 1 +
          P.h A.straightHenselStart =
      beattyIndex A.straightHenselStart +
          P.h A.normalForm.previous := by
  have hCheckpoint :=
    A.previousCarryExcess_checkpoint_identity
  have hpM : A.normalForm.previous < P.m :=
    A.previous_isExposed.lt_m
  have hsM : A.straightHenselStart < P.m := by
    have hsC := A.straightHenselStart_lt_terminalCriticalStart
    have hcM := P.terminalCriticalStart_spec.1
    omega
  have hpDepth := P.admissible.depth_le hpM
  have hsDepth := P.admissible.depth_le hsM
  unfold profileCheckpoint at hCheckpoint
  omega

/--
straight Hensel width は last two exposed cuts の index 差そのもの。

  W = terminal - previous
-/
theorem straightHenselWidth_eq_terminal_sub_previous
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    A.straightHenselWidth =
      A.normalForm.terminal - A.normalForm.previous := by
  unfold straightHenselWidth straightHenselStart
  have hPrevTerm := A.normalForm.previous_lt_terminal
  have hTermEq := A.terminal_eq
  have hcPos := A.terminalCriticalStart_pos
  omega

/--
straight suffix の内部では checkpoint は一列ごとに exact に `+1`。

既存 `internal_carryRunGap_eq_one` だけを使って再構成する。
`AttachedTerminalTailDepthCoordinates` 内にも同内容の private 補題があるが、
この compatibility file から使える public bridge をここで持つ。
-/
theorem straightProfileCheckpoint_eq_start_add
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    profileCheckpoint P.h (A.straightHenselStart + i) =
      profileCheckpoint P.h A.straightHenselStart + i := by
  induction i with
  | zero =>
      simp
  | succ i ih =>
      have hiPrev : i < A.straightHenselWidth := by
        omega
      have hIH := ih hiPrev
      have hEnd := A.straightHenselStart_add_width
      let k := A.straightHenselStart + i
      have hPrev : A.normalForm.previous < k := by
        dsimp [k]
        unfold straightHenselStart
        omega
      have hTerm : k < A.normalForm.terminal := by
        rw [A.terminal_eq]
        dsimp [k]
        omega
      have hkC : k + 1 < P.terminalCriticalStart := by
        dsimp [k]
        omega
      have hGap :=
        A.internal_carryRunGap_eq_one hPrev hTerm
      have hGap' :
          profileCheckpoint P.h (k + 1) -
              profileCheckpoint P.h k = 1 := by
        rw [← carryRunGap_of_succ_lt P hkC]
        exact hGap
      have hcM : P.terminalCriticalStart ≤ P.m :=
        P.terminalCriticalStart_spec.1
      have hkM : k + 1 < P.m := by
        omega
      have hStrict :=
        P.admissible.checkpoint_strict (k := k) hkM
      have hStep :
          profileCheckpoint P.h (k + 1) =
            profileCheckpoint P.h k + 1 := by
        omega
      have hIdx0 :
          A.straightHenselStart + i = k := by
        rfl
      have hIdx1 :
          A.straightHenselStart + (i + 1) = k + 1 := by
        dsimp [k]
        omega
      rw [hIdx1, hStep, ← hIdx0, hIH]
      omega

/--
previous から terminal exposed cut までの checkpoint 差は exact に `W + rho`。

  q(terminal) = q(previous) + W + rho
-/
theorem terminalProfileCheckpoint_eq_previous_add_width_add_excess
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    profileCheckpoint P.h A.normalForm.terminal =
      profileCheckpoint P.h A.normalForm.previous +
        A.straightHenselWidth + A.previousCarryExcess := by
  have hWidthPos := A.straightHenselWidth_pos
  have hi :
      A.straightHenselWidth - 1 < A.straightHenselWidth := by
    omega
  have hStraight :=
    A.straightProfileCheckpoint_eq_start_add
      (i := A.straightHenselWidth - 1) hi
  have hEnd := A.straightHenselStart_add_width
  have hTerminalIndex :
      A.straightHenselStart + (A.straightHenselWidth - 1) =
        A.normalForm.terminal := by
    have hTermEq := A.terminal_eq
    omega
  rw [hTerminalIndex] at hStraight
  have hPrevious := A.previousCarryExcess_checkpoint_identity
  omega

/--
Shared-Cost transport の指数 `W + rho` を actual endpoint depths へ戻す主 bridge。

  beta(p) + W + rho + h(t) = beta(t) + h(p)

ここで `p = previous`, `t = terminal`。
したがって abstract transport の `2^(W+rho)` は、actual profile の
両端 checkpoint 差そのものである。
-/
theorem previous_to_terminal_depth_identity
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    beattyIndex A.normalForm.previous +
          A.straightHenselWidth + A.previousCarryExcess +
          P.h A.normalForm.terminal =
      beattyIndex A.normalForm.terminal +
          P.h A.normalForm.previous := by
  have hCheckpoint :=
    A.terminalProfileCheckpoint_eq_previous_add_width_add_excess
  have hpM : A.normalForm.previous < P.m :=
    A.previous_isExposed.lt_m
  have htM : A.normalForm.terminal < P.m :=
    A.terminal_isExposed.lt_m
  have hpDepth := P.admissible.depth_le hpM
  have htDepth := P.admissible.depth_le htM
  unfold profileCheckpoint at hCheckpoint
  omega

end AttachedTwoCornerPacket

/--
純算術 `AttachedSharedCostCheckpoint` と actual attached geometry の compatibility。

既存 checkpoint structure に field を直接追加すると既存 constructor を壊すため、
外付け packet として保持する。
-/
structure AttachedSharedCostActualCompatibility
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (C : AttachedSharedCostCheckpoint) : Prop where
  /-- transport width は actual straight width。 -/
  transfer_width_eq :
    C.transfer.width = A.straightHenselWidth

  /-- transport rho は actual previous excess carry。 -/
  transfer_rho_eq :
    C.transfer.rho = A.previousCarryExcess

  /-- Hensel width も同じ actual straight width。 -/
  hensel_width_eq :
    C.hensel.width = A.straightHenselWidth

  /-- entrance Hensel depth は actual straight start depth。 -/
  hensel_entranceDepth_eq :
    C.hensel.entranceDepth = P.h A.straightHenselStart

namespace AttachedSharedCostActualCompatibility

/-- transport と Hensel は同じ corridor width を見る。 -/
theorem widths_eq
    {P : PureBProfileObstruction}
    {A : AttachedTwoCornerPacket P}
    {C : AttachedSharedCostCheckpoint}
    (K : AttachedSharedCostActualCompatibility A C) :
    C.transfer.width = C.hensel.width := by
  calc
    C.transfer.width = A.straightHenselWidth := K.transfer_width_eq
    _ = C.hensel.width := K.hensel_width_eq.symm

/-- actual attached branch では abstract transport rho も正。 -/
theorem transfer_rho_pos
    {P : PureBProfileObstruction}
    {A : AttachedTwoCornerPacket P}
    {C : AttachedSharedCostCheckpoint}
    (K : AttachedSharedCostActualCompatibility A C) :
    0 < C.transfer.rho := by
  rw [K.transfer_rho_eq]
  exact A.previousCarryExcess_pos

/--
abstract `rho` と abstract `entranceDepth` は独立ではなく、
actual previous/start depth identity を同時に満たす。
-/
theorem rho_entranceDepth_identity
    {P : PureBProfileObstruction}
    {A : AttachedTwoCornerPacket P}
    {C : AttachedSharedCostCheckpoint}
    (K : AttachedSharedCostActualCompatibility A C) :
    beattyIndex A.normalForm.previous +
          C.transfer.rho + 1 + C.hensel.entranceDepth =
      beattyIndex A.straightHenselStart +
          P.h A.normalForm.previous := by
  rw [K.transfer_rho_eq, K.hensel_entranceDepth_eq]
  exact A.previousCarryExcess_depth_identity

/--
Shared-Cost transport の abstract `width + rho` を actual endpoint depth identity へ戻す。
-/
theorem transport_endpoint_depth_identity
    {P : PureBProfileObstruction}
    {A : AttachedTwoCornerPacket P}
    {C : AttachedSharedCostCheckpoint}
    (K : AttachedSharedCostActualCompatibility A C) :
    beattyIndex A.normalForm.previous +
          C.transfer.width + C.transfer.rho +
          P.h A.normalForm.terminal =
      beattyIndex A.normalForm.terminal +
          P.h A.normalForm.previous := by
  rw [K.transfer_width_eq, K.transfer_rho_eq]
  exact A.previous_to_terminal_depth_identity

end AttachedSharedCostActualCompatibility

/--
既存 Shared-Cost checkpoint と actual geometry compatibility を一つに束ねる refined packet。
後段の最終算術排除はこの packet を受け取れば、`width/rho/entranceDepth` を
独立変数として誤って扱わずに済む。
-/
structure AttachedSharedCostActualCheckpoint
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) where
  checkpoint : AttachedSharedCostCheckpoint
  compatibility :
    AttachedSharedCostActualCompatibility A checkpoint

namespace AttachedSharedCostActualCheckpoint

/-- refined packet から既存三本柱の arithmetic obligation をそのまま取り出す。 -/
theorem arithmetic_obligation
    {P : PureBProfileObstruction}
    {A : AttachedTwoCornerPacket P}
    (X : AttachedSharedCostActualCheckpoint A) :
    AttachedSharedCostCheckpoint.AttachedSharedCostArithmeticObligation X.checkpoint :=
  X.checkpoint.arithmetic_obligation

/-- refined packet では transport/Hensel width が一致する。 -/
theorem widths_eq
    {P : PureBProfileObstruction}
    {A : AttachedTwoCornerPacket P}
    (X : AttachedSharedCostActualCheckpoint A) :
    X.checkpoint.transfer.width = X.checkpoint.hensel.width :=
  X.compatibility.widths_eq

/-- refined packet では abstract rho は actual previous excess carry。 -/
theorem rho_eq_previousCarryExcess
    {P : PureBProfileObstruction}
    {A : AttachedTwoCornerPacket P}
    (X : AttachedSharedCostActualCheckpoint A) :
    X.checkpoint.transfer.rho = A.previousCarryExcess :=
  X.compatibility.transfer_rho_eq

/-- refined packet では entrance depth は actual straight-start depth。 -/
theorem entranceDepth_eq_straightStartDepth
    {P : PureBProfileObstruction}
    {A : AttachedTwoCornerPacket P}
    (X : AttachedSharedCostActualCheckpoint A) :
    X.checkpoint.hensel.entranceDepth =
      P.h A.straightHenselStart :=
  X.compatibility.hensel_entranceDepth_eq

/-- refined packet 上の endpoint rho-depth bridge。 -/
theorem transport_endpoint_depth_identity
    {P : PureBProfileObstruction}
    {A : AttachedTwoCornerPacket P}
    (X : AttachedSharedCostActualCheckpoint A) :
    beattyIndex A.normalForm.previous +
          X.checkpoint.transfer.width +
          X.checkpoint.transfer.rho +
          P.h A.normalForm.terminal =
      beattyIndex A.normalForm.terminal +
          P.h A.normalForm.previous :=
  X.compatibility.transport_endpoint_depth_identity

end AttachedSharedCostActualCheckpoint

end MultiCorner
end CSTMicro
end Collatz2
