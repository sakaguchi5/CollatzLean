import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCanonicalHenselBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalTopCellActualPredecessor
import Mathlib.Tactic.Ring

/-!
# MultiCorner attached branch: terminal top / straight-start exact coordinates

このファイルでは attached branch の high-depth 側を Farey terminal coordinate へ
送り直すための三つの exact theorem をまとめる。

1. actual terminal-top predecessor の position は terminal rank `c-1` 以上。
2. straight Hensel start の depth は terminal-top の Beatty slack 以下。
3. terminal Farey tail depth `H-position` を `ℤ` 上で
   Beatty gap・straight width・straight-start depth の exact identity にする。

三つ目を `ℤ` で述べるのは、Nat の途中減算による truncation を避けて
`+ startDepth` を情報損失なしで露出させるためである。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- Bool word の odd count は length を越えない。 -/
private theorem cstOddCount_le_length
    (v : ParityWord) :
    oddCount v ≤ v.length := by
  induction v with
  | nil =>
      simp [oddCount]
  | cons b v ih =>
      cases b <;>
        simp [oddCount, bitNat] at ih ⊢ <;>
        omega

namespace MinimalActualABObstructionPacket

/--
actual terminal-top predecessor の position は terminal rank `c-1` 以上。
predecessor の left context に含まれる odd 数がその length を越えないことだけを使う。
-/
theorem terminalTopCellPosition_ge_terminalRank
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    (M.toPureBProfileObstruction hL).terminalCriticalStart - 1 ≤
      (M.toPureBProfileObstruction hL).terminalTopCellPosition := by
  obtain ⟨lower, S, hLowerFP, hPos, hLeft, hOdd⟩ :=
    M.exists_terminalTopCellActualPredecessor_of_positive_criticalization
      hL hStart
  have hCount :
      oddCount S.edge.leftContext ≤ S.edge.leftContext.length :=
    cstOddCount_le_length S.edge.leftContext
  unfold AdjacentFerrersSwap.fareyLeftExponent at hLeft
  unfold AdjacentFerrersSwap.position at hPos
  omega

end MinimalActualABObstructionPacket

namespace AttachedTwoCornerPacket

/--
attached straight suffix では start depth は任意の occupied offset の depth 以下。
各 internal step が depth を据え置くか `+1` することだけを使う。
-/
private theorem straightStart_depth_le_offset
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    P.h A.straightHenselStart ≤
      P.h (A.straightHenselStart + i) := by
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
      have hkC : k + 1 < P.terminalCriticalStart := by
        dsimp [k]
        omega
      have hStep :=
        A.internal_depth_succ_eq_self_or_add_one hPrev hkC
      have hLe : P.h k ≤ P.h (k + 1) := by
        rcases hStep with hEq | hEq
        · rw [hEq]
        · rw [hEq]
          omega
      have hIdx :
          A.straightHenselStart + (i + 1) = k + 1 := by
        dsimp [k]
        omega
      rw [hIdx]
      exact le_trans hIH hLe

/--
attached straight suffix の profile checkpoint は一列ごとに exact に `+1`。
したがって offset `i` の checkpoint は start checkpoint `+ i` になる。
-/
private theorem straight_profileCheckpoint_eq_start_add
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
terminal Farey tail depth を整数差で exact に書き直す。

`s = straightHenselStart`, `W = straightHenselWidth` とすると

  H - terminalTopCellPosition
    = beta(m) - beta(s) - W + h(s) + 2

が `ℤ` 上で exact に成り立つ。
Nat の途中減算を避けることで high start-depth の寄与 `+ h(s)` をそのまま残す。
-/
theorem terminalFareyTailDepth_int_eq_beattyGap_sub_width_add_startDepth
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P) :
    (P.H : ℤ) - (P.terminalTopCellPosition : ℤ) =
      (beattyIndex P.m : ℤ) -
        (beattyIndex A.straightHenselStart : ℤ) -
        (A.straightHenselWidth : ℤ) +
        (P.h A.straightHenselStart : ℤ) + 2 := by
  have hWidthPos := A.straightHenselWidth_pos
  have hi :
      A.straightHenselWidth - 1 < A.straightHenselWidth := by
    omega
  have hCheckpoint :=
    A.straight_profileCheckpoint_eq_start_add
      (i := A.straightHenselWidth - 1) hi
  have hEnd := A.straightHenselStart_add_width
  have hPredIdx :
      A.straightHenselStart + (A.straightHenselWidth - 1) =
        P.terminalCriticalStart - 1 := by
    omega
  rw [hPredIdx] at hCheckpoint
  have hPosition :
      P.terminalTopCellPosition =
        profileCheckpoint P.h A.straightHenselStart +
          (A.straightHenselWidth - 1) := by
    change
      profileCheckpoint P.h (P.terminalCriticalStart - 1) =
        profileCheckpoint P.h A.straightHenselStart +
          (A.straightHenselWidth - 1)
    exact hCheckpoint
  have hsM : A.straightHenselStart < P.m := by
    have hcM := P.terminalCriticalStart_spec.1
    have hsC := A.straightHenselStart_lt_terminalCriticalStart
    omega
  have hsDepth :
      P.h A.straightHenselStart ≤
        beattyIndex A.straightHenselStart :=
    P.admissible.depth_le hsM
  have hPositionNat :
      P.terminalTopCellPosition =
        beattyIndex A.straightHenselStart -
            P.h A.straightHenselStart +
          (A.straightHenselWidth - 1) := by
    simpa [profileCheckpoint] using hPosition
  have hPositionZ :=
    congrArg (fun n : ℕ => (n : ℤ)) hPositionNat
  have hOneLeWidth : 1 ≤ A.straightHenselWidth := by
    omega
  simp only [Nat.cast_add] at hPositionZ
  rw [Nat.cast_sub hsDepth, Nat.cast_sub hOneLeWidth] at hPositionZ
  push_cast at hPositionZ
  have hHZ :=
    congrArg (fun n : ℕ => (n : ℤ)) P.terminal_beatty
  push_cast at hHZ
  rw [hHZ, hPositionZ]
  ring

/--
attached straight Hensel start の depth は terminal-top Beatty slack 以下。

  h(s) ≤ beta(c-1) - (c-1)

ここで `s = straightHenselStart`, `c = terminalCriticalStart`。
straight suffix の depth monotonicity と actual terminal-top position の rank lower bound を繋ぐ。
-/
theorem straightHenselStart_depth_le_terminalTopSlack
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (A : AttachedTwoCornerPacket (M.toPureBProfileObstruction hL))
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    let P := M.toPureBProfileObstruction hL
    P.h A.straightHenselStart ≤
      beattyIndex (P.terminalCriticalStart - 1) -
        (P.terminalCriticalStart - 1) := by
  let P := M.toPureBProfileObstruction hL
  let k := P.terminalCriticalStart - 1
  have hWidthPos := A.straightHenselWidth_pos
  have hi :
      A.straightHenselWidth - 1 < A.straightHenselWidth := by
    omega
  have hMono :=
    A.straightStart_depth_le_offset
      (i := A.straightHenselWidth - 1) hi
  have hEnd := A.straightHenselStart_add_width
  have hPredIdx :
      A.straightHenselStart + (A.straightHenselWidth - 1) = k := by
    dsimp [k, P]
    omega
  rw [hPredIdx] at hMono
  have hRank :=
    MinimalActualABObstructionPacket.terminalTopCellPosition_ge_terminalRank M hL hStart
  have hRankP : k ≤ P.terminalTopCellPosition := by
    simpa [P, k] using hRank
  have hcM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hcPos : 0 < P.terminalCriticalStart :=
    A.terminalCriticalStart_pos
  have hkM : k < P.m := by
    dsimp [k]
    omega
  have hDepthK : P.h k ≤ beattyIndex k :=
    P.admissible.depth_le hkM
  have hPositionEq :
      P.terminalTopCellPosition = beattyIndex k - P.h k := by
    simp [
      PureBProfileObstruction.terminalTopCellPosition,
      PureBProfileObstruction.terminalTopColumn,
      k
    ]
  rw [hPositionEq] at hRankP
  have hTerminalSlack :
      P.h k ≤ beattyIndex k - k := by
    omega
  exact le_trans hMono hTerminalSlack

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
