import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedTerminalComponentRigidity

/-!
# MultiCorner: restarted terminal geometry packet

既存 `RestartedTerminalStraightPacket` は Case I 用に

  criticalizationStart ≤ previous

を field として持つ。しかし、restarted terminal component の幾何そのもの、すなわち

* `previous + 1 < b`,
* `(previous,b)` の depth は zero,
* `[b,c)` の support は positive,
* `h(b)=1`,
* terminal component interior の `profileRunGap = 1`,
* checkpoint は slope-one の直線、

にはこの Case I 条件は不要である。

このファイルではその部分だけを独立 packet に切り出す。
後段の hard Case II `previous < criticalizationStart` でも同じ geometry を再利用できる。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
restarted terminal component の純粋な幾何 packet。

Case I / Case II の criticalization の位置関係は一切持たない。
-/
structure RestartedTerminalGeometryPacket
    (P : PureBProfileObstruction)
    (N : LastTwoExposedNormalForm P) where
  /-- last exposed predecessor は geometric terminal start の直前。 -/
  terminal_eq : N.terminal = P.terminalCriticalStart - 1
  /-- terminal start は正。 -/
  terminalCriticalStart_pos : 0 < P.terminalCriticalStart
  /-- previous exposed の直後で一度 depth が zero へ落ちる。 -/
  restart_zero : P.h (N.previous + 1) = 0

namespace RestartedTerminalGeometryPacket

/-- previous の右で最初に depth が再び正になる index。 -/
noncomputable def b
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (_S : RestartedTerminalGeometryPacket P N) : ℕ :=
  restartedComponentStart N

/-- restarted terminal component の幅 `c-b`。 -/
noncomputable def width
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) : ℕ :=
  P.terminalCriticalStart - S.b

/-- restart の前には最低一列の zero gap がある。 -/
theorem previous_succ_lt_b
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    N.previous + 1 < S.b := by
  simpa [b] using
    N.previous_succ_lt_restartedComponentStart S.restart_zero

/-- restarted start は terminal critical start より strict に左。 -/
theorem b_lt_terminalCriticalStart
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    S.b < P.terminalCriticalStart := by
  have hSpec := N.restartedComponentStart_spec
  rw [S.terminal_eq] at hSpec
  dsimp [b]
  omega

/-- restarted component の幅は正。 -/
theorem width_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    0 < S.width := by
  unfold width
  exact Nat.sub_pos_iff_lt.mpr S.b_lt_terminalCriticalStart

/-- `(previous,b)` は exact に zero-depth。 -/
theorem zero_between_previous_and_b
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    {k : ℕ}
    (hak : N.previous < k)
    (hkb : k < S.b) :
    P.h k = 0 := by
  simpa [b] using
    N.depth_eq_zero_between_previous_and_restart hak hkb

/-- `[b,c)` では depth は常に正。 -/
theorem support_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    {k : ℕ}
    (hbk : S.b ≤ k)
    (hkc : k < P.terminalCriticalStart) :
    0 < P.h k := by
  have hkt : k ≤ N.terminal := by
    rw [S.terminal_eq]
    omega
  simpa [b] using N.restarted_support_pos hbk hkt

/-- restart entrance の depth は exact に `1`。 -/
theorem h_b_eq_one
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    P.h S.b = 1 := by
  have hbLtC := S.b_lt_terminalCriticalStart
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hbM : S.b < P.m := lt_of_lt_of_le hbLtC hcLeM
  have hbPos : 0 < S.b := by
    have hGap := S.previous_succ_lt_b
    omega
  have hPrevZero : P.h (S.b - 1) = 0 := by
    apply S.zero_between_previous_and_b
    · have hGap := S.previous_succ_lt_b
      omega
    · omega
  have hbOneLe : 1 ≤ S.b := Nat.succ_le_iff.mpr hbPos
  have hIdx : (S.b - 1) + 1 < P.m := by
    rw [Nat.sub_add_cancel hbOneLe]
    exact hbM
  have hStep :=
    P.admissible.next_depth_le_add_one (k := S.b - 1) hIdx
  have hStep' : P.h S.b ≤ 1 := by
    simpa [Nat.sub_add_cancel hbOneLe, hPrevZero] using hStep
  have hPos : 0 < P.h S.b :=
    S.support_pos le_rfl hbLtC
  omega

/-- terminal component interior の run-gap はすべて `1`。 -/
theorem interior_runGap_eq_one
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    {k : ℕ}
    (hbk : S.b ≤ k)
    (hk1c : k + 1 < P.terminalCriticalStart) :
    P.profileRunGap k = 1 := by
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hkM : k < P.m := by omega
  have hk1M : k + 1 < P.m := by omega
  have hkPos : 0 < P.h k :=
    S.support_pos hbk (by omega)
  have hGapEq := P.profileRunGap_of_succ_lt hk1M
  have hStrict := P.admissible.checkpoint_strict hk1M
  have hGapPos : 0 < P.profileRunGap k := by
    rw [hGapEq]
    exact Nat.sub_pos_of_lt hStrict
  by_contra hne
  have hGapTwo : 2 ≤ P.profileRunGap k := by omega
  have hExp : P.IsExposedPredecessorIndex k :=
    ⟨hkM, hkPos, hGapTwo⟩
  have hak : N.previous < k := by
    have hab := N.restartedComponentStart_spec.1
    change N.previous < restartedComponentStart N at hab
    simpa [b] using lt_of_lt_of_le hab hbk
  have hkt : k < N.terminal := by
    rw [S.terminal_eq]
    omega
  exact N.no_exposed_between k hak hkt
    ((P.mem_exposedPredecessorSet_iff).2 hExp)

/--
restart から terminal まで checkpoint は slope-one の直線になる。

  checkpoint(b+n) = beta(b)-1+n.
-/
theorem checkpoint_offset
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    {n : ℕ}
    (hbn : S.b + n < P.terminalCriticalStart) :
    profileCheckpoint P.h (S.b + n) =
      beattyIndex S.b - 1 + n := by
  induction n with
  | zero =>
      change profileCheckpoint P.h S.b = beattyIndex S.b - 1
      unfold profileCheckpoint
      rw [S.h_b_eq_one]
  | succ n ih =>
      have hPrevC : S.b + n < P.terminalCriticalStart := by omega
      have hIH := ih hPrevC
      have hGapOne : P.profileRunGap (S.b + n) = 1 := by
        apply S.interior_runGap_eq_one
        · omega
        · simpa [Nat.add_assoc] using hbn
      have hcLeM : P.terminalCriticalStart ≤ P.m :=
        P.terminalCriticalStart_spec.1
      have hSuccM : S.b + n + 1 < P.m := by omega
      have hGapEq := P.profileRunGap_of_succ_lt hSuccM
      rw [hGapEq] at hGapOne
      have hStrict := P.admissible.checkpoint_strict hSuccM
      have hNext :
          profileCheckpoint P.h (S.b + n + 1) =
            profileCheckpoint P.h (S.b + n) + 1 := by
        omega
      change
        profileCheckpoint P.h (S.b + (n + 1)) =
          beattyIndex S.b - 1 + (n + 1)
      rw [← Nat.add_assoc, hNext, hIH]
      omega

/-- terminal component 全体で使う checkpoint line。 -/
theorem checkpoint_line
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N)
    {k : ℕ}
    (hbk : S.b ≤ k)
    (hkc : k < P.terminalCriticalStart) :
    profileCheckpoint P.h k =
      beattyIndex S.b - 1 + (k - S.b) := by
  have hEq : S.b + (k - S.b) = k := Nat.add_sub_of_le hbk
  have h := S.checkpoint_offset (n := k - S.b) (by simpa [hEq] using hkc)
  simpa [hEq] using h

/-- restart entrance では `beta(b)>0`。 -/
theorem beattyIndex_b_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    0 < beattyIndex S.b := by
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hbM : S.b < P.m := lt_of_lt_of_le S.b_lt_terminalCriticalStart hcLeM
  have hDepth := P.admissible.depth_le hbM
  rw [S.h_b_eq_one] at hDepth
  omega

/-- terminal start は `b + width`。 -/
theorem terminalCriticalStart_eq_b_add_width
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalGeometryPacket P N) :
    P.terminalCriticalStart = S.b + S.width := by
  unfold width
  exact
    (Nat.add_sub_of_le
      (Nat.le_of_lt S.b_lt_terminalCriticalStart)).symm

end RestartedTerminalGeometryPacket

end MultiCorner
end CSTMicro
end Collatz2
