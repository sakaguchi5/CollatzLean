import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedBranchDivisibility
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerDefectRecurrence

/-!
# MultiCorner: restarted terminal component rigidity

previous exposed `a` の直後が zero である restarted subcase を、
terminal exposed `t=c-1` までの局所 geometry だけで正規化する。

`b` は `a` より右で最初に depth が再び正になる index。
定義の最小性と `no_exposed_between` から

* `a+1 < b`,
* `(a,b)` は zero,
* `[b,c)` は連続 positive,
* `h b = 1`,
* interior `profileRunGap = 1`,
* checkpoint は `beta(b)-1+(k-b)`

をすべて導く。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/-- previous より右には terminal exposed 自身が positive candidate として存在する。 -/
theorem exists_positive_after_previous
    {P : PureBProfileObstruction}
    (N : LastTwoExposedNormalForm P) :
    ∃ k : ℕ,
      N.previous < k ∧
      k ≤ N.terminal ∧
      0 < P.h k := by
  have E : P.IsExposedPredecessorIndex N.terminal :=
    (P.mem_exposedPredecessorSet_iff).1 N.terminal_mem
  exact ⟨N.terminal, N.previous_lt_terminal, le_rfl, E.depth_pos⟩

/-- previous の右で最初に再び positive になる index。 -/
noncomputable def restartedComponentStart
    {P : PureBProfileObstruction}
    (N : LastTwoExposedNormalForm P) : ℕ :=
  Nat.find (exists_positive_after_previous N)

namespace LastTwoExposedNormalForm

/-- canonical restarted start の基本 spec。 -/
theorem restartedComponentStart_spec
    {P : PureBProfileObstruction}
    (N : LastTwoExposedNormalForm P) :
    N.previous < restartedComponentStart N ∧
      restartedComponentStart N ≤ N.terminal ∧
      0 < P.h (restartedComponentStart N) := by
  simpa [restartedComponentStart] using
    Nat.find_spec (exists_positive_after_previous N)

/-- restarted 条件 `h(a+1)=0` なら positive restart まで最低一列 zero がある。 -/
theorem previous_succ_lt_restartedComponentStart
    {P : PureBProfileObstruction}
    (N : LastTwoExposedNormalForm P)
    (hRestart : P.h (N.previous + 1) = 0) :
    N.previous + 1 < restartedComponentStart N := by
  have hSpec := N.restartedComponentStart_spec
  by_contra hnot
  have hLe : restartedComponentStart N ≤ N.previous + 1 := by omega
  have hEq : restartedComponentStart N = N.previous + 1 := by omega
  have hPos : 0 < P.h (restartedComponentStart N) := hSpec.2.2
  rw [hEq, hRestart] at hPos
  omega

/-- `(a,b)` は exact に zero。 -/
theorem depth_eq_zero_between_previous_and_restart
    {P : PureBProfileObstruction}
    (N : LastTwoExposedNormalForm P)
    {k : ℕ}
    (hak : N.previous < k)
    (hkb : k < restartedComponentStart N) :
    P.h k = 0 := by
  by_contra hne
  have hPos : 0 < P.h k := Nat.pos_of_ne_zero hne
  have hSpec := N.restartedComponentStart_spec
  have hCandidate :
      N.previous < k ∧ k ≤ N.terminal ∧ 0 < P.h k := by
    constructor
    · exact hak
    · constructor
      · exact le_trans (Nat.le_of_lt hkb) hSpec.2.1
      · exact hPos
  have hMin : restartedComponentStart N ≤ k := by
    have h :=
      Nat.find_min' (exists_positive_after_previous N) hCandidate
    simpa [restartedComponentStart] using h
  omega

/-- restart 後は terminal exposed まで positive support が途切れない。 -/
theorem restarted_support_pos
    {P : PureBProfileObstruction}
    (N : LastTwoExposedNormalForm P)
    {k : ℕ}
    (hbk : restartedComponentStart N ≤ k)
    (hkt : k ≤ N.terminal) :
    0 < P.h k := by
  let b := restartedComponentStart N
  have hSpec := N.restartedComponentStart_spec
  have hPosOffset :
      ∀ n : ℕ,
        b + n ≤ N.terminal →
          0 < P.h (b + n) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa [b] using hSpec.2.2
    | succ n ih =>
        intro hSuccT
        have hPrevT : b + n < N.terminal := by omega
        have hPrevPos : 0 < P.h (b + n) :=
          ih (by omega)
        by_contra hnot
        have hZero : P.h (b + n + 1) = 0 :=
          Nat.eq_zero_of_not_pos hnot
        have Eterm : P.IsExposedPredecessorIndex N.terminal :=
          (P.mem_exposedPredecessorSet_iff).1 N.terminal_mem
        have hSuccM : b + n + 1 < P.m :=
          lt_of_le_of_lt hSuccT Eterm.lt_m
        have hExp : P.IsExposedPredecessorIndex (b + n) :=
          P.positiveEndpoint_isExposed_of_succ_lt
            hSuccM hPrevPos (by simpa [Nat.add_assoc] using hZero)
        have hPrevA : N.previous < b + n := by
          have hab : N.previous < b := by simpa [b] using hSpec.1
          omega
        have hNot :=
          N.no_exposed_between (b + n) hPrevA hPrevT
        exact hNot ((P.mem_exposedPredecessorSet_iff).2 hExp)
  have hEq : b + (k - b) = k := Nat.add_sub_of_le hbk
  have h := hPosOffset (k - b) (by simpa [hEq] using hkt)
  simpa [b, hEq] using h

end LastTwoExposedNormalForm

/--
restarted terminal straight component をまとめた packet。
`criticalization_le_previous` は Case I `s≤a` を明示する。
-/
structure RestartedTerminalStraightPacket
    (P : PureBProfileObstruction)
    (N : LastTwoExposedNormalForm P) where
  terminal_eq : N.terminal = P.terminalCriticalStart - 1
  terminalCriticalStart_pos : 0 < P.terminalCriticalStart
  criticalization_le_previous : P.criticalizationStart ≤ N.previous
  restart_zero : P.h (N.previous + 1) = 0

namespace RestartedTerminalStraightPacket

noncomputable def b
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (_S : RestartedTerminalStraightPacket P N) : ℕ :=
  restartedComponentStart N

noncomputable def width
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N) : ℕ :=
  P.terminalCriticalStart - S.b

/-- `a+1<b`。 -/
theorem previous_succ_lt_b
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N) :
    N.previous + 1 < S.b := by
  simpa [b] using
    N.previous_succ_lt_restartedComponentStart S.restart_zero

/-- `b<c`。 -/
theorem b_lt_terminalCriticalStart
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N) :
    S.b < P.terminalCriticalStart := by
  have hSpec := N.restartedComponentStart_spec
  rw [S.terminal_eq] at hSpec
  dsimp [b]
  omega

/-- width は正。 -/
theorem width_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N) :
    0 < S.width := by
  unfold width
  exact Nat.sub_pos_iff_lt.mpr S.b_lt_terminalCriticalStart

/-- `[a+1,b)` は zero。 -/
theorem zero_between_previous_and_b
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {k : ℕ}
    (hak : N.previous < k)
    (hkb : k < S.b) :
    P.h k = 0 := by
  simpa [b] using
    N.depth_eq_zero_between_previous_and_restart hak hkb

/-- `[b,c)` は positive。 -/
theorem support_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {k : ℕ}
    (hbk : S.b ≤ k)
    (hkc : k < P.terminalCriticalStart) :
    0 < P.h k := by
  have hkt : k ≤ N.terminal := by
    rw [S.terminal_eq]
    omega
  simpa [b] using N.restarted_support_pos hbk hkt

/-- restart entrance depth は exact 1。 -/
theorem h_b_eq_one
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N) :
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

/-- terminal component interior の run-gap は全て 1。 -/
theorem interior_runGap_eq_one
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
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

/-- support interval 上の checkpoint は一本の straight line。 -/
theorem checkpoint_offset
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
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

/-- support interval 全体の checkpoint line。 -/
theorem checkpoint_line
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    {k : ℕ}
    (hbk : S.b ≤ k)
    (hkc : k < P.terminalCriticalStart) :
    profileCheckpoint P.h k =
      beattyIndex S.b - 1 + (k - S.b) := by
  have hEq : S.b + (k - S.b) = k := Nat.add_sub_of_le hbk
  have h := S.checkpoint_offset (n := k - S.b) (by simpa [hEq] using hkc)
  simpa [hEq] using h

/-- `beta(b)>0`。 -/
theorem beattyIndex_b_pos
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N) :
    0 < beattyIndex S.b := by
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hbM : S.b < P.m := lt_of_lt_of_le S.b_lt_terminalCriticalStart hcLeM
  have hDepth := P.admissible.depth_le hbM
  rw [S.h_b_eq_one] at hDepth
  omega

/-- zero gap により `[a+1,c)` と `[b,c)` の tail は一致する。 -/
theorem tail_from_previous_succ_eq_tail_from_b
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N) :
    restartedClosedTailZ P (N.previous + 1) P.terminalCriticalStart =
      restartedClosedTailZ P S.b P.terminalCriticalStart := by
  apply restartedClosedTailZ_eq_of_zero_interval P
  · exact Nat.le_of_lt S.previous_succ_lt_b
  · exact Nat.le_of_lt S.b_lt_terminalCriticalStart
  · intro k huk hkb
    apply S.zero_between_previous_and_b
    · omega
    · exact hkb

/-- restarted geometry が local width より一段深い 3-adic divisibility を強制する。 -/
theorem tail_extra_threeAdic_dvd
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart) :
    (3 : ℤ) ^ (S.width + 1) ∣
      restartedClosedTailZ P S.b P.terminalCriticalStart := by
  have hCrit := S.criticalization_le_previous
  have hsk : P.criticalizationStart ≤ N.previous + 1 := by
    omega
  have hkc : N.previous + 1 ≤ P.terminalCriticalStart := by
    have hGap := S.previous_succ_lt_b
    have hbC := S.b_lt_terminalCriticalStart
    omega
  have hDeep :=
    restartedTail_localWidth_dvd P hStart hsk hkc
  have hEq := S.tail_from_previous_succ_eq_tail_from_b
  rw [hEq] at hDeep
  have hExpLe :
      S.width + 1 ≤ P.terminalCriticalStart - (N.previous + 1) := by
    unfold width
    have hGap := S.previous_succ_lt_b
    have hbC := S.b_lt_terminalCriticalStart
    omega
  have hPowDvd :
      (3 : ℤ) ^ (S.width + 1) ∣
        (3 : ℤ) ^ (P.terminalCriticalStart - (N.previous + 1)) :=
    threePow_dvd_threePow_of_le hExpLe
  exact dvd_trans hPowDvd hDeep

/-- terminal straight tail は既存 `singleCornerDefect` と exact に一致する。 -/
theorem tail_eq_singleCornerDefect
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N) :
    restartedClosedTailZ P S.b P.terminalCriticalStart =
      (singleCornerDefect S.b S.width : ℤ) := by
  let w := S.width
  have hcEq : P.terminalCriticalStart = S.b + w := by
    dsimp [w, width]
    exact (Nat.add_sub_of_le (Nat.le_of_lt S.b_lt_terminalCriticalStart)).symm
  have hMain :
      ∀ n : ℕ, n ≤ w →
        restartedClosedTailZ P S.b (S.b + n) =
          (singleCornerDefect S.b n : ℤ) := by
    intro n hn
    induction n with
    | zero =>
        simp [restartedClosedTailZ, singleCornerDefect]
    | succ n ih =>
        have hnlt : n < w := by omega
        have hPrev := ih (by omega)
        have hTailRec :=
          restartedClosedTailZ_succ P
            (b := S.b) (c := S.b + n) (by omega)
        have hIndex : S.b + n + 1 = S.b + (n + 1) := by omega
        rw [hIndex] at hTailRec
        rw [hTailRec, hPrev, singleCornerDefect_succ]
        have hNc : S.b + n < P.terminalCriticalStart := by
          rw [hcEq]
          omega
        have hLine := S.checkpoint_line (k := S.b + n) (by omega) hNc
        have hDiff : S.b + n - S.b = n := by omega
        have hCheckpoint :
            beattyIndex (S.b + n) - P.h (S.b + n) =
              beattyIndex S.b - 1 + n := by
          simpa [profileCheckpoint, hDiff] using hLine
        have hMassNat :
            profileRightmostColumnMass P.h (S.b + n) =
              2 ^ beattyIndex (S.b + n) -
                2 ^ (beattyIndex S.b - 1 + n) := by
          unfold profileRightmostColumnMass
          rw [hCheckpoint]
        rw [hMassNat]
        rw [Nat.cast_add, Nat.cast_mul]
        ring
  rw [hcEq]
  exact hMain w le_rfl

end RestartedTerminalStraightPacket

end MultiCorner
end CSTMicro
end Collatz2
