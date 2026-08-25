import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBPositiveComponentEndpoint

/-!
# Pure B: single exposed corner rigidity

actual minimal B で exposed predecessor set が一個だけなら、terminal cut `c-1` が既に
exposed なので、それが唯一の exposed index である。

positive support の各 connected component の右端は exposed だから、positive support は
一つの interval `[b,c)` に限られる。さらに interior で `e_k>=2` は新しい exposed cut を
作るため、全 interior run は exact に `e_k=1`。

入口では直前の depth が zero なので admissibility の one-step bound から `h(b)=1`。
従って checkpoints は

  p_k = beta(b)-1 + (k-b),  b <= k < c

という一本の等差列に固定される。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-- single exposed branch で得る interval rigidity packet。 -/
structure SingleExposedCornerRigidityPacket
    (P : PureBProfileObstruction) where
  b : ℕ
  b_lt_c : b < P.terminalCriticalStart
  h_b_eq_one : P.h b = 1

  support_iff :
    ∀ k : ℕ, k < P.m →
      (0 < P.h k ↔ b ≤ k ∧ k < P.terminalCriticalStart)

  interior_runGap_eq_one :
    ∀ k : ℕ,
      b ≤ k →
      k + 1 < P.terminalCriticalStart →
      P.profileRunGap k = 1

  checkpoint_line :
    ∀ k : ℕ,
      b ≤ k →
      k < P.terminalCriticalStart →
      profileCheckpoint P.h k =
        beattyIndex b - 1 + (k - b)

namespace SingleExposedCornerRigidityPacket

/-- packet 内では positive support は exactly `[b,c)`。 -/
theorem depth_pos
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {k : ℕ}
    (hkM : k < P.m)
    (hbk : S.b ≤ k)
    (hkc : k < P.terminalCriticalStart) :
    0 < P.h k :=
  (S.support_iff k hkM).2 ⟨hbk, hkc⟩

/-- interval 外では depth は zero。 -/
theorem depth_eq_zero_of_outside
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    {k : ℕ}
    (hkM : k < P.m)
    (hout : k < S.b ∨ P.terminalCriticalStart ≤ k) :
    P.h k = 0 := by
  by_contra hne
  have hPos : 0 < P.h k := Nat.pos_of_ne_zero hne
  have hIn := (S.support_iff k hkM).1 hPos
  rcases hout with hkb | hck
  · omega
  · omega

end SingleExposedCornerRigidityPacket

end PureBProfileObstruction

namespace MinimalActualABObstructionPacket

/--
actual minimal B では terminal critical start は正。
-/
private theorem actualTerminalCriticalStart_pos
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    0 <
      (M.toPureBProfileObstruction hL).terminalCriticalStart := by
  let P := M.toPureBProfileObstruction hL
  have hStart :
      0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  have hLe :
      P.criticalizationStart ≤
        P.terminalCriticalStart :=
    P.criticalizationStart_le_terminalCriticalStart
  exact lt_of_lt_of_le hStart hLe


/--
`|E(B)| = 1` なら、任意の exposed predecessor は
terminal predecessor `c - 1` に一致する。

`Finset.card_eq_one` の existential elimination は
Prop を返すこの theorem 内に閉じ込める。
-/
private theorem exposedPredecessor_eq_terminalPred_of_card_one
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    {k : ℕ}
    (hk :
      (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex k) :
    k =
      (M.toPureBProfileObstruction hL).terminalCriticalStart - 1 := by
  let P := M.toPureBProfileObstruction hL
  have hCardP :
      P.exposedPredecessorSet.card = 1 := by
    simpa [P] using hCard
  have htExposed :
      P.IsExposedPredecessorIndex
        (P.terminalCriticalStart - 1) := by
    simpa [P] using
      M.terminalPred_isExposed R hL
  have hkMem :
      k ∈ P.exposedPredecessorSet :=
    P.mem_exposedPredecessorSet_iff.mpr
      (by simpa [P] using hk)
  have htMem :
      P.terminalCriticalStart - 1 ∈
        P.exposedPredecessorSet :=
    P.mem_exposedPredecessorSet_iff.mpr htExposed
  obtain ⟨u, hu⟩ :=
    Finset.card_eq_one.mp hCardP
  rw [hu] at hkMem htMem
  have hku : k = u := by
    simpa using hkMem
  have htu :
      P.terminalCriticalStart - 1 = u := by
    simpa using htMem
  exact hku.trans htu.symm


/--
terminal predecessor `c - 1` は、
`c` より前にある positive-depth index を一つ与える。
-/
private theorem exists_positive_before_terminalCriticalStart
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    ∃ k : ℕ,
      k <
          (M.toPureBProfileObstruction hL).terminalCriticalStart ∧
        0 <
          (M.toPureBProfileObstruction hL).h k := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let t := c - 1
  have hcPos :
      0 < c := by
    simpa [P, c] using
      actualTerminalCriticalStart_pos R M hL
  have htPos :
      0 < P.h t := by
    have h :=
      P.terminalLastDepth_pos hcPos
    simpa [t, c] using h
  have htLtC :
      t < c := by
    dsimp [t]
    omega
  exact ⟨t, htLtC, htPos⟩


/--
terminal critical interval の前で最初に depth が正になる index。
-/
private noncomputable def singleExposedCornerStart
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) : ℕ :=
  Nat.find
    (exists_positive_before_terminalCriticalStart
      R M hL)


/--
canonical start `b` は `b < c` かつ `h b > 0`。
-/
private theorem singleExposedCornerStart_spec
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    singleExposedCornerStart R M hL <
        (M.toPureBProfileObstruction hL).terminalCriticalStart ∧
      0 <
        (M.toPureBProfileObstruction hL).h
          (singleExposedCornerStart R M hL) := by
  simpa [singleExposedCornerStart] using
    Nat.find_spec
      (exists_positive_before_terminalCriticalStart
        R M hL)


/--
canonical start `b` より前では depth はすべて 0。
-/
private theorem singleExposedCornerStart_before_zero
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (hk :
      k < singleExposedCornerStart R M hL) :
    (M.toPureBProfileObstruction hL).h k = 0 := by
  let P := M.toPureBProfileObstruction hL
  let b := singleExposedCornerStart R M hL
  have hbSpec :
      b < P.terminalCriticalStart ∧
        0 < P.h b := by
    simpa [P, b] using
      singleExposedCornerStart_spec R M hL
  by_contra hne
  have hkPos :
      0 < P.h k :=
    Nat.pos_of_ne_zero hne
  have hkC :
      k < P.terminalCriticalStart :=
    lt_trans
      (by simpa [b] using hk)
      hbSpec.1
  have hCandidate :
      k < P.terminalCriticalStart ∧
        0 < P.h k :=
    ⟨hkC, hkPos⟩
  have hMin :
      b ≤ k := by
    have h :=
      Nat.find_min'
        (exists_positive_before_terminalCriticalStart
          R M hL)
        hCandidate
    simpa [b, singleExposedCornerStart] using h
  have hkb :
      k < b := by
    simpa [b] using hk
  omega


/--
`|E(B)| = 1` なら canonical start `b` から terminal start `c`
まで depth は途切れず正。
-/
private theorem singleExposedCorner_support_pos
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    {k : ℕ}
    (hbk :
      singleExposedCornerStart R M hL ≤ k)
    (hkc :
      k <
        (M.toPureBProfileObstruction hL).terminalCriticalStart) :
    0 <
      (M.toPureBProfileObstruction hL).h k := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let b := singleExposedCornerStart R M hL
  have hbSpec :
      b < c ∧ 0 < P.h b := by
    simpa [P, c, b] using
      singleExposedCornerStart_spec R M hL
  have hcLeM :
      c ≤ P.m := by
    simpa [c] using
      P.terminalCriticalStart_spec.1
  have hPosOffset :
      ∀ n : ℕ,
        b + n < c →
          0 < P.h (b + n) := by
    intro n
    induction n with
    | zero =>
        intro hbc
        simpa using hbSpec.2
    | succ n ih =>
        intro hSuccC
        have hPrevC :
            b + n < c := by
          omega
        have hPrevPos :
            0 < P.h (b + n) :=
          ih hPrevC
        by_contra hnot
        have hZero :
            P.h (b + n + 1) = 0 :=
          Nat.eq_zero_of_not_pos hnot
        have hSuccM :
            b + n + 1 < P.m :=
          lt_of_lt_of_le hSuccC hcLeM
        have hExp :
            P.IsExposedPredecessorIndex (b + n) :=
          P.positiveEndpoint_isExposed_of_succ_lt
            (k := b + n)
            hSuccM
            hPrevPos
            (by
              simpa [Nat.add_assoc] using hZero)
        have hEq :=
          exposedPredecessor_eq_terminalPred_of_card_one
            R M hL hCard hExp
        have hEq' :
            b + n = c - 1 := by
          simpa [P, c] using hEq
        omega
  have hEq :
      b + (k - b) = k :=
    Nat.add_sub_of_le
      (by simpa [b] using hbk)
  have h :=
    hPosOffset
      (k - b)
      (by
        simpa [P, c, b, hEq] using hkc)
  simpa [P, b, hEq] using h


/--
canonical start `b` の depth はちょうど 1。
-/
private theorem singleExposedCornerStart_depth_eq_one
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).h
        (singleExposedCornerStart R M hL) = 1 := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let b := singleExposedCornerStart R M hL
  have hbSpec :
      b < c ∧ 0 < P.h b := by
    simpa [P, c, b] using
      singleExposedCornerStart_spec R M hL
  have hcLeM :
      c ≤ P.m := by
    simpa [c] using
      P.terminalCriticalStart_spec.1
  have hbLtM :
      b < P.m :=
    lt_of_lt_of_le hbSpec.1 hcLeM
  have hBefore :
      ∀ k : ℕ, k < b → P.h k = 0 := by
    intro k hk
    exact
      singleExposedCornerStart_before_zero
        R M hL
        (by simpa [b] using hk)
  have hbOne :=
    P.admissible.firstPositiveDepth_eq_one
      hbLtM hbSpec.2 hBefore
  simpa [P, b] using hbOne


/--
`|E(B)| = 1` なら positive support は厳密に `[b,c)`。
-/
private theorem singleExposedCorner_support_iff
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    {k : ℕ}
    (hkM :
      k < (M.toPureBProfileObstruction hL).m) :
    (0 < (M.toPureBProfileObstruction hL).h k ↔
      singleExposedCornerStart R M hL ≤ k ∧
        k <
          (M.toPureBProfileObstruction hL).terminalCriticalStart) := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let b := singleExposedCornerStart R M hL
  constructor
  · intro hkPos
    have hkc :
        k < c := by
      by_contra hnot
      have hck :
          c ≤ k := by
        omega
      have hZero :
          P.h k = 0 :=
        P.terminalCriticalStart_spec.2
          k hck
          (by simpa [P] using hkM)
      rw [hZero] at hkPos
      omega
    have hbk :
        b ≤ k := by
      by_contra hnot
      have hkb :
          k < b := by
        omega
      have hZero :
          P.h k = 0 := by
        apply
          singleExposedCornerStart_before_zero
            R M hL
        simpa [b] using hkb
      rw [hZero] at hkPos
      omega
    exact
      ⟨by simpa [b] using hbk,
       by simpa [P, c] using hkc⟩
  · rintro ⟨hbk, hkc⟩
    exact
      singleExposedCorner_support_pos
        R M hL hCard
        (by simpa [b] using hbk)
        (by simpa [P, c] using hkc)


/--
support interval の interior では run-gap はすべて 1。
gap 2 以上なら新しい exposed predecessor が生じ、
cardinality-one と矛盾する。
-/
private theorem singleExposedCorner_interior_runGap_eq_one
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    {k : ℕ}
    (hbk :
      singleExposedCornerStart R M hL ≤ k)
    (hk1c :
      k + 1 <
        (M.toPureBProfileObstruction hL).terminalCriticalStart) :
    (M.toPureBProfileObstruction hL).profileRunGap k = 1 := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let b := singleExposedCornerStart R M hL
  have hcLeM :
      c ≤ P.m := by
    simpa [c] using
      P.terminalCriticalStart_spec.1
  have hkC :
      k < c := by
    have :
        k < k + 1 :=
      Nat.lt_succ_self k
    exact lt_trans this
      (by simpa [P, c] using hk1c)
  have hkM :
      k < P.m :=
    lt_of_lt_of_le hkC hcLeM
  have hk1M :
      k + 1 < P.m :=
    lt_of_lt_of_le
      (by simpa [P, c] using hk1c)
      hcLeM
  have hkPos :
      0 < P.h k :=
    singleExposedCorner_support_pos
      R M hL hCard
      (by simpa [b] using hbk)
      hkC
  have hStrict :=
    P.admissible.checkpoint_strict hk1M
  have hGapEq :=
    P.profileRunGap_of_succ_lt hk1M
  have hGapPos :
      0 < P.profileRunGap k := by
    rw [hGapEq]
    exact Nat.sub_pos_of_lt hStrict
  by_contra hne
  have hGapTwo :
      2 ≤ P.profileRunGap k := by
    have hOneLe :
        1 ≤ P.profileRunGap k :=
      Nat.succ_le_iff.mpr hGapPos
    have hOneNe :
        1 ≠ P.profileRunGap k :=
      Ne.symm hne
    have hOneLt :
        1 < P.profileRunGap k :=
      lt_of_le_of_ne hOneLe hOneNe
    exact Nat.succ_le_iff.mpr hOneLt
  have hExp :
      P.IsExposedPredecessorIndex k :=
    ⟨hkM, hkPos, hGapTwo⟩
  have hEq :=
    exposedPredecessor_eq_terminalPred_of_card_one
      R M hL hCard hExp
  have hEq' :
      k = c - 1 := by
    simpa [P, c] using hEq
  have hk1c' :
      k + 1 < c := by
    simpa [P, c] using hk1c
  omega


/--
canonical start から `n` 個進んだ checkpoint は
`beattyIndex b - 1 + n`。
-/
private theorem singleExposedCorner_checkpoint_offset
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    {n : ℕ}
    (hbn :
      singleExposedCornerStart R M hL + n <
        (M.toPureBProfileObstruction hL).terminalCriticalStart) :
    profileCheckpoint
        (M.toPureBProfileObstruction hL).h
        (singleExposedCornerStart R M hL + n) =
      beattyIndex (singleExposedCornerStart R M hL) - 1 + n := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let b := singleExposedCornerStart R M hL
  have hcLeM :
      c ≤ P.m := by
    simpa [c] using
      P.terminalCriticalStart_spec.1
  have hbOne :
      P.h b = 1 := by
    simpa [P, b] using
      singleExposedCornerStart_depth_eq_one
        R M hL
  induction n with
  | zero =>
      change
        profileCheckpoint P.h b =
          beattyIndex b - 1
      unfold profileCheckpoint
      rw [hbOne]
  | succ n ih =>
      have hSuccC :
          b + n + 1 < c := by
        simpa [P, c, b, Nat.add_assoc] using hbn
      have hPrevC :
          b + n < c := by
        omega
      have hIH :
          profileCheckpoint P.h (b + n) =
            beattyIndex b - 1 + n := by
        apply ih
        simpa [P, c, b] using hPrevC
      have hGapOne :
          P.profileRunGap (b + n) = 1 := by
        apply
          singleExposedCorner_interior_runGap_eq_one
            R M hL hCard
        · simp only [le_add_iff_nonneg_right, zero_le, b]
        · simpa [P, c, b, Nat.add_assoc] using hSuccC
      have hSuccM :
          b + n + 1 < P.m :=
        lt_of_lt_of_le hSuccC hcLeM
      have hGapEq :=
        P.profileRunGap_of_succ_lt hSuccM
      rw [hGapEq] at hGapOne
      have hStrict :=
        P.admissible.checkpoint_strict hSuccM
      have hNext :
          profileCheckpoint P.h (b + n + 1) =
            profileCheckpoint P.h (b + n) + 1 := by
        omega
      change
        profileCheckpoint P.h (b + (n + 1)) =
          beattyIndex b - 1 + (n + 1)
      rw [← Nat.add_assoc, hNext, hIH]
      omega


/--
support interval 全体で checkpoint は一本の affine line。
-/
private theorem singleExposedCorner_checkpoint_line
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    {k : ℕ}
    (hbk :
      singleExposedCornerStart R M hL ≤ k)
    (hkc :
      k <
        (M.toPureBProfileObstruction hL).terminalCriticalStart) :
    profileCheckpoint
        (M.toPureBProfileObstruction hL).h k =
      beattyIndex (singleExposedCornerStart R M hL) - 1 +
        (k - singleExposedCornerStart R M hL) := by
  let P := M.toPureBProfileObstruction hL
  let b := singleExposedCornerStart R M hL
  have hEq :
      b + (k - b) = k :=
    Nat.add_sub_of_le
      (by simpa [b] using hbk)
  have h :=
    singleExposedCorner_checkpoint_offset
      R M hL hCard
      (n := k - b)
      (by
        simpa [P, b, hEq] using hkc)
  simpa [P, b, hEq] using h


/--
`|E(B)|=1` から single shifted interval geometry を canonical に抽出する。
-/
noncomputable def toSingleExposedCornerRigidityPacket
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1) :
    (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket := by
  let P := M.toPureBProfileObstruction hL
  let b := singleExposedCornerStart R M hL
  refine {
    b := b

    b_lt_c := ?_

    h_b_eq_one := ?_

    support_iff := ?_

    interior_runGap_eq_one := ?_

    checkpoint_line := ?_
  }
  · have h :=
      singleExposedCornerStart_spec
        R M hL
    simpa [P, b] using h.1
  · simpa [P, b] using
      singleExposedCornerStart_depth_eq_one
        R M hL
  · intro k hkM
    simpa [P, b] using
      singleExposedCorner_support_iff
        R M hL hCard hkM
  · intro k hbk hk1c
    simpa [P, b] using
      singleExposedCorner_interior_runGap_eq_one
        R M hL hCard hbk hk1c
  · intro k hbk hkc
    simpa [P, b] using
      singleExposedCorner_checkpoint_line
        R M hL hCard hbk hkc



end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
