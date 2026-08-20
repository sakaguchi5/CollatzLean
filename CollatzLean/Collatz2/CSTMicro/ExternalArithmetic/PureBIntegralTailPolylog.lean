import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBFullDepthOriginExclusion
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalPolylog
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.RestrictedOstrowskiIntervals

/-!
# Pure B: maximal integral tail is one terminal polylog window

origin full-depth exclusion により、actual minimal B の arithmetic critical tail は
origin からは始まらない。一方その最左 start `ell = criticalizationStart` から terminal までは
critical recurrence が整数のまま通る。

このファイルでは既存 `PureBTerminalPolylog` の Xi / Christoffel / Rhin packing を、
幾何的 terminal suffix ではなく `IsIntegralCriticalTail` に対して再利用する。
その結果

  m - ell = O((log m)^210)

を得る。さらに `ell <= terminalCriticalStart` と origin exclusion を合わせると、

* arithmetic full-depth が初めて失敗する column `ell-1`,
* noncritical だが arithmetic critical な corridor `[ell, terminalCriticalStart)`,
* genuine terminal critical suffix,

が全部一つの terminal polylog window `[ell,m]` に入る。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-- integral-tail record start も同じ finite Xi candidate。 -/
theorem integralRecordStart_isBoundaryXiCandidate
    (P : PureBProfileObstruction)
    {a s r : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hend : s + r ≤ P.m)
    (B : CriticalRecordPiece s r) :
    BoundaryXiCandidate
      (beattyIndex r)
      (P.integralCriticalTailStateNat A hy s has (by omega)) := by
  let Zs := P.integralCriticalTailStateNat A hy s has (by omega : s ≤ P.m)
  have hTransport :=
    P.integralCriticalTailStateInt_interval_transport A has hend
  rw [B.intervalPhi_eq_prefixPhi] at hTransport
  have hStartCast :=
    P.integralCriticalTailStateNat_cast A hy has (by omega : s ≤ P.m)
  rw [← hStartCast] at hTransport
  have hQ := B.terminal_beatty_eq
  let Q := beattyIndex (s + r) - beattyIndex s
  have hEqQ : Q = beattyIndex r + 1 := by
    simpa [Q] using hQ
  have hDivPow :
      (2 : ℤ) ^ beattyIndex r ∣ (2 : ℤ) ^ Q := by
    rw [hEqQ]
    refine ⟨2, ?_⟩
    rw [pow_succ]
  have hDiv :
      (2 : ℤ) ^ beattyIndex r ∣
        (3 : ℤ) ^ r * (Zs : ℤ) + criticalPrefixPhiZ r := by
    rw [← hTransport]
    exact dvd_mul_of_dvd_left hDivPow _
  have hCastEq := natCast_eq_criticalXi_of_threePow_add_phi_dvd hDiv
  refine ⟨r, rfl, ?_⟩
  have hVal := congrArg ZMod.val hCastEq
  simpa [ZMod.val_natCast] using hVal

/-- integral-tail final no-carry fragment start も同じ Xi candidate。 -/
theorem integralNoCarryStart_isBoundaryXiCandidate
    (P : PureBProfileObstruction)
    {a s r : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hend : s + r ≤ P.m)
    (F : CriticalNoCarryFragment s r) :
    BoundaryXiCandidate
      (beattyIndex r)
      (P.integralCriticalTailStateNat A hy s has (by omega)) := by
  let Zs := P.integralCriticalTailStateNat A hy s has (by omega : s ≤ P.m)
  have hTransport :=
    P.integralCriticalTailStateInt_interval_transport A has hend
  rw [F.intervalPhi_eq_prefixPhi] at hTransport
  have hStartCast :=
    P.integralCriticalTailStateNat_cast A hy has (by omega : s ≤ P.m)
  rw [← hStartCast] at hTransport
  have hQ := F.terminal_beatty_eq
  have hDiv :
      (2 : ℤ) ^ beattyIndex r ∣
        (3 : ℤ) ^ r * (Zs : ℤ) + criticalPrefixPhiZ r := by
    rw [← hTransport, hQ]
    refine ⟨_, rfl⟩
  have hCastEq := natCast_eq_criticalXi_of_threePow_add_phi_dvd hDiv
  refine ⟨r, rfl, ?_⟩
  have hVal := congrArg ZMod.val hCastEq
  simpa [ZMod.val_natCast] using hVal

/-- `m+1<=2^ell` なら integral-tail state も terminal state と同じ dyadic size bound。 -/
theorem integralCriticalTailStateNat_succ_le_dyadic
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {a s ell : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hsm : s ≤ P.m)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    P.integralCriticalTailStateNat A hy s has hsm + 1 ≤
      2 ^ (20 + 15 * ell) := by
  have hState := P.integralCriticalTailStateNat_le_four_yNat A hy has hsm
  have hyBound := P.yNat_le_rhinPolynomial R hy
  have hPow : (P.m + 1) ^ 15 ≤ (2 ^ ell) ^ 15 :=
    Nat.pow_le_pow_left hmSize 15
  have hCore :
      P.integralCriticalTailStateNat A hy s has hsm ≤
        4 * rhinGapK * (2 ^ ell) ^ 15 := by
    calc
      P.integralCriticalTailStateNat A hy s has hsm
          ≤ 4 * P.yNat := hState
      _ ≤ 4 * (rhinGapK * (P.m + 1) ^ 15) :=
        Nat.mul_le_mul_left 4 hyBound
      _ ≤ 4 * rhinGapK * (2 ^ ell) ^ 15 := by
        nlinarith
  have hPowerEq :
      4 * rhinGapK * (2 ^ ell) ^ 15 =
        2 ^ (16 + 15 * ell) := by
    unfold rhinGapK
    norm_num
    rw [← pow_mul]
    have hMul : ell * 15 = 15 * ell := by omega
    rw [hMul, pow_add]
    ring
  rw [hPowerEq] at hCore
  have hSucc :
      P.integralCriticalTailStateNat A hy s has hsm + 1 ≤
        2 * 2 ^ (16 + 15 * ell) := by
    have hPos : 0 < 2 ^ (16 + 15 * ell) := by positivity
    omega
  calc
    P.integralCriticalTailStateNat A hy s has hsm + 1
        ≤ 2 * 2 ^ (16 + 15 * ell) := hSucc
    _ = 2 ^ (17 + 15 * ell) := by
      have hExp : 17 + 15 * ell = (16 + 15 * ell) + 1 := by omega
      rw [hExp, pow_succ]
      ring
    _ ≤ 2 ^ (20 + 15 * ell) :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)

/-- one integral-tail first-carry record の degree-14 length bound。 -/
theorem integralRecordPiece_length_le
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {a s r ell : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hend : s + r ≤ P.m)
    (B : CriticalRecordPiece s r)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    r ≤ terminalRecordLengthBound ell := by
  let x := P.integralCriticalTailStateNat A hy s has (by omega : s ≤ P.m)
  have hxSize : x + 1 ≤ 2 ^ (20 + 15 * ell) := by
    simpa [x] using
      P.integralCriticalTailStateNat_succ_le_dyadic
        R A hy has (by omega) hmSize
  have hCandidate := P.integralRecordStart_isBoundaryXiCandidate A hy has hend B
  have hPrec := smallXiCandidate_precision_le R hxSize hCandidate
  have hre : r ≤ beattyIndex r := length_le_beattyIndex B.length_pos
  exact le_trans hre
    (le_trans hPrec (smallXiPrecisionBound_terminalSize_le_recordLengthBound ell))

/-- integral-tail final no-carry fragment も degree-14 length bound。 -/
theorem integralNoCarryFragment_length_le
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {a s r ell : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hend : s + r ≤ P.m)
    (F : CriticalNoCarryFragment s r)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    r ≤ terminalRecordLengthBound ell := by
  by_cases hr0 : r = 0
  · subst r
    omega
  · have hrPos : 0 < r := Nat.pos_of_ne_zero hr0
    let x := P.integralCriticalTailStateNat A hy s has (by omega : s ≤ P.m)
    have hxSize : x + 1 ≤ 2 ^ (20 + 15 * ell) := by
      simpa [x] using
        P.integralCriticalTailStateNat_succ_le_dyadic
          R A hy has (by omega) hmSize
    have hCandidate := P.integralNoCarryStart_isBoundaryXiCandidate A hy has hend F
    have hPrec := smallXiCandidate_precision_le R hxSize hCandidate
    have hre : r ≤ beattyIndex r := length_le_beattyIndex hrPos
    exact le_trans hre
      (le_trans hPrec (smallXiPrecisionBound_terminalSize_le_recordLengthBound ell))

/-- integral-tail chain 内の全 record / final fragment を一様 bound。 -/
theorem integralRecordChain_piece_bounds
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {a start remaining ell : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (C : CriticalRecordChain start remaining)
    (has : a ≤ start)
    (hend : start + remaining = P.m)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    (∀ r : ℕ, r ∈ C.recordLengths → r ≤ terminalRecordLengthBound ell) ∧
      C.finalLength ≤ terminalRecordLengthBound ell := by
  induction C with
  | @final start remaining fragment =>
      constructor
      · intro r hr
        simp [CriticalRecordChain.recordLengths] at hr
      · change remaining ≤ terminalRecordLengthBound ell
        have hEnd : start + remaining ≤ P.m := by omega
        exact
          P.integralNoCarryFragment_length_le
            R A hy has hEnd fragment hmSize
  | @step start remaining r hrPos hrLe piece tail ih =>
      have hPieceEnd : start + r ≤ P.m := by omega
      have hPiece :=
        P.integralRecordPiece_length_le
          R A hy has hPieceEnd piece hmSize
      have hTailStart : a ≤ start + r := by omega
      have hTailEnd : (start + r) + (remaining - r) = P.m := by omega
      have hTail := ih hTailStart hTailEnd
      constructor
      · intro u hu
        simp only [CriticalRecordChain.recordLengths, List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact hPiece
        · exact hTail.1 u hu
      · exact hTail.2

/--
main arithmetic-tail theorem, dyadic-size form。
幾何的 profile criticality は不要で、full-depth integral tail だけで degree 210 が出る。
-/
theorem integralCriticalTail_le_dyadicPolylog
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {a ell : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hy : 0 ≤ P.y)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    P.m - a ≤
      terminalCriticalSuffixPolylogConstant * (ell + 1) ^ 210 := by
  obtain ⟨C⟩ := exists_criticalRecordChain a (P.m - a)
  have ha : a ≤ P.m := A.1
  have hEnd : a + (P.m - a) = P.m :=
    Nat.add_sub_of_le ha
  have hBounds :
      (∀ r : ℕ,
          r ∈ C.recordLengths → r ≤ terminalRecordLengthBound ell) ∧
        C.finalLength ≤ terminalRecordLengthBound ell :=
    P.integralRecordChain_piece_bounds
      R A hy C le_rfl hEnd hmSize
  have hChain :
      P.m - a ≤
        (2 ^ 14 + 1) * terminalRecordLengthBound ell ^ 15 :=
    C.remaining_le_pow15_of_record_bounds
      R
      (terminalRecordLengthBound_pos ell)
      hBounds.1
      hBounds.2
  calc
    P.m - a
        ≤ (2 ^ 14 + 1) * terminalRecordLengthBound ell ^ 15 := hChain
    _ = terminalCriticalSuffixPolylogConstant * (ell + 1) ^ 210 :=
      terminalRecordLengthBound_pack_eq_polylog ell

/-- canonical arithmetic criticalization tail の dyadic-size bound。 -/
theorem criticalizationTail_le_dyadicPolylog
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    {ell : ℕ}
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    P.m - P.criticalizationStart ≤
      terminalCriticalSuffixPolylogConstant * (ell + 1) ^ 210 := by
  exact
    P.integralCriticalTail_le_dyadicPolylog
      R P.criticalizationStart_spec hy hmSize

/-- canonical arithmetic criticalization tail の Nat-log form。 -/
theorem criticalizationTail_le_log210
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y) :
    P.m - P.criticalizationStart ≤
      terminalCriticalSuffixPolylogConstant *
        (Nat.log 2 (P.m + 1) + 2) ^ 210 := by
  let ell := Nat.log 2 (P.m + 1) + 1
  have hmLt :
      P.m + 1 < 2 ^ (Nat.log 2 (P.m + 1) + 1) := by
    simpa using
      Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (P.m + 1)
  have hmSize : P.m + 1 ≤ 2 ^ ell := by
    dsimp [ell]
    exact Nat.le_of_lt hmLt
  have hMain := P.criticalizationTail_le_dyadicPolylog R hy hmSize
  simpa [ell, Nat.add_assoc] using hMain

/--
canonical arithmetic tail 自体も restricted Ostrowski fold 一個として exact に読める。
従って decisive window を canonical whole blocks と高々一つの left fragment へ分解できる。
-/
theorem criticalizationWindow_eq_restrictedPhaseFold
    (P : PureBProfileObstruction) :
    criticalIntervalDefectZ P.criticalizationStart P.m P.y =
      actualCriticalRestrictedPhaseDefectFold
        P.criticalizationStart P.m P.y := by
  exact
    criticalIntervalDefectZ_eq_actualCriticalRestrictedPhaseDefectFold
      P.criticalizationStart_spec.1 P.y

/-- origin exclusion 後の canonical stopping column。 -/
noncomputable def criticalizationStopColumn
    (P : PureBProfileObstruction) : ℕ :=
  P.criticalizationStart - 1

/-- positive criticalization start の一歩左は full-depth ではない。 -/
theorem not_integralCriticalTail_at_stopColumn
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart) :
    ¬ IsIntegralCriticalTail P P.criticalizationStopColumn := by
  intro A
  have hMin := P.criticalizationStart_minimal A
  unfold criticalizationStopColumn at hMin
  omega

/-- arithmetic start から geometric terminal start までの corridor も同じ window 内。 -/
theorem terminalCriticalStart_sub_criticalizationStart_le
    (P : PureBProfileObstruction) :
    P.terminalCriticalStart - P.criticalizationStart ≤
      P.m - P.criticalizationStart := by
  have hTerminal := P.terminalCriticalStart_spec.1
  have hStart := P.criticalizationStart_le_terminalCriticalStart
  omega

end PureBProfileObstruction

/--
actual minimal B に残る decisive terminal window packet。

`start` より右では critical recurrence が integral、`stopColumn=start-1` で初めて失敗し、
geometric terminal suffix の開始点も同じ window の内部にある。
-/
structure TerminalPolylogWindowPacket
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) where
  start : ℕ
  stopColumn : ℕ

  start_eq :
    start = (M.toPureBProfileObstruction hL).criticalizationStart
  stop_eq : stopColumn = start - 1

  start_pos : 0 < start
  start_le_terminalCriticalStart :
    start ≤ (M.toPureBProfileObstruction hL).terminalCriticalStart

  integral_from_start :
    IsIntegralCriticalTail (M.toPureBProfileObstruction hL) start
  nonintegral_at_stop :
    ¬ IsIntegralCriticalTail (M.toPureBProfileObstruction hL) stopColumn

  window_width_le :
    (M.toPureBProfileObstruction hL).m - start ≤
      terminalCriticalSuffixPolylogConstant *
        (Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1) + 2) ^ 210

  noncritical_corridor_le :
    (M.toPureBProfileObstruction hL).terminalCriticalStart - start ≤
      terminalCriticalSuffixPolylogConstant *
        (Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1) + 2) ^ 210

  restricted_window_exact :
    criticalIntervalDefectZ
        start (M.toPureBProfileObstruction hL).m
        (M.toPureBProfileObstruction hL).y =
      actualCriticalRestrictedPhaseDefectFold
        start (M.toPureBProfileObstruction hL).m
        (M.toPureBProfileObstruction hL).y

  tiny_q : 3 * (M.toPureBProfileObstruction hL).q <
    (M.toPureBProfileObstruction hL).m

/-- actual minimal B から terminal polylog window packet を canonical に構成。 -/
noncomputable def MinimalActualABObstructionPacket.toTerminalPolylogWindowPacket
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    TerminalPolylogWindowPacket R M hL := by
  let P := M.toPureBProfileObstruction hL
  let s := P.criticalizationStart
  have hsPos : 0 < s := by
    simpa [s, P] using M.criticalizationStart_pos R hL
  have hWidth :=
    P.criticalizationTail_le_log210 R (M.toPureBProfileObstruction_y_nonneg hL)
  have hCorridor :
      P.terminalCriticalStart - s ≤
        terminalCriticalSuffixPolylogConstant *
          (Nat.log 2 (P.m + 1) + 2) ^ 210 := by
    exact le_trans
      P.terminalCriticalStart_sub_criticalizationStart_le
      (by simpa [s] using hWidth)
  refine {
    start := s
    stopColumn := s - 1
    start_eq := rfl
    stop_eq := rfl
    start_pos := hsPos
    start_le_terminalCriticalStart := ?_
    integral_from_start := ?_
    nonintegral_at_stop := ?_
    window_width_le := ?_
    noncritical_corridor_le := ?_
    restricted_window_exact := ?_
    tiny_q := ?_
  }
  · simpa [s] using P.criticalizationStart_le_terminalCriticalStart
  · simpa [s] using P.criticalizationStart_spec
  · simpa [s, PureBProfileObstruction.criticalizationStopColumn] using
      P.not_integralCriticalTail_at_stopColumn hsPos
  · simpa [P, s] using hWidth
  · simpa [P, s] using hCorridor
  · simpa [P, s] using P.criticalizationWindow_eq_restrictedPhaseFold
  · simpa [P] using P.small_strip

/--
最終 localization summary：B の full-depth stopping と geometric terminal transition は
一つの degree-210 terminal window の内部に同時に入る。
-/
theorem MinimalActualABObstructionPacket.decisive_geometry_localized_to_terminal_polylog_window
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    ∃ start stop : ℕ,
      0 < start ∧
      stop = start - 1 ∧
      start ≤ (M.toPureBProfileObstruction hL).terminalCriticalStart ∧
      IsIntegralCriticalTail (M.toPureBProfileObstruction hL) start ∧
      ¬ IsIntegralCriticalTail (M.toPureBProfileObstruction hL) stop ∧
      (M.toPureBProfileObstruction hL).m - start ≤
        terminalCriticalSuffixPolylogConstant *
          (Nat.log 2 ((M.toPureBProfileObstruction hL).m + 1) + 2) ^ 210 := by
  let W := M.toTerminalPolylogWindowPacket R hL
  exact
    ⟨W.start, W.stopColumn,
      W.start_pos,
      W.stop_eq,
      W.start_le_terminalCriticalStart,
      W.integral_from_start,
      W.nonintegral_at_stop,
      W.window_width_le⟩

end ExternalArithmetic
end CSTMicro
end Collatz2
