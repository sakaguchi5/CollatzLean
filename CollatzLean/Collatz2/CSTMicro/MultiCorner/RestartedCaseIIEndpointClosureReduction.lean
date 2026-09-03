import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedCaseIIActualEndpointReduction
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedActualProfileWeightBridge
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedActualDoublePredecessorSafety
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBActualProfileCoordinateBridge

/-!
# Case II endpoint `s=c`: `c<m` の閉鎖と `c=m` の最終縮約

前段までで `s=c` endpoint mass

  E_c = A_c + 2^(beta(b)-1+width)

が exact positive affine seed に一致すること、また actual Shared-Cost 側では

  modulus * q_* =
    gap * (deltaSum - representativeThreshold) + actualExtra

が成立することを得た。

このファイルでは次の二段階を行う。

1. `E_c < actualExtra` なら representative threshold は no-carry 側へ入り、
   double predecessor safety から `q_* < 0`。一方 endpoint bridge は `q_* > 0`。
   よって矛盾。

2. `c < m` では

     A_c < A_m = affineConst(B)

   かつ terminal actual cell について

     boundaryMass < deltaB_terminal

   なので `E_c < actualExtra` が自動的に成立する。

3. 最終端 `c = m` では

     A_c = affineConst(B),
     boundaryMass = 2 * deltaB_terminal

   となるため、`E_c < actualExtra` は exact に

     deltaB_terminal < deltaB_previous

   と同値になる。

したがって endpoint bridge と double predecessor packet が構成済みなら、
`c<m` は contradiction まで閉じ、残る `c=m` は
`deltaB_previous > deltaB_terminal` という一個の幾何的不等式へ縮約される。
-/

namespace Collatz2
namespace CSTMicro

open ExternalArithmetic

namespace ExternalArithmetic
namespace MinimalActualABObstructionPacket

/--
actual minimal bad word から作った pure packet の terminal time `H` は、
元の parity word の length そのもの。
-/
theorem toPureBProfileObstruction_H_eq_wordLength
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).H = M.word.length := by
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hEndpoint :=
    firstPassage_twoSteps_eq_beattyIndex_oddSteps_add_one
      M.word_firstPassage hLen
  have hTwo :=
    M.word_firstPassage.twoSteps_exponentWordOfParity_eq_length hLen
  have hOdd := oddSteps_exponentWordOfParity M.word
  have hWordBeatty :
      M.word.length = beattyIndex (oddCount M.word) + 1 := by
    calc
      M.word.length =
          Collatz2.Word.twoSteps (exponentWordOfParity M.word) :=
        hTwo.symm
      _ =
          beattyIndex
              (Collatz2.Word.oddSteps (exponentWordOfParity M.word)) + 1 :=
        hEndpoint
      _ = beattyIndex (oddCount M.word) + 1 := by
        rw [hOdd]
  have hPureBeatty :=
    (M.toPureBProfileObstruction hL).terminal_beatty
  have hm := M.toPureBProfileObstruction_m_eq_wordOddCount hL
  rw [hm] at hPureBeatty
  omega

/-- pure packet の terminal gap は actual parity word の terminal gap と同じ。 -/
theorem toPureBProfileObstruction_gap_eq_wordTerminalGap
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).gap = wordTerminalGap M.word := by
  unfold PureBProfileObstruction.gap columnLayerGap wordTerminalGap
  rw [
    M.toPureBProfileObstruction_H_eq_wordLength hL,
    M.toPureBProfileObstruction_m_eq_wordOddCount hL
  ]

/--
full pure profile affine numerator は actual parity word の affine constant そのもの。

既存 private construction theorem を外へ漏らさず、

* pure profile defect equation,
* `y = R + q`,
* parity normalized-defect factorization

だけから公開形として再構成する。
-/
theorem toPureBProfileObstruction_profileAffine_eq_wordAffineConst
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    profileAffineNumerator
        (M.toPureBProfileObstruction hL).m
        (M.toPureBProfileObstruction hL).h =
      affineConst M.word := by
  let P := M.toPureBProfileObstruction hL
  have hUpper :
      M.actual.firstFailureEdge.step.edge.upperWord = M.word := by
    unfold ActualABObstructionPacket.firstFailureEdge
    unfold ActualBoundaryFirstFailureCocyclePacket.firstFailureEdge
    unfold FirstFailureProvenance.toFirstFailureEdge
    dsimp
    exact M.failureStep_upperWord_eq_word
  have hR :
      M.actual.firstFailureEdge.step.edge.upperR =
        leastRepresentative M.word := by
    unfold AdjacentFerrersSwap.upperR
    rw [hUpper]
  have hPureAffine := P.profileDefect_eq_profileAffine_sub_gap_mul_y
  have hPureQ := P.profileDefect_eq_threePow_mul_q
  have hGap := M.toPureBProfileObstruction_gap_eq_wordTerminalGap hL
  have hY := M.toPureBProfileObstruction_y_eq_upperR_add_q hL
  have hQ := M.toPureBProfileObstruction_q_eq hL
  have hm := M.toPureBProfileObstruction_m_eq_wordOddCount hL
  rw [hR] at hY
  rw [hGap, hY] at hPureAffine
  rw [hQ, hm] at hPureQ
  have hPure :
      (profileAffineNumerator P.m P.h : ℤ) -
          (wordTerminalGap M.word : ℤ) *
            ((leastRepresentative M.word : ℤ) + (M.actual.q : ℤ)) =
        (3 : ℤ) ^ oddCount M.word * (M.actual.q : ℤ) := by
    linarith [hPureAffine, hPureQ]
  have hFactor :=
    wordSeparationDefectInt_eq_modulus_mul_normalized
      M.word M.word_firstPassage.2.2
  have hQNorm := M.actual_q_cast_eq_word_normalized
  rw [← hQNorm] at hFactor
  unfold wordSeparationDefectInt at hFactor
  have hContract :
      3 ^ oddCount M.word < 2 ^ M.word.length :=
    M.word_firstPassage.2.2
  have hGapAddNat :
      wordTerminalGap M.word + 3 ^ oddCount M.word =
        parityModulus M.word := by
    unfold wordTerminalGap parityModulus
    omega
  have hGapAdd :
      (parityModulus M.word : ℤ) =
        (wordTerminalGap M.word : ℤ) +
          (3 : ℤ) ^ oddCount M.word := by
    have hZ :=
      congrArg (fun n : ℕ => (n : ℤ)) hGapAddNat
    push_cast at hZ
    exact hZ.symm
  rw [hGapAdd] at hFactor
  have hCast :
      (profileAffineNumerator P.m P.h : ℤ) =
        (affineConst M.word : ℤ) := by
    nlinarith [hPure, hFactor]
  exact_mod_cast hCast

end MinimalActualABObstructionPacket
end ExternalArithmetic

namespace MultiCorner

/-- profile affine numerator は右へ一段進むごとに strict に増える。 -/
theorem profileAffineNumerator_lt_succ
    (h : ℕ → ℕ)
    (n : ℕ) :
    profileAffineNumerator n h <
      profileAffineNumerator (n + 1) h := by
  rw [profileAffineNumerator_succ_rightAffine h n]
  have hPow : 0 < 2 ^ profileCheckpoint h n := by
    positivity
  nlinarith

/-- profile affine numerator は endpoint index に関して strict monotone。 -/
theorem profileAffineNumerator_strictMono
    (h : ℕ → ℕ)
    {a b : ℕ}
    (hab : a < b) :
    profileAffineNumerator a h <
      profileAffineNumerator b h := by
  induction b generalizing a with
  | zero =>
      omega
  | succ b ih =>
      by_cases hEq : a = b
      · subst a
        simpa [Nat.succ_eq_add_one] using
          profileAffineNumerator_lt_succ h b
      · have hab' : a < b := by
          omega
        have hLeft := ih hab'
        have hRight := profileAffineNumerator_lt_succ h b
        exact lt_trans hLeft (by
          simpa [Nat.succ_eq_add_one] using hRight)

namespace LastTwoSharedCostActualPairAssemblyInput

/--
terminal critical start が full profile endpoint より左なら、
restarted boundary mass は terminal actual cell の `deltaB` より strict に小さい。

`2 * deltaB_terminal = 3^(m-c) * boundaryMass` と `m-c>0` だけを使う。
-/
theorem boundaryMass_lt_step1_deltaB_of_terminal_lt_m
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (hcM :
      (M.toPureBProfileObstruction hL).terminalCriticalStart <
        (M.toPureBProfileObstruction hL).m) :
    2 ^ (beattyIndex S.b - 1 + S.width) <
      D.step1.edge.deltaB := by
  let P := M.toPureBProfileObstruction hL
  have hWeight :=
    D.two_mul_step1_deltaB_eq_threePow_terminalSuffix_mul_boundaryMass S
  have hDiff : 0 < P.m - P.terminalCriticalStart := by
    dsimp [P]
    omega
  have hPow : 3 ≤ 3 ^ (P.m - P.terminalCriticalStart) := by
    have hPow' : 3 ^ 1 ≤ 3 ^ (P.m - P.terminalCriticalStart) :=
      Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hDiff
    simpa using hPow'
  have hBoundaryPos :
      0 < 2 ^ (beattyIndex S.b - 1 + S.width) := by
    positivity
  have hThree :
      3 * 2 ^ (beattyIndex S.b - 1 + S.width) ≤
        2 * D.step1.edge.deltaB := by
    rw [hWeight]
    exact Nat.mul_le_mul_right
      (2 ^ (beattyIndex S.b - 1 + S.width)) hPow
  omega

end LastTwoSharedCostActualPairAssemblyInput

namespace RestartedTerminalGeometryPacket

/--
endpoint mass が actual Shared-Cost extra より strict に小さければ contradiction。

endpoint bridge は `q_* > 0` を与える一方、master identity から threshold が
no-carry 側へ入り、double predecessor safety は同じ `q_* < 0` を与える。
-/
theorem caseIIEndpoint_false_of_endpointMass_lt_actualExtra
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (X : RestartedActualDoublePredecessorData M hL N D)
    (H : S.CaseIIEndpointActualMassBridgeCandidate D)
    (hMassExtra :
      profileAffineNumerator
          (M.toPureBProfileObstruction hL).terminalCriticalStart
          (M.toPureBProfileObstruction hL).h +
          2 ^ (beattyIndex S.b - 1 + S.width) <
        affineConst M.word +
          D.step0.edge.deltaB + D.step1.edge.deltaB) :
    False := by
  let E : ℕ :=
    profileAffineNumerator
        (M.toPureBProfileObstruction hL).terminalCriticalStart
        (M.toPureBProfileObstruction hL).h +
      2 ^ (beattyIndex S.b - 1 + S.width)
  have hBridge :=
    S.caseIIEndpointAffineSharedCostBridge_of_actualMassBridgeCandidate D H
  have hPos :=
    S.doubleNormalizedQCandidate_pos_of_caseIIEndpointBridge
      D.toPair
      D.step0.edge.toFareyCellPacket.residue
      D.step1.edge.toFareyCellPacket.residue
      hBridge
  have hCost := D.toPair_costs_eq_gap_sub_residues
  have hMaster :=
    D.toPair.modulus_mul_doubleNormalizedQCandidate_eq_masterRight'
      D.step0.edge.toFareyCellPacket.residue
      D.step1.edge.toFareyCellPacket.residue
      hCost.1 hCost.2
  rcases H with ⟨_hsEq, hMass⟩
  have hMassE :
      D.toPair.modulus *
          D.toPair.doubleNormalizedQCandidate
            D.step0.edge.toFareyCellPacket.residue
            D.step1.edge.toFareyCellPacket.residue =
        (E : ℤ) := by
    simpa [E] using hMass
  have hCoords := D.toPair_actual_coordinates
  rcases hCoords with
    ⟨hAffineB, _hQ, _hR, _hC0, _hC1,
      _hD0, _hD1, hW0, hW1⟩
  have hMassExtraZ :
      (E : ℤ) <
        D.toPair.affineB + D.toPair.weight0 + D.toPair.weight1 := by
    have hZ :
        (E : ℤ) <
          (affineConst M.word : ℤ) +
            (D.step0.edge.deltaB : ℤ) +
            (D.step1.edge.deltaB : ℤ) := by
      exact_mod_cast hMassExtra
    rw [hAffineB, hW0, hW1]
    exact hZ
  have hDeltaLt :
      D.toPair.deltaSum < D.toPair.representativeThreshold := by
    rw [hMassE] at hMaster
    nlinarith [D.toPair.gap_pos, hMassExtraZ]
  have hNeg :=
    X.pair_doubleNormalizedQCandidate_neg (le_of_lt hDeltaLt)
  linarith

/--
`c<m` では endpoint mass が actual extra より自動的に小さい。

左項は profile affine の strict monotonicity、右端 boundary mass は
terminal actual `deltaB` の strict 下界で処理する。
-/
theorem endpointMass_lt_actualExtra_of_terminal_lt_m
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (hcM :
      (M.toPureBProfileObstruction hL).terminalCriticalStart <
        (M.toPureBProfileObstruction hL).m) :
    profileAffineNumerator
        (M.toPureBProfileObstruction hL).terminalCriticalStart
        (M.toPureBProfileObstruction hL).h +
        2 ^ (beattyIndex S.b - 1 + S.width) <
      affineConst M.word +
        D.step0.edge.deltaB + D.step1.edge.deltaB := by
  let P := M.toPureBProfileObstruction hL
  have hAffineLt :
      profileAffineNumerator P.terminalCriticalStart P.h <
        profileAffineNumerator P.m P.h :=
    profileAffineNumerator_strictMono P.h (by
      dsimp [P]
      exact hcM)
  have hFull :=
    M.toPureBProfileObstruction_profileAffine_eq_wordAffineConst hL
  have hAffineLt' :
      profileAffineNumerator P.terminalCriticalStart P.h <
        affineConst M.word := by
    rw [hFull] at hAffineLt
    exact hAffineLt
  have hBoundaryLt :=
    D.boundaryMass_lt_step1_deltaB_of_terminal_lt_m S hcM
  dsimp [P] at hAffineLt'
  omega

/--
Case II endpoint `s=c` で `c<m` なら contradiction。

残っている endpoint mass bridge candidate と double predecessor packet を受け取った後は、
追加の算術仮定を必要としない。
-/
theorem caseIIEndpoint_false_of_terminal_lt_m
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (X : RestartedActualDoublePredecessorData M hL N D)
    (H : S.CaseIIEndpointActualMassBridgeCandidate D)
    (hcM :
      (M.toPureBProfileObstruction hL).terminalCriticalStart <
        (M.toPureBProfileObstruction hL).m) :
    False := by
  exact
    S.caseIIEndpoint_false_of_endpointMass_lt_actualExtra
      D X H (S.endpointMass_lt_actualExtra_of_terminal_lt_m D hcM)

/--
最終端 `c=m` では endpoint-mass-vs-extra 条件が exact に

  deltaB_terminal < deltaB_previous

へ縮約する。
-/
theorem endpointMass_lt_actualExtra_iff_terminalDeltaB_lt_previous_of_terminal_eq_m
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (hcEq :
      (M.toPureBProfileObstruction hL).terminalCriticalStart =
        (M.toPureBProfileObstruction hL).m) :
    (profileAffineNumerator
          (M.toPureBProfileObstruction hL).terminalCriticalStart
          (M.toPureBProfileObstruction hL).h +
          2 ^ (beattyIndex S.b - 1 + S.width) <
        affineConst M.word +
          D.step0.edge.deltaB + D.step1.edge.deltaB) ↔
      D.step1.edge.deltaB < D.step0.edge.deltaB := by
  let P := M.toPureBProfileObstruction hL
  have hFull :=
    M.toPureBProfileObstruction_profileAffine_eq_wordAffineConst hL
  have hAffine :
      profileAffineNumerator P.terminalCriticalStart P.h =
        affineConst M.word := by
    rw [hcEq]
    simpa [P] using hFull
  have hWeight :=
    D.two_mul_step1_deltaB_eq_threePow_terminalSuffix_mul_boundaryMass S
  have hBoundary :
      2 * D.step1.edge.deltaB =
        2 ^ (beattyIndex S.b - 1 + S.width) := by
    simpa [hcEq] using hWeight
  dsimp [P] at hAffine
  constructor
  · intro h
    rw [hAffine, ← hBoundary] at h
    omega
  · intro h
    rw [hAffine, ← hBoundary]
    omega

/--
`c=m` で `deltaB_terminal < deltaB_previous` が証明できれば endpoint branch は閉じる。
-/
theorem caseIIEndpoint_false_of_terminal_eq_m_of_terminalDeltaB_lt_previous
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (X : RestartedActualDoublePredecessorData M hL N D)
    (H : S.CaseIIEndpointActualMassBridgeCandidate D)
    (hcEq :
      (M.toPureBProfileObstruction hL).terminalCriticalStart =
        (M.toPureBProfileObstruction hL).m)
    (hWeight : D.step1.edge.deltaB < D.step0.edge.deltaB) :
    False := by
  have hMassExtra :=
    (S.endpointMass_lt_actualExtra_iff_terminalDeltaB_lt_previous_of_terminal_eq_m
      D hcEq).2 hWeight
  exact
    S.caseIIEndpoint_false_of_endpointMass_lt_actualExtra
      D X H hMassExtra

/--
endpoint branch がまだ生き残るなら、必ず `c=m` であり、かつ

  deltaB_previous ≤ deltaB_terminal

でなければならない。

従って `c=m` における逆向き strict inequality
`deltaB_terminal < deltaB_previous` が最終の幾何 obligation である。
-/
theorem caseIIEndpoint_survivor_forces_terminal_eq_m_and_previousDeltaB_le_terminal
    {L : ℕ}
    {M : MinimalActualABObstructionPacket L}
    {hL : 2 < L}
    {N : LastTwoExposedNormalForm (M.toPureBProfileObstruction hL)}
    (S : RestartedTerminalGeometryPacket
      (M.toPureBProfileObstruction hL) N)
    (D : LastTwoSharedCostActualPairAssemblyInput M hL N)
    (X : RestartedActualDoublePredecessorData M hL N D)
    (H : S.CaseIIEndpointActualMassBridgeCandidate D) :
    (M.toPureBProfileObstruction hL).terminalCriticalStart =
        (M.toPureBProfileObstruction hL).m ∧
      D.step0.edge.deltaB ≤ D.step1.edge.deltaB := by
  let P := M.toPureBProfileObstruction hL
  have hcLeM : P.terminalCriticalStart ≤ P.m :=
    P.terminalCriticalStart_spec.1
  have hcEq : P.terminalCriticalStart = P.m := by
    by_contra hne
    have hcM : P.terminalCriticalStart < P.m := by
      omega
    exact
      S.caseIIEndpoint_false_of_terminal_lt_m D X H (by
        simpa [P] using hcM)
  refine ⟨by simpa [P] using hcEq, ?_⟩
  by_contra hnot
  have hWeight : D.step1.edge.deltaB < D.step0.edge.deltaB := by
    omega
  exact
    S.caseIIEndpoint_false_of_terminal_eq_m_of_terminalDeltaB_lt_previous
      D X H (by simpa [P] using hcEq) hWeight

end RestartedTerminalGeometryPacket

end MultiCorner
end CSTMicro
end Collatz2
