import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBIntegralCriticalTail
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ActualBoundaryAFromRhin

/-!
# Pure B: origin full-depth exclusion

`PureBIntegralCriticalTail` で導入した arithmetic critical tail が origin まで到達すると、
profile numerator 全体が `3^m` で消える。そのとき origin state は critical boundary の
実際の affine realization の start になる。

actual minimal B では witness `y` は非負であり、origin state は `y` 以下である。
一方 reviewed `RhinLinearForm14` から critical Ferrers boundary は既に
`WordPureSeparation` を満たす。したがって nondecreasing critical realization は存在できず、
origin full-depth は排除される。

ここで A branch を再展開しない。既に閉じた `boundaryA_eliminated_from_RhinLinearForm14`
を contradiction theorem として一度だけ使用する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- actual pure packet の odd depth は minimal bad word の odd count。 -/
theorem MinimalActualABObstructionPacket.pureB_m_eq_oddCount
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).m = oddCount M.word := by
  let P := M.toPureBProfileObstruction hL
  have hUpperOdd :
      Collatz2.Word.oddSteps M.actual.firstFailureEdge.upperExponentWord =
        M.actual.firstFailureEdge.step.edge.oddTotal :=
    M.actual.firstFailureEdge.upperExponentWord_oddSteps
  have hEdgeOdd :
      oddCount M.actual.firstFailureEdge.step.edge.upperWord =
        M.actual.firstFailureEdge.step.edge.oddTotal :=
    M.actual.firstFailureEdge.step.edge.upperWord_oddCount
  have hUpperWord :
      M.actual.firstFailureEdge.step.edge.upperWord = M.word := by
    simpa [
      ActualABObstructionPacket.firstFailureEdge,
      ActualBoundaryFirstFailureCocyclePacket.firstFailureEdge,
      FirstFailureProvenance.toFirstFailureEdge
    ] using M.failureStep_upperWord_eq_word
  change
    Collatz2.Word.oddSteps M.actual.firstFailureEdge.upperExponentWord =
      oddCount M.word
  calc
    Collatz2.Word.oddSteps M.actual.firstFailureEdge.upperExponentWord
        = M.actual.firstFailureEdge.step.edge.oddTotal := hUpperOdd
    _ = oddCount M.actual.firstFailureEdge.step.edge.upperWord := hEdgeOdd.symm
    _ = oddCount M.word := by rw [hUpperWord]

/-- actual pure packet の terminal two-depth は minimal bad word length。 -/
theorem MinimalActualABObstructionPacket.pureB_H_eq_word_length
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).H = M.word.length := by
  let P := M.toPureBProfileObstruction hL
  have hm := M.pureB_m_eq_oddCount hL
  have hFP := M.word_firstPassage
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hTerminal :=
    firstPassage_twoSteps_eq_beattyIndex_oddSteps_add_one hFP hLen
  have hTwo := hFP.twoSteps_exponentWordOfParity_eq_length hLen
  have hBeatty :
      beattyIndex (oddCount M.word) + 1 = M.word.length := by
    rw [← oddSteps_exponentWordOfParity M.word]
    rw [← hTerminal]
    exact hTwo
  calc
    P.H = beattyIndex P.m + 1 := P.terminal_beatty
    _ = beattyIndex (oddCount M.word) + 1 := by rw [hm]
    _ = M.word.length := hBeatty

/--
critical boundary の standard affine numerator は critical prefix numerator `Psi(m)`。

profile route で既に証明した checkpoint sum を使い、critical boundary の extra-depth が
全て zero であることから exact に同定する。
-/
theorem criticalBoundary_affineConst_cast_eq_criticalPrefixPhiZ
    {v : ParityWord}
    (hFP : IsFirstPassageWord v)
    (hLen : 1 < v.length) :
    (affineConst (criticalBoundaryWord v.length) : ℤ) =
      criticalPrefixPhiZ (oddCount v) := by
  let b : ParityWord := criticalBoundaryWord v.length
  have hBFP : IsFirstPassageWord b := by
    simpa [b] using criticalBoundaryWord_isFirstPassage hFP
  have hBLen : 1 < b.length := by
    simpa [b] using hLen
  have hLead : leadingEvenCount b = 0 := by
    obtain ⟨t, ht⟩ := hBFP.exists_eq_true_cons hBLen
    rw [ht]
    simp
  have hStdWord := affineConst_eq_twoPow_leading_mul_wordAffineConst b
  rw [hLead] at hStdWord
  simp only [pow_zero, one_mul] at hStdWord
  have hOdd :
      Collatz2.Word.oddSteps (exponentWordOfParity b) = oddCount v := by
    rw [oddSteps_exponentWordOfParity]
    simpa [b] using criticalBoundaryWord_oddCount_eq hFP
  have hProfile :=
    firstPassage_profileAffineNumerator_eq_wordAffineConst hBFP hBLen
  rw [hOdd] at hProfile
  have hZero :
      ∀ k : ℕ, k < oddCount v → parityExtraDepth b k = 0 := by
    intro k hk
    apply criticalBoundaryWord_parityExtraDepth_eq_zero hFP hLen
    rw [hOdd]
    exact hk
  have hProfileCritical :
      profileAffineNumerator (oddCount v) (parityExtraDepth b) =
        criticalPrefixPhiNat (oddCount v) := by
    unfold profileAffineNumerator criticalPrefixPhiNat
    apply Finset.sum_congr rfl
    intro k hkMem
    have hk : k < oddCount v := Finset.mem_range.mp hkMem
    have hCheckpoint :
        profileCheckpoint (parityExtraDepth b) k = beattyIndex k := by
      unfold profileCheckpoint
      rw [hZero k hk]
      simp
    rw [hCheckpoint]
  have hNat :
      affineConst b = criticalPrefixPhiNat (oddCount v) := by
    calc
      affineConst b
          = Collatz2.Word.affineConst (exponentWordOfParity b) := hStdWord
      _ = profileAffineNumerator (oddCount v) (parityExtraDepth b) := hProfile.symm
      _ = criticalPrefixPhiNat (oddCount v) := hProfileCritical
  have hCast := congrArg (fun n : ℕ => (n : ℤ)) hNat
  rw [criticalPrefixPhiNat_cast_eq_criticalPrefixPhiZ] at hCast
  simpa [b] using hCast

/--
terminal-contracting word が safe なら、任意の actual affine realization は
start より endpoint が strict に小さい。
-/
theorem affineRealization_decreases_of_wordPureSeparation
    {v : ParityWord}
    {x y : ℕ}
    (hContract : CoefficientContracting v)
    (hSafe : WordPureSeparation v)
    (hAffine : AffineRealizes v x y) :
    y < x := by
  have hRle : leastRepresentative v ≤ x :=
    hAffine.leastRepresentative_le_start
  have hGapNonneg : 0 ≤ wordTerminalGap v := by omega
  have hGR :
      wordTerminalGap v * leastRepresentative v ≤
        wordTerminalGap v * x :=
    Nat.mul_le_mul_left _ hRle
  have hBlt : affineConst v < wordTerminalGap v * x :=
    lt_of_lt_of_le hSafe hGR
  unfold AffineRealizes at hAffine
  unfold CoefficientContracting at hContract
  have hGapEq :
      wordTerminalGap v + 3 ^ oddCount v = 2 ^ v.length := by
    unfold wordTerminalGap
    exact Nat.sub_add_cancel (Nat.le_of_lt hContract)
  by_contra hnot
  have hxy : x ≤ y := by omega
  have hMul : 2 ^ v.length * x ≤ 2 ^ v.length * y :=
    Nat.mul_le_mul_left _ hxy
  rw [hAffine, ← hGapEq, add_mul] at hMul
  omega

/--
actual minimal B では arithmetic critical tail は origin まで到達できない。
-/
theorem MinimalActualABObstructionPacket.originFullDepth_impossible
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    ¬ IsIntegralCriticalTail (M.toPureBProfileObstruction hL) 0 := by
  intro A0
  let P := M.toPureBProfileObstruction hL
  let b : ParityWord := criticalBoundaryWord M.word.length
  have hy : 0 ≤ P.y := M.toPureBProfileObstruction_y_nonneg hL
  have hm : P.m = oddCount M.word := M.pureB_m_eq_oddCount hL
  have hH : P.H = M.word.length := M.pureB_H_eq_word_length hL
  have hFP : IsFirstPassageWord M.word := M.word_firstPassage
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hBFP : IsFirstPassageWord b := by
    simpa [b] using criticalBoundaryWord_isFirstPassage hFP
  have hBLen : b.length = P.H := by
    simp [b, hH]
  have hBOdd : oddCount b = P.m := by
    calc
      oddCount b = oddCount M.word := by
        simpa [b] using criticalBoundaryWord_oddCount_eq hFP
      _ = P.m := hm.symm
  let x : ℕ := P.integralCriticalTailStateNat A0 hy 0 (by omega) (by omega)
  let y : ℕ := P.yNat
  have hxCast :
      (x : ℤ) = P.integralCriticalTailStateInt A0 0 (by omega) (by omega) := by
    simpa [x] using
      P.integralCriticalTailStateNat_cast A0 hy (s := 0) (by omega) (by omega)
  have hyCast : (y : ℤ) = P.y := by
    simpa [y] using P.yNat_cast hy
  have hSpec :=
    P.integralCriticalTailStateInt_spec A0 (s := 0) (by omega) (by omega)
  have hBalance := P.terminalRawTail_zero_eq_profile_balance
  have hxLeZ :
      P.integralCriticalTailStateInt A0 0 (by omega) (by omega) ≤ P.y := by
    rw [hBalance] at hSpec
    simp only [Nat.sub_zero] at hSpec
    have hN :
        (0 : ℤ) ≤
          (profileDyadicCellNumerator P.m P.h : ℤ) := by
      positivity
    have hq :
        (0 : ℤ) ≤ (P.q : ℤ) := by
      positivity
    have hPow :
        0 < (3 : ℤ) ^ P.m := by
      positivity
    have hSub :
        (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) -
            (profileDyadicCellNumerator P.m P.h : ℤ)
          ≤
        (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) :=
      sub_le_self _ hN
    have hYq :
        P.y - (P.q : ℤ) ≤ P.y :=
      sub_le_self _ hq
    have hMulYq :
        (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ))
          ≤
        (3 : ℤ) ^ P.m * P.y :=
      mul_le_mul_of_nonneg_left hYq (le_of_lt hPow)
    have hMul :
        (3 : ℤ) ^ P.m *
            P.integralCriticalTailStateInt
              A0 0 (by omega) (by omega)
          ≤
        (3 : ℤ) ^ P.m * P.y := by
      calc
        (3 : ℤ) ^ P.m *
              P.integralCriticalTailStateInt
                A0 0 (by omega) (by omega)
            =
          (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) -
            (profileDyadicCellNumerator P.m P.h : ℤ) :=
          hSpec.symm
        _ ≤
          (3 : ℤ) ^ P.m * (P.y - (P.q : ℤ)) :=
          hSub
        _ ≤
          (3 : ℤ) ^ P.m * P.y :=
          hMulYq
    exact le_of_mul_le_mul_left hMul hPow
  have hxLe : x ≤ y := by
    rw [← hxCast, ← hyCast] at hxLeZ
    exact_mod_cast hxLeZ
  have hPhi := criticalBoundary_affineConst_cast_eq_criticalPrefixPhiZ hFP hLen
  rw [← hm] at hPhi
  have hRaw0 :
      P.terminalRawTail 0 =
        (2 : ℤ) ^ P.H * P.y - criticalPrefixPhiZ P.m := by
    unfold PureBProfileObstruction.terminalRawTail
    rw [beattyIndex_zero, Nat.sub_zero, criticalPrefixPhiZ_eq_interval_zero]
    rw [P.terminal_beatty]
    rw [pow_succ]
    ring
  have hAffineZ :
      (2 : ℤ) ^ b.length * (y : ℤ) =
        (3 : ℤ) ^ oddCount b * (x : ℤ) + (affineConst b : ℤ) := by
    rw [hBLen, hBOdd, hxCast, hyCast, hPhi]
    rw [hRaw0] at hSpec
    simp only [Nat.sub_zero] at hSpec
    calc
      (2 : ℤ) ^ P.H * P.y
          =
        ((2 : ℤ) ^ P.H * P.y -
            criticalPrefixPhiZ P.m) +
          criticalPrefixPhiZ P.m := by
            exact
              (sub_add_cancel
                ((2 : ℤ) ^ P.H * P.y)
                (criticalPrefixPhiZ P.m)).symm
      _ =
        (3 : ℤ) ^ P.m *
            P.integralCriticalTailStateInt
              A0 0 (by omega) (by omega) +
          criticalPrefixPhiZ P.m := by
            rw [hSpec]
  have hAffine : AffineRealizes b x y := by
    unfold AffineRealizes
    exact_mod_cast hAffineZ
  have hBoundary : IsFerrersBoundary b := by
    have hBoundary0 := M.actual.cocycle.provenance.boundary_isBoundary
    have hEq := M.actual.boundary_eq_critical
    rw [hEq] at hBoundary0
    simpa [b, MinimalActualABObstructionPacket.word] using hBoundary0
  have hSafe : WordPureSeparation b :=
    boundaryA_eliminated_from_RhinLinearForm14
      R b hBoundary (by simpa [b, M.word_length_eq] using hL)
  have hContract : CoefficientContracting b := hBFP.2.2
  have hDecrease :=
    affineRealization_decreases_of_wordPureSeparation hContract hSafe hAffine
  omega

/-- origin full-depth exclusion を profile numerator divisibility で読む。 -/
theorem MinimalActualABObstructionPacket.not_threePow_dvd_profileNumerator
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    ¬ (3 : ℤ) ^ (M.toPureBProfileObstruction hL).m ∣
        (profileDyadicCellNumerator
          (M.toPureBProfileObstruction hL).m
          (M.toPureBProfileObstruction hL).h : ℤ) := by
  intro hDvd
  apply M.originFullDepth_impossible R hL
  exact
    ((M.toPureBProfileObstruction hL).originIntegralCriticalTail_iff_profileNumerator_dvd).2
      hDvd

/-- actual minimal B の arithmetic criticalization start は strict positive。 -/
theorem MinimalActualABObstructionPacket.criticalizationStart_pos
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    0 < (M.toPureBProfileObstruction hL).criticalizationStart := by
  by_contra hnot
  have hZero :
      (M.toPureBProfileObstruction hL).criticalizationStart = 0 := by
    omega
  have hSpec :=
    (M.toPureBProfileObstruction hL).criticalizationStart_spec
  rw [hZero] at hSpec
  exact M.originFullDepth_impossible R hL hSpec

end ExternalArithmetic
end CSTMicro
end Collatz2
