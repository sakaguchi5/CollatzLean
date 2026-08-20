import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBExposedPredecessorIndex

/-!
# Pure B: exposed index = actual first-passage predecessor

pure condition

  k < m,
  h(k) > 0,
  e_k >= 2

を actual parity word の `10 -> 01` predecessor と同定する。

`e_k >= 2` は selected odd の直後に explicit even があることを意味し、
`h(k)>0` は一段右へ戻した lower prefix に first-passage slack を与える。
逆向きには first-passage predecessor の selected cut は extraDepth >= 1 であり、
upper word が `10` を持つため selected run gap は少なくとも 2。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- actual minimal B へ入る first-passage predecessor が cut `k` に存在すること。 -/
def HasActualExposedPredecessorAt
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (k : ℕ) : Prop :=
  ∃ lower : ParityWord,
    ∃ S : FerrersStep lower M.word,
      IsFirstPassageWord lower ∧ S.edge.rankCut = k

namespace MinimalActualABObstructionPacket

/-- pure endpoint checkpoint は actual odd-only prefix depth と一致する。 -/
theorem profileEndpointCheckpoint_eq_actualPrefixTwoDepth
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (hk : k ≤ (M.toPureBProfileObstruction hL).m) :
    (M.toPureBProfileObstruction hL).profileEndpointCheckpoint k =
      Collatz2.Word.prefixTwoDepth
        (exponentWordOfParity M.word) k := by
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  have hFP : IsFirstPassageWord M.word := M.word_firstPassage
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hM : P.m = oddCount M.word := by
    simpa [P] using M.toPureBProfileObstruction_m_eq_wordOddCount hL
  have hkLeP : k ≤ P.m := by
    simpa [P] using hk
  by_cases hkLt : k < P.m
  · rw [P.profileEndpointCheckpoint_of_lt hkLt]
    have hkWord :
        k < Collatz2.Word.oddSteps w := by
      rw [show Collatz2.Word.oddSteps w = oddCount M.word by
        simp [w, oddSteps_exponentWordOfParity]]
      rw [← hM]
      exact hkLt
    have hCheckpoint :=
      firstPassage_profileCheckpoint_eq_prefixTwoDepth hFP hLen hkWord
    have hProfileK :
        P.h k = parityExtraDepth M.word k := by
      simp only [toPureBProfileObstruction_h_apply, P]
    unfold profileCheckpoint
    rw [hProfileK]
    simpa [w, profileCheckpoint] using hCheckpoint
  · have hkEq : k = P.m := by omega
    subst k
    rw [P.profileEndpointCheckpoint_m]
    have hTotal :
        P.H = Collatz2.Word.twoSteps w := by
      calc
        P.H = beattyIndex P.m + 1 := P.terminal_beatty
        _ = beattyIndex (Collatz2.Word.oddSteps w) + 1 := by
          have hmWord : P.m = Collatz2.Word.oddSteps w := by
            rw [show Collatz2.Word.oddSteps w = oddCount M.word by
              simp [w, oddSteps_exponentWordOfParity]]
            exact hM
          rw [hmWord]
        _ = Collatz2.Word.twoSteps w := by
          symm
          simpa [w] using
            firstPassage_twoSteps_eq_beattyIndex_oddSteps_add_one hFP hLen
    have hPrefixEnd :
        Collatz2.Word.prefixTwoDepth w (Collatz2.Word.oddSteps w) =
          Collatz2.Word.twoSteps w := by
      unfold Collatz2.Word.prefixTwoDepth Collatz2.Word.oddSteps
      rw [List.take_length]
    have hmWord : P.m = Collatz2.Word.oddSteps w := by
      simpa [w, oddSteps_exponentWordOfParity] using hM
    rw [hmWord, hPrefixEnd, hTotal]

/-- actual endpoint time は pure `H`。 -/
theorem pureH_eq_actualWordLength
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    (M.toPureBProfileObstruction hL).H = M.word.length := by
  let P := M.toPureBProfileObstruction hL
  have hFP : IsFirstPassageWord M.word := M.word_firstPassage
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hM : P.m = oddCount M.word := by
    simpa [P] using M.toPureBProfileObstruction_m_eq_wordOddCount hL
  calc
    P.H = beattyIndex P.m + 1 := P.terminal_beatty
    _ = beattyIndex
          (Collatz2.Word.oddSteps (exponentWordOfParity M.word)) + 1 := by
      rw [oddSteps_exponentWordOfParity, ← hM]
    _ = Collatz2.Word.twoSteps (exponentWordOfParity M.word) := by
      symm
      exact firstPassage_twoSteps_eq_beattyIndex_oddSteps_add_one hFP hLen
    _ = M.word.length := hFP.twoSteps_exponentWordOfParity_eq_length hLen

/--
pure run gap `>=2` なら kth odd の直後は actual word で `false`。
同時に kth odd の左 context を exact に切り出す。
-/
private theorem exists_selected_true_false_of_exposed
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (E : (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex k) :
    ∃ left right : ParityWord,
      M.word = left ++ true :: false :: right ∧
      oddCount left = k ∧
      left.length =
        profileCheckpoint (M.toPureBProfileObstruction hL).h k := by
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  have hk : k < P.m := E.lt_m
  have hFP : IsFirstPassageWord M.word := M.word_firstPassage
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hM : P.m = oddCount M.word := by
    simpa [P] using M.toPureBProfileObstruction_m_eq_wordOddCount hL
  have hPrefixK := M.profileEndpointCheckpoint_eq_actualPrefixTwoDepth hL (Nat.le_of_lt hk)
  have hPrefixK1 :=
    M.profileEndpointCheckpoint_eq_actualPrefixTwoDepth hL
      (by omega : k + 1 ≤ P.m)
  have hRunGap :
      2 ≤ Collatz2.Word.prefixTwoDepth w (k + 1) -
        Collatz2.Word.prefixTwoDepth w k := by
    have h := E.two_le_runGap
    unfold PureBProfileObstruction.profileRunGap at h
    rw [hPrefixK, hPrefixK1] at h
    simpa [w, P] using h
  obtain ⟨left, rest, hWord, hOddLeft⟩ :=
    exists_append_true_of_lt_oddCount
      M.word
      (by rw [← hM]; exact hk)
  have hLead : leadingEvenCount M.word = 0 :=
    hFP.leadingEvenCount_eq_zero_of_one_lt_length hLen
  have hRun :=
    leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_before_true
      left rest
  rw [← hWord] at hRun
  rw [hLead, zero_add, hOddLeft] at hRun
  have hLeftLen :
      left.length = Collatz2.Word.prefixTwoDepth w k := by
    unfold Collatz2.Word.prefixTwoDepth
    exact hRun.symm
  cases rest with
  | nil =>
      have hOddWord : oddCount M.word = k + 1 := by
        rw [hWord, cstOddCount_append]
        rw [hOddLeft]
        simp [oddCount, bitNat]
      have hkEnd : k + 1 = P.m := by
        exact hOddWord.symm.trans hM.symm
      have hPrefixNext :
          Collatz2.Word.prefixTwoDepth w (k + 1) = M.word.length := by
        calc
          Collatz2.Word.prefixTwoDepth w (k + 1)
              = P.profileEndpointCheckpoint (k + 1) := by
                symm
                simpa [P, w] using hPrefixK1
          _ = P.H := by rw [hkEnd, P.profileEndpointCheckpoint_m]
          _ = M.word.length := by
                simpa [P] using M.pureH_eq_actualWordLength hL
      have hWordLength : M.word.length = left.length + 1 := by
        rw [hWord]
        simp
      rw [← hLeftLen, hPrefixNext, hWordLength] at hRunGap
      omega
  | cons b right =>
      cases b with
      | false =>
          refine ⟨left, right, ?_, hOddLeft, ?_⟩
          · simpa using hWord
          · have hCheckpoint :
                profileCheckpoint P.h k =
                  Collatz2.Word.prefixTwoDepth w k := by
              calc
                profileCheckpoint P.h k = P.profileEndpointCheckpoint k := by
                  symm
                  exact P.profileEndpointCheckpoint_of_lt hk
                _ = Collatz2.Word.prefixTwoDepth w k := by
                  simpa [P, w] using hPrefixK
            calc
              left.length = Collatz2.Word.prefixTwoDepth w k := hLeftLen
              _ = profileCheckpoint P.h k := hCheckpoint.symm
              _ = profileCheckpoint (M.toPureBProfileObstruction hL).h k := by
                rfl
      | true =>
          have hShape :
              M.word = (left ++ [true]) ++ true :: right := by
            simpa [List.append_assoc] using hWord
          have hRunNext :=
            leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_before_true
              (left ++ [true]) right
          rw [← hShape] at hRunNext
          rw [hLead, zero_add] at hRunNext
          have hOddNext : oddCount (left ++ [true]) = k + 1 := by
            rw [cstOddCount_append, hOddLeft]
            simp [oddCount, bitNat]
          rw [hOddNext] at hRunNext
          have hPrefixNext :
              Collatz2.Word.prefixTwoDepth w (k + 1) = left.length + 1 := by
            unfold Collatz2.Word.prefixTwoDepth
            simpa using hRunNext
          rw [← hLeftLen, hPrefixNext] at hRunGap
          omega

/-- exposed cut から exact rank-cut predecessor を構成する。 -/
theorem exists_actualPredecessor_of_exposedIndex
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (E : (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex k) :
    HasActualExposedPredecessorAt M k := by
  let P := M.toPureBProfileObstruction hL
  let w := exponentWordOfParity M.word
  have hk : k < P.m := E.lt_m
  have hDepthPos : 0 < P.h k := E.depth_pos
  have hFP : IsFirstPassageWord M.word := M.word_firstPassage
  have hLen : 1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  obtain ⟨left, right, hWord, hOddLeft, hLeftLen⟩ :=
    exists_selected_true_false_of_exposed M hL E
  let A : AdjacentFerrersSwap := {
    leftContext := left
    rightContext := right
  }
  have hUpper : M.word = A.upperWord := by
    dsimp [A, AdjacentFerrersSwap.upperWord]
    simpa [List.append_assoc] using hWord
  let lower : ParityWord := A.lowerWord
  let S : FerrersStep lower M.word := {
    edge := A
    lower_eq := rfl
    upper_eq := hUpper
  }
  have hRankCut : A.rankCut = k := by
    dsimp [A, AdjacentFerrersSwap.rankCut]
    exact hOddLeft
  have hPosition : A.position = profileCheckpoint P.h k := by
    dsimp [A, AdjacentFerrersSwap.position]
    exact hLeftLen
  have hDepthLe : P.h k ≤ beattyIndex k := P.admissible.depth_le hk
  have hkPos : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    have hDepthLe0 :
        P.h 0 ≤ beattyIndex 0 := by
      simpa [hk0] using hDepthLe
    have hDepthPos0 :
        0 < P.h 0 := by
      simpa [hk0] using hDepthPos
    rw [beattyIndex_zero] at hDepthLe0
    omega
  have hPrefix :
      profileCheckpoint P.h k = Collatz2.Word.prefixTwoDepth w k := by
    calc
      profileCheckpoint P.h k = P.profileEndpointCheckpoint k := by
        symm
        exact P.profileEndpointCheckpoint_of_lt hk
      _ = Collatz2.Word.prefixTwoDepth w k := by
        simpa [P, w] using
          M.profileEndpointCheckpoint_eq_actualPrefixTwoDepth hL (Nat.le_of_lt hk)
  have hSuccLeBeta :
      Collatz2.Word.prefixTwoDepth w k + 1 ≤ beattyIndex k := by
    rw [← hPrefix]
    unfold profileCheckpoint
    omega
  have hSuccLeCritical :
      Collatz2.Word.prefixTwoDepth w k + 1 ≤
        Collatz2.Word.criticalHeight k := by
    rw [← beattyIndex_eq_wordCriticalHeight_all]
    exact hSuccLeBeta
  have hPowLe :
      2 ^ (Collatz2.Word.prefixTwoDepth w k + 1) ≤
        2 ^ Collatz2.Word.criticalHeight k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hSuccLeCritical
  have hCritPow := Collatz2.Word.criticalHeight_pow_lt_threePow hkPos
  have hSlack0 :
      2 ^ (Collatz2.Word.prefixTwoDepth w k + 1) < 3 ^ k :=
    lt_of_le_of_lt hPowLe hCritPow
  have hSlack : 2 ^ (A.position + 1) < 3 ^ A.rankCut := by
    rw [hRankCut, hPosition, hPrefix]
    exact hSlack0
  have hLowerFP : IsFirstPassageWord lower := by
    apply FerrersStep.lower_firstPassage_of_upper_and_rankCellSlack S hFP
    simpa [S] using hSlack
  exact ⟨lower, S, hLowerFP, by simpa [S] using hRankCut⟩

end MinimalActualABObstructionPacket

namespace FerrersStep

/--
upper word の selected `10` は、selected odd run の長さを少なくとも 2 にする。
endpoint run も同じ statement で扱う。
-/
theorem two_le_selected_upper_prefixRunGap
    {lower upper : ParityWord}
    (S : FerrersStep lower upper)
    (hUpperFP : IsFirstPassageWord upper) :
    2 ≤
      Collatz2.Word.prefixTwoDepth S.edge.rankUpperExponentWord (S.edge.rankCut + 1) -
        Collatz2.Word.prefixTwoDepth S.edge.rankUpperExponentWord S.edge.rankCut := by
  have hEdgeUpperFP : IsFirstPassageWord S.edge.upperWord := by
    exact Eq.mp (congrArg IsFirstPassageWord S.upper_eq) hUpperFP
  have hAtCut := S.edge.prefixTwoDepth_rankCut_eq_position hEdgeUpperFP
  by_cases hRightZero : oddCount S.edge.rightContext = 0
  · have hCutEnd : S.edge.rankCut + 1 = S.edge.oddTotal := by
      unfold AdjacentFerrersSwap.rankCut AdjacentFerrersSwap.oddTotal
      omega
    have hOddSteps :
        Collatz2.Word.oddSteps S.edge.rankUpperExponentWord = S.edge.oddTotal :=
      S.edge.rankUpperExponentWord_oddSteps
    have hEnd :
        Collatz2.Word.prefixTwoDepth
            S.edge.rankUpperExponentWord (S.edge.rankCut + 1) =
          S.edge.length := by
      rw [hCutEnd, ← hOddSteps]
      unfold Collatz2.Word.prefixTwoDepth Collatz2.Word.oddSteps
      rw [List.take_length]
      exact S.edge.rankUpperExponentWord_twoSteps hEdgeUpperFP
    have hLen : S.edge.position + 2 ≤ S.edge.length := by
      unfold AdjacentFerrersSwap.position AdjacentFerrersSwap.length
      omega
    rw [hAtCut, hEnd]
    omega
  · have hRightPos : 0 < oddCount S.edge.rightContext := by omega
    obtain ⟨before, after, hRight, hOddBefore⟩ :=
      exists_append_true_of_lt_oddCount
        S.edge.rightContext hRightPos
    let pre : ParityWord :=
      S.edge.leftContext ++ [true, false] ++ before
    have hShape :
        S.edge.upperWord = pre ++ true :: after := by
      dsimp [pre]
      unfold AdjacentFerrersSwap.upperWord
      rw [hRight]
      simp [List.append_assoc]
    have hLead := S.edge.rankUpper_leadingEvenCount_eq_zero hEdgeUpperFP
    have hRun :=
      leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_before_true
        pre after
    rw [← hShape] at hRun
    rw [hLead, zero_add] at hRun
    have hOddPre : oddCount pre = S.edge.rankCut + 1 := by
      dsimp [pre]
      rw [cstOddCount_append, cstOddCount_append]
      have hPair :
          oddCount ([true, false] : ParityWord) = 1 := by
        simp [oddCount, bitNat]
      rw [hPair, hOddBefore]
      simp [AdjacentFerrersSwap.rankCut]
    rw [hOddPre] at hRun
    have hNext :
        Collatz2.Word.prefixTwoDepth
            S.edge.rankUpperExponentWord (S.edge.rankCut + 1) =
          pre.length := by
      unfold Collatz2.Word.prefixTwoDepth AdjacentFerrersSwap.rankUpperExponentWord
      exact hRun
    have hPreLen : S.edge.position + 2 ≤ pre.length := by
      dsimp [pre, AdjacentFerrersSwap.position]
      simp
    rw [hAtCut, hNext]
    omega

end FerrersStep

namespace MinimalActualABObstructionPacket

/-- actual first-passage predecessor から pure exposed conditions を回収する。 -/
theorem exposedIndex_of_actualPredecessor
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ}
    (A : HasActualExposedPredecessorAt M k) :
    (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex k := by
  let P := M.toPureBProfileObstruction hL
  obtain ⟨lower, S, hLowerFP, hRankCut⟩ := A
  have hUpperFP : IsFirstPassageWord M.word := M.word_firstPassage
  have hM : P.m = oddCount M.word := by
    simpa [P] using M.toPureBProfileObstruction_m_eq_wordOddCount hL
  have hOddTotal : S.edge.oddTotal = oddCount M.word := by
    calc
      S.edge.oddTotal = oddCount S.edge.upperWord :=
        S.edge.upperWord_oddCount.symm
      _ = oddCount M.word := by rw [← S.upper_eq]
  have hk : k < P.m := by
    have hCut := S.edge.rankCut_lt_oddSteps
    rw [S.edge.rankUpperExponentWord_oddSteps] at hCut
    rw [hRankCut, hOddTotal, ← hM] at hCut
    exact hCut
  have hExtra := S.one_le_extraDepth_rankCut hLowerFP
  have hUpperWordEq :
      S.edge.rankUpperExponentWord = exponentWordOfParity M.word := by
    unfold AdjacentFerrersSwap.rankUpperExponentWord
    exact congrArg exponentWordOfParity S.upper_eq.symm
  have hDepthActual : 0 < parityExtraDepth M.word k := by
    unfold parityExtraDepth
    rw [← hUpperWordEq, ← hRankCut]
    omega
  have hDepth : 0 < P.h k := by
    simpa [P] using hDepthActual
  have hPrefixGap := FerrersStep.two_le_selected_upper_prefixRunGap S hUpperFP
  have hEndpointK :=
    M.profileEndpointCheckpoint_eq_actualPrefixTwoDepth hL (Nat.le_of_lt hk)
  have hEndpointK1 :=
    M.profileEndpointCheckpoint_eq_actualPrefixTwoDepth hL
      (by omega : k + 1 ≤ P.m)
  have hGap : 2 ≤ P.profileRunGap k := by
    unfold PureBProfileObstruction.profileRunGap
    rw [hEndpointK, hEndpointK1]
    rw [← hUpperWordEq, ← hRankCut]
    exact hPrefixGap
  exact ⟨hk, hDepth, hGap⟩

/--
main dictionary: pure exposed cut と actual first-passage predecessor existence は exact に同値。
-/
theorem exposedIndex_iff_actualPredecessor
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    {k : ℕ} :
    (M.toPureBProfileObstruction hL).IsExposedPredecessorIndex k ↔
      HasActualExposedPredecessorAt M k := by
  constructor
  · exact M.exists_actualPredecessor_of_exposedIndex hL
  · exact M.exposedIndex_of_actualPredecessor hL

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
