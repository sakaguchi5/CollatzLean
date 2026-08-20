import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBActualProfileCoordinateBridge

/-!
# Pure B: terminal top cell の actual Ferrers predecessor realization

actual minimal B に対し

  c = terminalCriticalStart,
  k = c - 1,
  p = beattyIndex k - h k

と置く。positive criticalization start では `h(k)>0`。
actual word の k-th odd は position `p` にあり、その直後は even でなければならない。
したがって word は

  left ++ [true,false] ++ right

と分解でき、その `10 -> 01` predecessor は first-passage のまま残る。

この step は exact に

  position = p,
  fareyLeftExponent = c,
  oddTotal = m

を持つ。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/--
actual minimal B の terminal top rank における
word prefix two-depth は geometric terminal top cell position と一致する。
-/
private theorem actualTerminalTop_prefixTwoDepth_eq_position
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    Collatz2.Word.prefixTwoDepth
        (exponentWordOfParity M.word)
        ((M.toPureBProfileObstruction hL).terminalCriticalStart - 1) =
      (M.toPureBProfileObstruction hL).terminalTopCellPosition := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let k := c - 1
  have hStartP :
      0 < P.criticalizationStart := by
    simpa [P] using hStart
  have hFP :
      IsFirstPassageWord M.word :=
    M.word_firstPassage
  have hLen :
      1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hM :
      P.m = oddCount M.word := by
    simpa [P] using
      M.toPureBProfileObstruction_m_eq_wordOddCount hL
  have hcLe :
      c ≤ P.m := by
    simpa [c] using
      P.terminalCriticalStart_spec.1
  have hcPos :
      0 < c := by
    have hAC :=
      P.criticalizationStart_le_terminalCriticalStart
    dsimp [c]
    omega
  have hkM :
      k < P.m := by
    dsimp [k]
    omega
  have hkWord :
      k <
        Collatz2.Word.oddSteps
          (exponentWordOfParity M.word) := by
    rw [oddSteps_exponentWordOfParity, ← hM]
    exact hkM
  have hCheckpoint :=
    firstPassage_profileCheckpoint_eq_prefixTwoDepth
      hFP hLen hkWord
  have hProfileK :
      P.h k =
        parityExtraDepth M.word k := by
    simp only [
      toPureBProfileObstruction_h_apply,
      P
    ]
  rw [← hCheckpoint]
  unfold profileCheckpoint
  rw [← hProfileK]
  simp [
    PureBProfileObstruction.terminalTopCellPosition,
    PureBProfileObstruction.terminalTopColumn,
    k, c
  ]
  rfl

/--
terminal top rank に対応する `true` と、
その直後の bit を actual word から切り出す。
-/
private theorem exists_actualTerminalTop_selectedBit
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    ∃ left : ParityWord,
      ∃ b : Bool,
      ∃ right : ParityWord,
        M.word = left ++ true :: b :: right ∧
        oddCount left =
          (M.toPureBProfileObstruction hL).terminalCriticalStart - 1 ∧
        left.length =
          (M.toPureBProfileObstruction hL).terminalTopCellPosition := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let k := c - 1
  have hStartP :
      0 < P.criticalizationStart := by
    simpa [P] using hStart
  have hFP :
      IsFirstPassageWord M.word :=
    M.word_firstPassage
  have hLen :
      1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hM :
      P.m = oddCount M.word := by
    simpa [P] using
      M.toPureBProfileObstruction_m_eq_wordOddCount hL
  have hcLe :
      c ≤ P.m := by
    simpa [c] using
      P.terminalCriticalStart_spec.1
  have hcPos :
      0 < c := by
    have hAC :=
      P.criticalizationStart_le_terminalCriticalStart
    dsimp [c]
    omega
  have hkM :
      k < P.m := by
    dsimp [k]
    omega
  have hPosition :
      Collatz2.Word.prefixTwoDepth
          (exponentWordOfParity M.word) k =
        P.terminalTopCellPosition := by
    simpa [P, c, k] using
      actualTerminalTop_prefixTwoDepth_eq_position
        M hL hStart
  have hTop :
      0 < P.h k := by
    have h :=
      P.terminalTopCell_exists hStartP
    simpa [
      PureBProfileObstruction.terminalTopColumn,
      k, c
    ] using h
  have hDepth :
      P.h k ≤ beattyIndex k :=
    P.admissible.depth_le hkM
  have hPositionLtBeta :
      P.terminalTopCellPosition <
        beattyIndex k := by
    have hBetaPos :
        0 < beattyIndex k :=
      lt_of_lt_of_le hTop hDepth
    have hSub :
        beattyIndex k - P.h k <
          beattyIndex k :=
      Nat.sub_lt hBetaPos hTop
    simpa [
      PureBProfileObstruction.terminalTopCellPosition,
      PureBProfileObstruction.terminalTopColumn,
      k, c
    ] using hSub
  obtain ⟨left, rest, hWord, hOddLeft⟩ :=
    exists_append_true_of_lt_oddCount
      M.word
      (by
        rw [← hM]
        exact hkM)
  have hLead :
      leadingEvenCount M.word = 0 :=
    hFP.leadingEvenCount_eq_zero_of_one_lt_length hLen
  have hRun :=
    leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_before_true
      left rest
  rw [← hWord] at hRun
  rw [hLead, zero_add, hOddLeft] at hRun
  have hLeftLen :
      left.length =
        Collatz2.Word.prefixTwoDepth
          (exponentWordOfParity M.word) k := by
    unfold Collatz2.Word.prefixTwoDepth
    exact hRun.symm
  have hLeftPosition :
      left.length =
        P.terminalTopCellPosition := by
    rw [hLeftLen, hPosition]
  have hWordLen :
      M.word.length =
        beattyIndex P.m + 1 := by
    have hTwo :=
      hFP.twoSteps_exponentWordOfParity_eq_length hLen
    have hBeat :=
      firstPassage_twoSteps_eq_beattyIndex_oddSteps_add_one
        hFP hLen
    calc
      M.word.length
          =
        Collatz2.Word.twoSteps
          (exponentWordOfParity M.word) :=
        hTwo.symm
      _ =
        beattyIndex
            (Collatz2.Word.oddSteps
              (exponentWordOfParity M.word)) + 1 :=
        hBeat
      _ =
        beattyIndex P.m + 1 := by
        rw [
          oddSteps_exponentWordOfParity,
          ← hM
        ]
  have hBetaKM :
      beattyIndex k <
        beattyIndex P.m :=
    beattyIndex_strictMono hkM
  have hAfterSelected :
      left.length + 1 <
        M.word.length := by
    rw [hWordLen, hLeftPosition]
    omega
  cases rest with
  | nil =>
      have hLenEq :=
        congrArg List.length hWord
      simp at hLenEq
      omega
  | cons b right =>
      exact
        ⟨left, b, right,
          hWord,
          by simpa [k, c] using hOddLeft,
          by simpa using hLeftPosition⟩

/--
terminal top の選択 bit の直後が `false` なら、
その `10 -> 01` predecessor は genuine first-passage Ferrers step。
-/
private theorem exists_actualTerminalTop_predecessor_of_false_shape
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    {left right : ParityWord}
    (hWord :
      M.word =
        left ++ true :: false :: right)
    (hOddLeft :
      oddCount left =
        (M.toPureBProfileObstruction hL).terminalCriticalStart - 1)
    (hLeftPosition :
      left.length =
        (M.toPureBProfileObstruction hL).terminalTopCellPosition) :
    ∃ lower : ParityWord,
      ∃ S : FerrersStep lower M.word,
        IsFirstPassageWord lower ∧
        S.edge.position =
          (M.toPureBProfileObstruction hL).terminalTopCellPosition ∧
        S.edge.fareyLeftExponent =
          (M.toPureBProfileObstruction hL).terminalCriticalStart ∧
        S.edge.oddTotal =
          (M.toPureBProfileObstruction hL).m := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let k := c - 1
  have hOddLeft' :
      oddCount left = k := by
    simpa [P, c, k] using hOddLeft
  have hLeftPosition' :
      left.length = P.terminalTopCellPosition := by
    simpa [P] using hLeftPosition
  have hStartP :
      0 < P.criticalizationStart := by
    simpa [P] using hStart
  have hFP :
      IsFirstPassageWord M.word :=
    M.word_firstPassage
  have hLen :
      1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hM :
      P.m = oddCount M.word := by
    simpa [P] using
      M.toPureBProfileObstruction_m_eq_wordOddCount hL
  have hcLe :
      c ≤ P.m := by
    simpa [c] using
      P.terminalCriticalStart_spec.1
  have hcPos :
      0 < c := by
    have hAC :=
      P.criticalizationStart_le_terminalCriticalStart
    dsimp [c]
    omega
  have hkM :
      k < P.m := by
    dsimp [k]
    omega
  have hPosition :
      Collatz2.Word.prefixTwoDepth
          (exponentWordOfParity M.word) k =
        P.terminalTopCellPosition := by
    simpa [P, c, k] using
      actualTerminalTop_prefixTwoDepth_eq_position
        M hL hStart
  have hProfileK :
      P.h k =
        parityExtraDepth M.word k := by
    simp only [
      toPureBProfileObstruction_h_apply,
      P
    ]
  have hTop :
      0 < P.h k := by
    have h :=
      P.terminalTopCell_exists hStartP
    simpa [
      PureBProfileObstruction.terminalTopColumn,
      k, c
    ] using h
  have hDepth :
      P.h k ≤ beattyIndex k :=
    P.admissible.depth_le hkM
  let E : AdjacentFerrersSwap := {
    leftContext := left
    rightContext := right
  }
  have hUpper :
      M.word = E.upperWord := by
    dsimp [E, AdjacentFerrersSwap.upperWord]
    simpa [List.append_assoc] using hWord
  let lower : ParityWord :=
    E.lowerWord
  let S : FerrersStep lower M.word := {
    edge := E
    lower_eq := rfl
    upper_eq := hUpper
  }
  have hRankCut :
      E.rankCut = k := by
    dsimp [E, AdjacentFerrersSwap.rankCut]
    exact hOddLeft'
  have hEPosition :
      E.position = P.terminalTopCellPosition := by
    dsimp [E, AdjacentFerrersSwap.position]
    exact hLeftPosition'
  have hkSucc :
      k + 1 = c := by
    dsimp [k]
    exact
      Nat.sub_add_cancel
        (by omega : 1 ≤ c)
  have hLeftExponent :
      E.fareyLeftExponent = c := by
    dsimp [E, AdjacentFerrersSwap.fareyLeftExponent]
    rw [hOddLeft']
    exact hkSucc
  have hBetaKPos :
      0 < beattyIndex k :=
    lt_of_lt_of_le hTop hDepth
  have hkPos :
      0 < k := by
    by_contra hnot
    have hk0 :
        k = 0 :=
      Nat.eq_zero_of_not_pos hnot
    have h := hBetaKPos
    rw [hk0, beattyIndex_zero] at h
    omega
  have hExtraParity :
      0 < parityExtraDepth M.word k := by
    rw [← hProfileK]
    exact hTop
  have hExtra :
      0 <
        Collatz2.Word.extraDepth
          (exponentWordOfParity M.word) k := by
    simpa [parityExtraDepth] using
      hExtraParity
  have hSuccLe :
      Collatz2.Word.prefixTwoDepth
            (exponentWordOfParity M.word) k + 1 ≤
        Collatz2.Word.criticalHeight k := by
    unfold Collatz2.Word.extraDepth at hExtra
    omega
  have hPowLe :
      2 ^
          (Collatz2.Word.prefixTwoDepth
              (exponentWordOfParity M.word) k + 1) ≤
        2 ^ Collatz2.Word.criticalHeight k :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      hSuccLe
  have hCritPow :=
    Collatz2.Word.criticalHeight_pow_lt_threePow
      hkPos
  have hSlack0 :
      2 ^
          (Collatz2.Word.prefixTwoDepth
              (exponentWordOfParity M.word) k + 1) <
        3 ^ k :=
    lt_of_le_of_lt hPowLe hCritPow
  have hSlack :
      2 ^ (E.position + 1) <
        3 ^ E.rankCut := by
    rw [
      hRankCut,
      hEPosition,
      ← hPosition
    ]
    exact hSlack0
  have hLowerFP :
      IsFirstPassageWord lower := by
    apply
      FerrersStep.lower_firstPassage_of_upper_and_rankCellSlack
        S hFP
    simpa [S] using hSlack
  have hOddTotal :
      E.oddTotal = P.m := by
    calc
      E.oddTotal
          = oddCount E.upperWord :=
        E.upperWord_oddCount.symm
      _ = oddCount M.word := by
        rw [← hUpper]
      _ = P.m :=
        hM.symm
  refine ⟨lower, S, hLowerFP, ?_, ?_, ?_⟩
  · simpa [S] using hEPosition
  · simpa [S, c] using hLeftExponent
  · simpa [S] using hOddTotal

/--
terminal top に対応する selected `true` の直後が
さらに `true` であることは不可能。
-/
private theorem actualTerminalTop_next_true_impossible
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart)
    {left right : ParityWord}
    (hWord :
      M.word =
        left ++ true :: true :: right)
    (hOddLeft :
      oddCount left =
        (M.toPureBProfileObstruction hL).terminalCriticalStart - 1)
    (hLeftPosition :
      left.length =
        (M.toPureBProfileObstruction hL).terminalTopCellPosition) :
    False := by
  let P := M.toPureBProfileObstruction hL
  let c := P.terminalCriticalStart
  let k := c - 1
  have hOddLeft' :
      oddCount left = k := by
    simpa [P, c, k] using hOddLeft
  have hLeftPosition' :
      left.length = P.terminalTopCellPosition := by
    simpa [P] using hLeftPosition
  have hStartP :
      0 < P.criticalizationStart := by
    simpa [P] using hStart
  have hFP :
      IsFirstPassageWord M.word :=
    M.word_firstPassage
  have hLen :
      1 < M.word.length := by
    rw [M.word_length_eq]
    omega
  have hM :
      P.m = oddCount M.word := by
    simpa [P] using
      M.toPureBProfileObstruction_m_eq_wordOddCount hL
  have hcLe :
      c ≤ P.m := by
    simpa [c] using
      P.terminalCriticalStart_spec.1
  have hcPos :
      0 < c := by
    have hAC :=
      P.criticalizationStart_le_terminalCriticalStart
    dsimp [c]
    omega
  have hkM :
      k < P.m := by
    dsimp [k]
    omega
  have hTop :
      0 < P.h k := by
    have h :=
      P.terminalTopCell_exists hStartP
    simpa [
      PureBProfileObstruction.terminalTopColumn,
      k, c
    ] using h
  have hDepth :
      P.h k ≤ beattyIndex k :=
    P.admissible.depth_le hkM
  have hPositionLtBeta :
      P.terminalTopCellPosition <
        beattyIndex k := by
    have hBetaPos :
        0 < beattyIndex k :=
      lt_of_lt_of_le hTop hDepth
    have hSub :
        beattyIndex k - P.h k <
          beattyIndex k :=
      Nat.sub_lt hBetaPos hTop
    simpa [
      PureBProfileObstruction.terminalTopCellPosition,
      PureBProfileObstruction.terminalTopColumn,
      k, c
    ] using hSub
  have hLeftLtBeta :
      left.length < beattyIndex k := by
    rw [hLeftPosition]
    exact hPositionLtBeta
  by_cases hcEq : c = P.m
  · have hOddWord :
        P.m = k + 2 + oddCount right := by
      calc
        P.m = oddCount M.word := hM
        _ = oddCount left + 2 + oddCount right := by
          rw [hWord]
          simp [oddCount, bitNat, Nat.add_assoc]
          omega
        _ = k + 2 + oddCount right := by
          rw [hOddLeft']
    dsimp [k] at hOddWord
    omega
  · have hcLtM :
        c < P.m := by
      omega
    have hZeroC :
        P.h c = 0 :=
      P.terminalCriticalStart_spec.2
        c
        (by simp [c])
        hcLtM
    have hcWord :
        c <
          Collatz2.Word.oddSteps
            (exponentWordOfParity M.word) := by
      rw [
        oddSteps_exponentWordOfParity,
        ← hM
      ]
      exact hcLtM
    have hCheckpointC :=
      firstPassage_profileCheckpoint_eq_prefixTwoDepth
        hFP hLen hcWord
    have hProfileC :
        P.h c =
          parityExtraDepth M.word c := by
      simp only [
        toPureBProfileObstruction_h_apply,
        P
      ]
    have hPrefixC :
        Collatz2.Word.prefixTwoDepth
            (exponentWordOfParity M.word) c =
          beattyIndex c := by
      rw [← hCheckpointC]
      unfold profileCheckpoint
      rw [← hProfileC, hZeroC]
      simp
    have hShape :
        M.word =
          (left ++ [true]) ++ true :: right := by
      simpa [List.append_assoc] using hWord
    have hLead :
        leadingEvenCount M.word = 0 :=
      hFP.leadingEvenCount_eq_zero_of_one_lt_length
        hLen
    have hRunNext :=
      leadingEvenCount_add_twoSteps_take_exponentWordOfParity_eq_length_before_true
        (left ++ [true]) right
    rw [← hShape] at hRunNext
    rw [hLead, zero_add] at hRunNext
    have hOddNext :
        oddCount (left ++ [true]) = c := by
      rw [cstOddCount_append, hOddLeft]
      simp [oddCount, bitNat, c]
      omega
    rw [hOddNext] at hRunNext
    have hPrefixCImmediate :
        Collatz2.Word.prefixTwoDepth
            (exponentWordOfParity M.word) c =
          left.length + 1 := by
      unfold Collatz2.Word.prefixTwoDepth
      simpa using hRunNext
    have hBetaKC :
        beattyIndex k <
          beattyIndex c :=
      beattyIndex_strictMono
        (by
          dsimp [k]
          omega)
    rw [hPrefixC] at hPrefixCImmediate
    omega

/--
actual minimal B の terminal top cell は
genuine adjacent predecessor として実現する。
-/
theorem exists_terminalTopCellActualPredecessor_of_positive_criticalization
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hStart :
      0 < (M.toPureBProfileObstruction hL).criticalizationStart) :
    ∃ lower : ParityWord,
      ∃ S : FerrersStep lower M.word,
        IsFirstPassageWord lower ∧
        S.edge.position =
          (M.toPureBProfileObstruction hL).terminalTopCellPosition ∧
        S.edge.fareyLeftExponent =
          (M.toPureBProfileObstruction hL).terminalCriticalStart ∧
        S.edge.oddTotal =
          (M.toPureBProfileObstruction hL).m := by
  obtain ⟨left, b, right, hWord, hOddLeft, hLeftPosition⟩ :=
    exists_actualTerminalTop_selectedBit
      M hL hStart
  cases b with
  | false =>
      exact
        exists_actualTerminalTop_predecessor_of_false_shape
          M hL hStart
          hWord
          hOddLeft
          hLeftPosition
  | true =>
      exact
        (actualTerminalTop_next_true_impossible
          M hL hStart
          hWord
          hOddLeft
          hLeftPosition).elim


/-- Rhin origin exclusion を使った actual minimal B wrapper。 -/
theorem exists_terminalTopCellActualPredecessor
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L) :
    ∃ lower : ParityWord,
      ∃ S : FerrersStep lower M.word,
        IsFirstPassageWord lower ∧
        S.edge.position =
          (M.toPureBProfileObstruction hL).terminalTopCellPosition ∧
        S.edge.fareyLeftExponent =
          (M.toPureBProfileObstruction hL).terminalCriticalStart ∧
        S.edge.oddTotal =
          (M.toPureBProfileObstruction hL).m := by
  let P := M.toPureBProfileObstruction hL
  have hStart : 0 < P.criticalizationStart := by
    simpa [P] using M.criticalizationStart_pos R hL
  exact
    M.exists_terminalTopCellActualPredecessor_of_positive_criticalization
      hL hStart

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
