import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselChain

/-!
# 第3例探索 D4.1: 計算可能な backward Hensel predecessor

右側状態 `(qNext, deltaNext)` から、staircase 条件

  deltaPrev = deltaNext

または

  deltaPrev + 1 = deltaNext

を満たす predecessor を有限に探す。

各 exponent 候補 `deltaPrev` に対して recurrence

  3 * qPrev = 2 * qNext + 2^deltaPrev - 1

から `qPrev` を整数除算で一つだけ作り、元の等式を再検査する。
従って hot path には存在量化も proof object も入らない。

重要:
このファイルが実装するのは「内部 staircase step」である。
terminal `q = 0` の直前では `deltaNext` が staircase data として存在しないため、
terminal 用には exponent `deltaTerminal` を別入力とする seed 関数を用意する。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/-- backward Hensel の有限状態。 -/
@[ext]
structure ThirdExampleBackwardHenselState where
  q : ℤ
  delta : ℕ
  deriving DecidableEq, Repr

/-- recurrence の右辺。 -/
def thirdExampleBackwardRhs
    (qNext : ℤ)
    (deltaPrev : ℕ) : ℤ :=
  2 * qNext + (2 : ℤ) ^ deltaPrev - 1

/--
固定 exponent 候補に対する唯一の整数商候補。
割り切れない場合も一旦整数除算し、次の関数で recurrence を再検査する。
-/
def thirdExampleBackwardCandidateQ
    (qNext : ℤ)
    (deltaPrev : ℕ) : ℤ :=
  thirdExampleBackwardRhs qNext deltaPrev / 3

/--
固定した `deltaPrev` に対する計算可能 candidate。
exact recurrence が成立する場合だけ `some` を返す。
-/
def thirdExampleBackwardCandidate
    (qNext : ℤ)
    (deltaPrev : ℕ) : Option ThirdExampleBackwardHenselState :=
  let qPrev := thirdExampleBackwardCandidateQ qNext deltaPrev
  if 3 * qPrev = thirdExampleBackwardRhs qNext deltaPrev then
    some { q := qPrev, delta := deltaPrev }
  else
    none

/-- candidate が返ったなら、その state は指定 exponent で recurrence を exact に満たす。 -/
theorem thirdExampleBackwardCandidate_sound
    {qNext : ℤ}
    {deltaPrev : ℕ}
    {S : ThirdExampleBackwardHenselState}
    (h : thirdExampleBackwardCandidate qNext deltaPrev = some S) :
    S.delta = deltaPrev ∧
      3 * S.q = thirdExampleBackwardRhs qNext deltaPrev := by
  unfold thirdExampleBackwardCandidate at h
  dsimp only at h
  by_cases hEq :
      3 * thirdExampleBackwardCandidateQ qNext deltaPrev =
        thirdExampleBackwardRhs qNext deltaPrev
  · rw [ite_eq_left hEq] at h
    have hState :
        ({ q := thirdExampleBackwardCandidateQ qNext deltaPrev
           delta := deltaPrev } : ThirdExampleBackwardHenselState) = S :=
      Option.some.inj h
    rw [← hState]
    exact ⟨rfl, hEq⟩
  · rw [ite_eq_right hEq] at h
    contradiction

/--
recurrence を満たす整数 `qPrev` が既に存在するなら、固定 exponent candidate は
その値を exact に返す。
-/
theorem thirdExampleBackwardCandidate_complete
    {qNext : ℤ}
    {deltaPrev : ℕ}
    {qPrev : ℤ}
    (hRec :
      3 * qPrev = thirdExampleBackwardRhs qNext deltaPrev) :
    thirdExampleBackwardCandidate qNext deltaPrev =
      some { q := qPrev, delta := deltaPrev } := by
  have hQ :
      thirdExampleBackwardCandidateQ qNext deltaPrev = qPrev := by
    unfold thirdExampleBackwardCandidateQ
    rw [← hRec]
    exact Int.mul_ediv_cancel_left qPrev (by norm_num : (3 : ℤ) ≠ 0)
  unfold thirdExampleBackwardCandidate
  dsimp only
  rw [hQ]
  rw [ite_eq_left hRec]

/--
内部 staircase predecessor。

まず `deltaPrev = deltaNext` を試し、失敗した場合だけ
`deltaPrev = deltaNext - 1` を試す。`deltaNext = 0` では後者は試さない。
既存の predecessor 一意性により、actual chain 上ではこの優先順序で情報を失わない。
-/
def thirdExampleComputableBackwardPredecessor
    (qNext : ℤ)
    (deltaNext : ℕ) : Option ThirdExampleBackwardHenselState :=
  match thirdExampleBackwardCandidate qNext deltaNext with
  | some S => some S
  | none =>
      if 0 < deltaNext then
        thirdExampleBackwardCandidate qNext (deltaNext - 1)
      else
        none

/--
計算関数が `some S` を返したなら、既存の純算術 predicate
`IsBackwardPredecessor` を満たす。
-/
theorem thirdExampleComputableBackwardPredecessor_sound
    {qNext : ℤ}
    {deltaNext : ℕ}
    {S : ThirdExampleBackwardHenselState}
    (h :
      thirdExampleComputableBackwardPredecessor qNext deltaNext = some S) :
    ExternalArithmetic.MonotoneSuffixHenselChain.IsBackwardPredecessor
      qNext deltaNext S.delta S.q := by
  unfold thirdExampleComputableBackwardPredecessor at h
  cases hSame : thirdExampleBackwardCandidate qNext deltaNext with
  | some T =>
      rw [hSame] at h
      have hTS : T = S := Option.some.inj h
      rw [← hTS]
      have hSpec := thirdExampleBackwardCandidate_sound hSame
      constructor
      · exact Or.inl hSpec.1
      · simpa [thirdExampleBackwardRhs, hSpec.1] using hSpec.2
  | none =>
      rw [hSame] at h
      by_cases hPos : 0 < deltaNext
      · rw [ite_eq_left hPos] at h
        have hSpec := thirdExampleBackwardCandidate_sound h
        constructor
        · right
          omega
        · simpa [thirdExampleBackwardRhs, hSpec.1] using hSpec.2
      · rw [ite_eq_right hPos] at h
        contradiction
/--
既存の `IsBackwardPredecessor` witness があれば、計算関数はその state を exact に返す。
同じ exponent 候補が先に通った場合でも、既存の `backwardPredecessor_unique` により
実 witness と一致する。従って有限計算側で余分な枝は残らない。
-/
theorem thirdExampleComputableBackwardPredecessor_complete
    {qNext : ℤ}
    {deltaNext deltaPrev : ℕ}
    {qPrev : ℤ}
    (hPrev :
      ExternalArithmetic.MonotoneSuffixHenselChain.IsBackwardPredecessor
        qNext deltaNext deltaPrev qPrev) :
    thirdExampleComputableBackwardPredecessor qNext deltaNext =
      some { q := qPrev, delta := deltaPrev } := by
  rcases hPrev with ⟨hDelta, hRec⟩
  rcases hDelta with hSame | hDown
  · subst deltaPrev
    have hCandidate :=
      thirdExampleBackwardCandidate_complete hRec
    unfold thirdExampleComputableBackwardPredecessor
    rw [hCandidate]
  · have hPos : 0 < deltaNext := by
      omega
    have hSub : deltaNext - 1 = deltaPrev := by
      omega
    have hDownCandidate :
        thirdExampleBackwardCandidate qNext (deltaNext - 1) =
          some { q := qPrev, delta := deltaPrev } := by
      rw [hSub]
      exact thirdExampleBackwardCandidate_complete hRec
    unfold thirdExampleComputableBackwardPredecessor
    cases hSameCandidate :
        thirdExampleBackwardCandidate qNext deltaNext with
    | none =>
        simpa [hPos] using hDownCandidate
    | some T =>
        have hSpec :=
          thirdExampleBackwardCandidate_sound hSameCandidate
        have hOther :
            ExternalArithmetic.MonotoneSuffixHenselChain.IsBackwardPredecessor
              qNext deltaNext T.delta T.q := by
          constructor
          · exact Or.inl hSpec.1
          · simpa [thirdExampleBackwardRhs, hSpec.1] using hSpec.2
        have hUnique :=
          ExternalArithmetic.MonotoneSuffixHenselChain.backwardPredecessor_unique
            hOther
            ⟨Or.inr hDown, hRec⟩
        have hEq : deltaNext = deltaPrev := by
          calc
            deltaNext = T.delta := hSpec.1.symm
            _ = deltaPrev := hUnique.1
        omega

/--
terminal `qNext = 0` の直前を作る seed。
terminal では next exponent を使わず、直前 exponent `deltaTerminal` を明示入力にする。
-/
def thirdExampleComputableTerminalPredecessor
    (deltaTerminal : ℕ) : Option ThirdExampleBackwardHenselState :=
  thirdExampleBackwardCandidate 0 deltaTerminal

/-- terminal seed が返ったなら `3*q = 2^delta - 1` を exact に満たす。 -/
theorem thirdExampleComputableTerminalPredecessor_sound
    {deltaTerminal : ℕ}
    {S : ThirdExampleBackwardHenselState}
    (h : thirdExampleComputableTerminalPredecessor deltaTerminal = some S) :
    S.delta = deltaTerminal ∧
      3 * S.q = (2 : ℤ) ^ deltaTerminal - 1 := by
  have hSpec := thirdExampleBackwardCandidate_sound h
  constructor
  · exact hSpec.1
  · simpa [thirdExampleBackwardRhs] using hSpec.2

/-- terminal recurrence を満たす actual state があれば terminal seed はそれを返す。 -/
theorem thirdExampleComputableTerminalPredecessor_complete
    {deltaTerminal : ℕ}
    {qPrev : ℤ}
    (hRec :
      3 * qPrev = (2 : ℤ) ^ deltaTerminal - 1) :
    thirdExampleComputableTerminalPredecessor deltaTerminal =
      some { q := qPrev, delta := deltaTerminal } := by
  unfold thirdExampleComputableTerminalPredecessor
  apply thirdExampleBackwardCandidate_complete
  simpa [thirdExampleBackwardRhs] using hRec

end ThirdExampleSearch
end CSTMicro
end Collatz2
