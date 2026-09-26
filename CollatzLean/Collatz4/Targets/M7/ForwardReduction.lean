import CollatzLean.Collatz4.Finite.ForwardProblem
import CollatzLean.Collatz4.Targets.M7.LengthBound

/-!
# Collatz4.Targets.M7.ForwardReduction

一般 `ForwardProblem` に渡すための m=7 固有データを定義する。

候補列そのものは `LengthBound` で一般等差列から特殊化済みなので、
ここでは開始状態・残り段数・目標状態だけを組み立てる。
-/

namespace Collatz4.Targets.M7

open Collatz4.Finite

/-- 候補 n の開始自然数 `3^n-1`。 -/
def initialA (i : Fin candidateCount) : ℕ :=
  3 ^ candidateN i - 1

/-- 開始自然数を `(t,u)` 状態へ圧縮する。 -/
def initialState (i : Fin candidateCount) : ForwardState :=
  ForwardState.ofNat (initialA i)

/-- n から共通時刻 8456 までに必要な段数。 -/
def remainingSteps (i : Fin candidateCount) : ℕ :=
  targetTime - candidateN i

/-- 従来名との互換用: 候補 i の最終状態。 -/
def finalState (i : Fin candidateCount) : ForwardState :=
  run (remainingSteps i) (initialState i)

/-- 最後の1段前 `s=8455` の状態。 -/
def checkpointState (i : Fin candidateCount) : ForwardState :=
  run (8455 - candidateN i) (initialState i)

/-- 目標状態 `(10996, 87*2^2400-1)`。 -/
def targetState : ForwardState :=
  ⟨targetTwoExponent, targetOdd⟩

/--
一般層へ渡す m=7 の前向き問題。
ここが m=7 特殊化と一般 finite exclusion の接点になる。
-/
def forwardProblem : Collatz4.Finite.ForwardProblem (Fin candidateCount) where
  initialState := initialState
  remainingSteps := remainingSteps
  targetState := targetState

/-- 一般 problem の finalState は従来の m=7 finalState と定義的に一致する。 -/
theorem forwardProblem_finalState (i : Fin candidateCount) :
    forwardProblem.finalState i = finalState i := by
  rfl

/--
Collatz4 における m=7 の reduced 前向き候補。

元の数論的 witness からここへ落とす bridge は別定理として積み上げる。
-/
def M7ForwardCandidate : Prop :=
  forwardProblem.Candidate

/-- 従来の存在量化表示。 -/
theorem m7ForwardCandidate_iff :
    M7ForwardCandidate ↔ ∃ i : Fin candidateCount, finalState i = targetState := by
  rfl

end Collatz4.Targets.M7
