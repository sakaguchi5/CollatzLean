import CollatzLean.Collatz4.Finite.Forward

/-!
# Collatz4.Finite.ForwardProblem

有限候補の「開始状態・残り段数・目標状態」だけを抽象化する。

ここが finite certificate と m 固有データの境界になる。
-/

namespace Collatz4.Finite

/--
添字型 `ι` ごとに一つの開始状態と残り段数を持つ一般前向き問題。
-/
structure ForwardProblem (ι : Type) where
  initialState : ι → ForwardState
  remainingSteps : ι → ℕ
  targetState : ForwardState

namespace ForwardProblem

/-- 候補 i を指定された段数だけ進めた最終状態。 -/
def finalState {ι : Type} (P : ForwardProblem ι) (i : ι) : ForwardState :=
  run (P.remainingSteps i) (P.initialState i)

/-- 有限化後の候補のどれかが目標状態へ一致する、という命題。 -/
def Candidate {ι : Type} (P : ForwardProblem ι) : Prop :=
  ∃ i : ι, P.finalState i = P.targetState

/-- 目標状態への一致から、2指数成分の一致を取り出す。 -/
theorem final_t_eq_target_t_of_hit
    {ι : Type} {P : ForwardProblem ι} {i : ι}
    (h : P.finalState i = P.targetState) :
    (P.finalState i).t = P.targetState.t := by
  exact congrArg ForwardState.t h

/-- 目標状態への一致から、奇数部分の一致を取り出す。 -/
theorem final_u_eq_target_u_of_hit
    {ι : Type} {P : ForwardProblem ι} {i : ι}
    (h : P.finalState i = P.targetState) :
    (P.finalState i).u = P.targetState.u := by
  exact congrArg ForwardState.u h

end ForwardProblem

end Collatz4.Finite
