import CollatzLean.Collatz4.Finite.ForwardProblem


/-!
# Collatz4.Finite.ValuationGap

候補終点の 2 進指数に「禁止帯」があるとき、帯の内部に 2 進指数を持つ目標状態を
一括排除する一般定理。

M=7 の `10672 < 10996 < 11058` のような具体値はここには置かない。
各 target 層では、候補終点が `lower` 以下または `upper` 以上にしか現れないことを
証明すれば、この一般定理だけで目標一致を否定できる。
-/

namespace Collatz4.Finite

/-- 数 `t` が開区間 `(lower, upper)` の外側にあること。 -/
def OutsideOpenInterval (lower upper t : ℕ) : Prop :=
  t ≤ lower ∨ upper ≤ t

/--
任意の数値族について、全候補が禁止帯の外側にあり、目標値が禁止帯の内部なら
目標値を取る候補は存在しない。
-/
theorem no_index_of_value_gap
    {ι : Type} {value : ι → ℕ} {target lower upper : ℕ}
    (hgap : ∀ i : ι, OutsideOpenInterval lower upper (value i))
    (hlower : lower < target)
    (hupper : target < upper) :
    ¬ ∃ i : ι, value i = target := by
  intro h
  rcases h with ⟨i, hi⟩
  have hg := hgap i
  unfold OutsideOpenInterval at hg
  omega

/--
一般 `ForwardProblem` の最終 2 指数が禁止帯の外側にしか現れず、
目標 2 指数がその内部にあるなら候補は存在しない。
-/
theorem no_candidate_of_t_gap
    {ι : Type} (P : ForwardProblem ι)
    {lower upper : ℕ}
    (hgap : ∀ i : ι,
      OutsideOpenInterval lower upper (P.finalState i).t)
    (hlower : lower < P.targetState.t)
    (hupper : P.targetState.t < upper) :
    ¬ P.Candidate := by
  intro h
  rcases h with ⟨i, hi⟩
  have ht : (P.finalState i).t = P.targetState.t :=
    ForwardProblem.final_t_eq_target_t_of_hit hi
  have hg := hgap i
  unfold OutsideOpenInterval at hg
  omega

/--
禁止帯を `≤ lower ∨ upper ≤` の形で直接与える版。
特殊化側で既にこの形の定理を持っている場合に使いやすい。
-/
theorem no_candidate_of_t_gap'
    {ι : Type} (P : ForwardProblem ι)
    {lower upper : ℕ}
    (hgap : ∀ i : ι,
      (P.finalState i).t ≤ lower ∨ upper ≤ (P.finalState i).t)
    (hlower : lower < P.targetState.t)
    (hupper : P.targetState.t < upper) :
    ¬ P.Candidate := by
  apply no_candidate_of_t_gap P
  · intro i
    exact hgap i
  · exact hlower
  · exact hupper

end Collatz4.Finite
