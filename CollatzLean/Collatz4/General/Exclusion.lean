import CollatzLean.Collatz4.General.FiniteReduction

/-!
# Collatz4.General.Exclusion

有限 certificate から候補非存在を得る一般主定理。

m=7 で本当に固有であるべきなのは `hcert` の計算結果だけであり、
そこから非存在を導く論理はこのファイルに固定する。
-/

namespace Collatz4.General

/--
全候補で最終2指数が目標2指数と異なるなら、目標状態への一致は不可能。
-/
theorem no_candidate_of_t_certificate
    {ι : Type} (P : ForwardProblem ι)
    (hcert : ∀ i : ι, (P.finalState i).t ≠ P.targetState.t) :
    ¬ P.Candidate := by
  intro h
  rcases h with ⟨i, hi⟩
  exact hcert i (ForwardProblem.final_t_eq_target_t_of_hit hi)

/--
奇数部分についての certificate だけでも同様に候補を排除できる。
-/
theorem no_candidate_of_u_certificate
    {ι : Type} (P : ForwardProblem ι)
    (hcert : ∀ i : ι, (P.finalState i).u ≠ P.targetState.u) :
    ¬ P.Candidate := by
  intro h
  rcases h with ⟨i, hi⟩
  exact hcert i (ForwardProblem.final_u_eq_target_u_of_hit hi)

/--
一般 witness から有限候補への reduction と、2指数 certificate を合成した主定理。
-/
theorem no_witness_of_t_certificate
    {ι : Type} {W : Prop} (P : ForwardProblem ι)
    (hreduce : ReducesTo W P)
    (hcert : ∀ i : ι, (P.finalState i).t ≠ P.targetState.t) :
    ¬ W := by
  exact no_witness_of_reduction hreduce (no_candidate_of_t_certificate P hcert)

end Collatz4.General
