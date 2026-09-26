import CollatzLean.Collatz4.General.Exclusion
import CollatzLean.Collatz4.M7.Witness
import CollatzLean.Collatz4.M7.FiniteCertificate

/-!
# Collatz4.Specialization.M7

一般理論を m=7 に適用する薄い特殊化層。

現在は

`M7Witness → ResidualData → finite candidate → target hit → finite certificate contradiction`

までが接続されている。
-/

namespace Collatz4.Specialization.M7

/-- m=7 の一般前向き問題。 -/
abbrev problem := Collatz4.M7.forwardProblem

/--
既存の m=7 finite certificate を、一般 `ForwardProblem` の2指数 certificate として読む。
-/
theorem t_certificate :
    ∀ i : Fin Collatz4.M7.candidateCount,
      (problem.finalState i).t ≠ problem.targetState.t := by
  intro i
  simpa [problem, Collatz4.M7.forwardProblem,
    Collatz4.General.ForwardProblem.finalState,
    Collatz4.M7.finalState, Collatz4.M7.targetState] using
      (Collatz4.M7.final_two_exponent_certificate i)

/-- 一般 exclusion theorem から得られる m=7 reduced candidate の非存在。 -/
theorem no_reduced_candidate : ¬ problem.Candidate := by
  exact Collatz4.General.no_candidate_of_t_certificate problem t_certificate

/-- m=7 の従来公開命題へ戻した形。 -/
theorem no_m7_forward_candidate : ¬ Collatz4.M7.M7ForwardCandidate := by
  exact no_reduced_candidate

/--
ユーザーが求めた第三 bridge の特殊化公開版。

意味論的 `M7Witness` があれば必ず reduced candidate が存在する。
-/
theorem forward_candidate_of_m7_witness
    (h : Collatz4.M7.M7Witness) :
    Collatz4.M7.M7ForwardCandidate :=
  h.forward_candidate_of_m7_witness

/--
一般 reduction theorem を使った形でも m=7 witness 非存在を得る。
-/
theorem no_m7_witness : ¬ Collatz4.M7.HasM7Witness := by
  exact Collatz4.General.no_witness_of_reduction
    Collatz4.M7.hasM7Witness_reducesTo
    no_reduced_candidate

/--
任意のさらに原始的な witness `W` が `HasM7Witness` へ落ちるなら、その `W` も存在しない。

今後、指数語・Mersenne block などからの最上流 bridge はこの定理へ接続すればよい。
-/
theorem no_source_witness_of_reduction
    {W : Prop}
    (hreduce : W → Collatz4.M7.HasM7Witness) :
    ¬ W := by
  intro hW
  exact no_m7_witness (hreduce hW)

/--
互換用の一般 API。任意の命題 `W` から直接 finite problem へ reduction があれば排除できる。
-/
theorem no_witness_of_reduction
    {W : Prop}
    (hreduce : Collatz4.General.ReducesTo W problem) :
    ¬ W := by
  exact Collatz4.General.no_witness_of_reduction hreduce no_reduced_candidate

/-- m=7 の包絡線 cutoff は一般 QCutoff の特殊化として公開される。 -/
theorem q_le_1275_of_envelope {q : ℕ}
    (hq : Collatz4.M7.qEnvelopeAdmissible q) : q ≤ 1275 :=
  Collatz4.M7.q_le_1275_of_envelope hq

end Collatz4.Specialization.M7
