import CollatzLean.Collatz4.General.Exclusion
import CollatzLean.Collatz4.M7.QBound
import CollatzLean.Collatz4.M7.FiniteCertificate

/-!
# Collatz4.Specialization.M7

一般理論を m=7 に適用する薄い特殊化層。

このファイルの役割は新しい計算をすることではなく、m=7 固有 certificate を
一般 exclusion theorem へ渡すことだけである。
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

/--
一般 exclusion theorem から得られる m=7 reduced candidate の非存在。
-/
theorem no_reduced_candidate : ¬ problem.Candidate := by
  exact Collatz4.General.no_candidate_of_t_certificate problem t_certificate

/-- m=7 の従来公開命題へ戻した形。 -/
theorem no_m7_forward_candidate : ¬ Collatz4.M7.M7ForwardCandidate := by
  exact no_reduced_candidate

/--
将来、元の m=7 witness `W` から `problem.Candidate` への bridge を証明したら、
その bridge だけで直ちに `¬ W` が得られる。

この定理により finite certificate 側を今後触り直す必要がない。
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
