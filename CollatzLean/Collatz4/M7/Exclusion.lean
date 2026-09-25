import CollatzLean.Collatz4.Core.Normalization
import CollatzLean.Collatz4.M7.QBound
import CollatzLean.Collatz4.M7.FiniteCertificate

/-!
# Collatz4.M7.Exclusion

前向き有限 certificate を最終 m=7 reduced theorem へ接続する。
-/

namespace Collatz4.M7

/--
Collatz4 の reduced m=7 候補は存在しない。

等号 `finalState i = targetState` が成立すれば双方の `t` 成分も等しいが、
有限 certificate は全2179候補でそれを否定する。
-/
theorem no_m7_forward_candidate : ¬ M7ForwardCandidate := by
  intro h
  rcases h with ⟨i, hi⟩
  have ht : (finalState i).t = targetTwoExponent := by
    simpa [targetState] using congrArg ForwardState.t hi
  exact (final_two_exponent_certificate i) ht

/-- 同内容を存在量化を展開した形でも公開する。 -/
theorem no_m7_target_hit :
    ¬ ∃ i : Fin candidateCount, finalState i = targetState :=
  no_m7_forward_candidate

/-- 短い公開名。Collatz4 内でいう `m=7` reduced candidate の非存在。 -/
theorem no_m7_candidate : ¬ M7ForwardCandidate :=
  no_m7_forward_candidate

end Collatz4.M7
