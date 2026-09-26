import CollatzLean.Collatz4.Core.Normalization
import CollatzLean.Collatz4.Specialization.M7

/-!
# Collatz4.M7.Exclusion

既存 API を保つための互換層。

実際の排除論理は `Collatz4.General.Exclusion`、m=7 への適用は
`Collatz4.Specialization.M7` に置き、このファイルでは従来名だけを公開する。
-/

namespace Collatz4.M7

/-- 一般 exclusion theorem を m=7 に特殊化して得た reduced candidate の非存在。 -/
theorem no_m7_forward_candidate : ¬ M7ForwardCandidate :=
  Collatz4.Specialization.M7.no_m7_forward_candidate

/-- 同内容を存在量化を展開した従来形式でも公開する。 -/
theorem no_m7_target_hit :
    ¬ ∃ i : Fin candidateCount, finalState i = targetState := by
  intro h
  exact no_m7_forward_candidate ((m7ForwardCandidate_iff).2 h)

/-- 短い従来公開名。 -/
theorem no_m7_candidate : ¬ M7ForwardCandidate :=
  no_m7_forward_candidate

end Collatz4.M7
