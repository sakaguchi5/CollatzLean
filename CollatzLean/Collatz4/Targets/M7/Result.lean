import CollatzLean.Collatz4.Finite.Exclusion
import CollatzLean.Collatz4.Targets.M7.Witness
import CollatzLean.Collatz4.Targets.M7.FiniteCertificate

/-!
# Collatz4.Targets.M7.Result

`M = 7` 個別研究の公開結果をまとめる最終層。

ここでは

`M7Witness → finite candidate → finite certificate contradiction`

だけを接続する。`M7Witness` より上流、すなわち `Family` / `Parametric` 層の
reachability から `M7Witness` を構成する bridge は、研究対象の定義と分離して追加する。

`M = 7` は `Targets` 配下の一ケースにすぎず、今後 `Targets/M5`, `Targets/M9`, ...
を同じ位置に追加できる。
-/

namespace Collatz4.Targets.M7

open Collatz4.Finite

/-- M=7 の一般前向き有限問題。 -/
abbrev problem := forwardProblem

/-- M=7 finite certificate を一般 `ForwardProblem` の2指数 certificate として読む。 -/
theorem t_certificate :
    ∀ i : Fin candidateCount,
      (problem.finalState i).t ≠ problem.targetState.t := by
  intro i
  simpa [problem, forwardProblem,
    Collatz4.Finite.ForwardProblem.finalState,
    finalState, targetState] using
      (final_two_exponent_certificate i)

/-- 一般 exclusion theorem から得られる M=7 reduced candidate の非存在。 -/
theorem no_reduced_candidate : ¬ problem.Candidate := by
  exact Collatz4.Finite.no_candidate_of_t_certificate problem t_certificate

/-- M=7 の reduced forward candidate は存在しない。 -/
theorem no_m7_forward_candidate : ¬ M7ForwardCandidate := by
  exact no_reduced_candidate

/-- 意味論的 M7 witness は存在しない。 -/
theorem no_m7_witness : ¬ HasM7Witness := by
  exact Collatz4.Finite.no_witness_of_reduction
    hasM7Witness_reducesTo
    no_reduced_candidate

/--
任意のさらに上流の命題 `W` が `HasM7Witness` へ落ちるなら、その `W` も存在しない。

今後、`Parametric` 層の reachability から M=7 witness を構成する bridge はここへ接続する。
-/
theorem no_source_witness_of_reduction
    {W : Prop}
    (hreduce : W → HasM7Witness) :
    ¬ W := by
  intro hW
  exact no_m7_witness (hreduce hW)

end Collatz4.Targets.M7
