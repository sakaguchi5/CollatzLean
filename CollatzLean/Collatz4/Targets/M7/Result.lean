import CollatzLean.Collatz4.Finite.Exclusion
import CollatzLean.Collatz4.Targets.M7.Witness
import CollatzLean.Collatz4.Targets.M7.FiniteCertificate
import CollatzLean.Collatz4.Targets.M7.StructuralResult

/-!
# Collatz4.Targets.M7.Result

`M = 7` 個別研究の公開結果をまとめる最終層。

現在は二つの独立な finite exclusion を保持する。

1. 従来証明:
   2179候補の checkpoint / final certificate を `native_decide` で直接確認する。
2. 構造証明:
   `2179 -> 97 -> (58 + 39)` の同期合流圧縮と禁止帯から排除する。

両者は同じ `M7ForwardCandidate` を否定するが、前者は回帰検査、
後者は今後 M を変えて再利用する主構造として位置づける。

`M7MasterWitness` より上流との完全接続については `MasterToWitness` を参照。
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

/-- 従来の直接 finite certificate から得られる M=7 reduced candidate の非存在。 -/
theorem no_reduced_candidate : ¬ problem.Candidate := by
  exact Collatz4.Finite.no_candidate_of_t_certificate problem t_certificate

/--
新しい同期合流圧縮証明から得られる reduced candidate の非存在。
従来の `final_two_exponent_certificate` には依存しない。
-/
theorem no_reduced_candidate_structural : ¬ problem.Candidate := by
  exact no_m7_forward_candidate_via_compression

/-- M=7 の reduced forward candidate は存在しない。従来 certificate 版。 -/
theorem no_m7_forward_candidate : ¬ M7ForwardCandidate := by
  exact no_reduced_candidate

/-- M=7 の reduced forward candidate は存在しない。構造圧縮版。 -/
theorem no_m7_forward_candidate_structural : ¬ M7ForwardCandidate := by
  exact no_m7_forward_candidate_via_compression

/-- 意味論的 M7 witness は存在しない。従来 certificate 版。 -/
theorem no_m7_witness : ¬ HasM7Witness := by
  exact Collatz4.Finite.no_witness_of_reduction
    hasM7Witness_reducesTo
    no_reduced_candidate

/-- 意味論的 M7 witness は存在しない。構造圧縮版。 -/
theorem no_m7_witness_structural : ¬ HasM7Witness := by
  exact no_m7_witness_via_compression

/--
任意のさらに上流の命題 `W` が `HasM7Witness` へ落ちるなら、その `W` も存在しない。
-/
theorem no_source_witness_of_reduction
    {W : Prop}
    (hreduce : W → HasM7Witness) :
    ¬ W := by
  intro hW
  exact no_m7_witness (hreduce hW)

end Collatz4.Targets.M7
