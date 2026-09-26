import CollatzLean.Collatz4.M7.LengthBound

/-!
# Collatz4.M7.ResidualBridge

q-bound と残余語長 bound を finite candidate へ接続する薄い bridge。

ここでは依存関係を正確に保つ。

* `qEnvelopeAdmissible q` から `q ≤ 1275` は一般 QCutoff 理論で得る。
* `4088 ≤ r ≤ 8444` と r 偶数から finite candidate index を得る。
* `q ≤ 1275` だけから r の範囲を導くことはしない。

今後、残余語の G-bound から `r` の上下限を証明すれば、
その定理をこの bridge の `hlo/hhi/heven` にそのまま渡せる。
-/

namespace Collatz4.M7

/--
包絡線必要条件を満たす q と、許容残余語長 r を同時に finite candidate へ接続する。

返り値には q の cutoff と、対応候補添字の両方を含める。
-/
theorem q_and_residual_bounds_to_candidate
    {q r : ℕ}
    (hq : qEnvelopeAdmissible q)
    (hlo : 4088 ≤ r)
    (hhi : r ≤ 8444)
    (heven : r % 2 = 0) :
    q ≤ 1275 ∧
      ∃ i : Fin candidateCount,
        candidateR i = r ∧ candidateN i = targetTime - r := by
  refine ⟨q_le_1275_of_envelope hq, ?_⟩
  exact exists_candidate_of_residual_bounds_even hlo hhi heven

end Collatz4.M7
