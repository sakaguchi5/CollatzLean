import CollatzLean.Collatz4.M7.ResidualBounds

/-!
# Collatz4.M7.ResidualBridge

q-bound と残余語長 G-bound を finite candidate へ接続する bridge。

現在は

* `qEnvelopeAdmissible q` から `q ≤ 1275`
* 正確な `G_min/G_max` から `4088 ≤ r ≤ 8444`
* r の偶数性から有限候補添字

までが連結されている。

残る意味論的課題は、元の m=7 witness から `ResidualData` を構成することだけである。
-/

namespace Collatz4.M7

/--
包絡線必要条件を満たす q と、許容残余語長 r を同時に finite candidate へ接続する。

低レベル API として残し、`ResidualData.to_candidate_index` が通常の入口になる。
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

namespace ResidualData

/--
正確な residual G-bound を持つデータは、必ず2179候補のどれか一つへ入る。

ここで候補数2179を仮定として使っているわけではなく、
`LengthBound` の interval family から得られる `Fin candidateCount` を返す。
-/
theorem to_candidate_index (d : ResidualData) :
    d.q ≤ 1275 ∧
      ∃ i : Fin candidateCount,
        candidateR i = d.r ∧ candidateN i = targetTime - d.r := by
  exact q_and_residual_bounds_to_candidate
    d.q_admissible d.r_lower d.r_upper d.r_even

/-- 対応する前向き変数 `n = targetTime-r` が有限候補列に現れる。 -/
theorem exists_candidateN (d : ResidualData) :
    ∃ i : Fin candidateCount, candidateN i = targetTime - d.r := by
  rcases d.to_candidate_index with ⟨_, i, _, hiN⟩
  exact ⟨i, hiN⟩

end ResidualData

end Collatz4.M7
