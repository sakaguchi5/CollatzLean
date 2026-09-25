import CollatzLean.Collatz4.M7.Constants

set_option exponentiation.threshold 10996
set_option linter.style.nativeDecide false
/-!
# Collatz4.M7.QBound

`q=1275/1276` の切替を独立ファイルに隔離する。

主有限証明は `n` の前向き系だけで完結するが、m=7 の候補生成側で
`q≤1275` が探索上限ではなく包絡線条件から来ることも、この層で検証する。
-/

namespace Collatz4.M7

/-- `G_*` が、その `q` に残された2指数の包絡線以下であるという必要条件。 -/
def qEnvelopeAdmissible (q : ℕ) : Prop :=
  gStar ≤ gEnvelope (residualTwoExponent q)

/-- `q≥1276` なら残り2指数は 8444 以下。 -/
theorem residualTwoExponent_le_8444 {q : ℕ} (hq : 1276 ≤ q) :
    residualTwoExponent q ≤ 8444 := by
  simp [residualTwoExponent, targetTwoExponent]
  omega

/-- `q=1276` 自身は包絡線の大きさだけで `G_*` に届かない。 -/
theorem q1276_envelope_too_small :
    gEnvelope (residualTwoExponent 1276) < gStar := by
  decide

/-- 数値境界 `8445 < G_* < 8446` をまとめた形。 -/
theorem gStar_minimum_envelope_boundary :
    gEnvelope 8445 < gStar ∧ gStar < gEnvelope 8446 := by
  exact ⟨envelope_8445_lt_gStar, gStar_lt_envelope_8446⟩

/-- `q≥5498` では自然数差として残り2指数が0になる。 -/
theorem residualTwoExponent_eq_zero_of_large {q : ℕ} (hq : 5498 ≤ q) :
    residualTwoExponent q = 0 := by
  simp [residualTwoExponent, targetTwoExponent]
  omega

/-- `G_*` は正。 -/
theorem gStar_pos : 0 < gStar := by
  decide

/-- 包絡線の0点。 -/
theorem gEnvelope_zero : gEnvelope 0 = 0 := by
  decide

/--
`q<5498` の有限領域について、包絡線必要条件を満たすなら `q≤1275`。

ここは巨大候補表を埋め込まず、定義から native に再計算する。
-/
theorem finite_q_envelope_cutoff :
    ∀ q : Fin 5498, qEnvelopeAdmissible q.1 → q.1 ≤ 1275 := by
  simp only [qEnvelopeAdmissible]
  native_decide

/--
包絡線必要条件を満たす任意の `q` は `1275` 以下。
したがって `q≥1276` は一括して排除される。
-/
theorem q_le_1275_of_envelope {q : ℕ} (hq : qEnvelopeAdmissible q) : q ≤ 1275 := by
  by_cases hs : q < 5498
  · exact finite_q_envelope_cutoff ⟨q, hs⟩ hq
  · have hlarge : 5498 ≤ q := by omega
    have hz : residualTwoExponent q = 0 :=
      residualTwoExponent_eq_zero_of_large hlarge
    unfold qEnvelopeAdmissible at hq
    rw [hz, gEnvelope_zero] at hq
    have hg := gStar_pos
    omega

end Collatz4.M7
