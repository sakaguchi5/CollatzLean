import CollatzLean.Collatz4.General.QCutoff
import CollatzLean.Collatz4.M7.Constants

set_option exponentiation.threshold 10996
set_option linter.style.nativeDecide false
/-!
# Collatz4.M7.QBound

m=7 固有の包絡線データを、一般理論 `Collatz4.General` へ代入する特殊化。

`q≤1275` は有限全探索ではなく、

* `gEnvelope` の単調増加性
* `residualTwoExponent` の反単調性
* 境界一点 `q=1276` で既に包絡線が不足すること

から導く。

したがって q-bound の理論から探索上限 `5498` は本質的に不要になる。
旧 API との互換性のため、`finite_q_envelope_cutoff` などは派生定理として残す。
-/

namespace Collatz4.M7

/-- m=7 の包絡線必要条件。一般定義への単なる特殊化。 -/
def qEnvelopeAdmissible (q : ℕ) : Prop :=
  Collatz4.General.EnvelopeAdmissible gStar gEnvelope residualTwoExponent q

/--
q を増やすと残り2指数は増えない。
自然数減算が0に飽和した後も含めて、全自然数上で反単調である。
-/
theorem residualTwoExponent_antitone : Antitone residualTwoExponent := by
  intro a b hab
  simp [residualTwoExponent, targetTwoExponent]
  omega

/-- `q≥1276` なら残り2指数は 8444 以下。 -/
theorem residualTwoExponent_le_8444 {q : ℕ} (hq : 1276 ≤ q) :
    residualTwoExponent q ≤ 8444 := by
  simp [residualTwoExponent, targetTwoExponent]
  omega

/--
`q=1276` 自身は包絡線の大きさだけで `G_*` に届かない。

新しい一般 cutoff 定理では、この境界一点だけが m=7 固有の数値確認になる。
-/
theorem q1276_envelope_too_small :
    gEnvelope (residualTwoExponent 1276) < gStar := by
  decide

/-- 数値境界 `8445 < G_* < 8446` をまとめた形。 -/
theorem gStar_minimum_envelope_boundary :
    gEnvelope 8445 < gStar ∧ gStar < gEnvelope 8446 := by
  exact ⟨envelope_8445_lt_gStar, gStar_lt_envelope_8446⟩

/--
包絡線必要条件を満たす任意の m=7 の q は 1275 以下。

有限領域を走査せず、一般の境界一点 cutoff 定理をそのまま特殊化する。
-/
theorem q_le_1275_of_envelope {q : ℕ} (hq : qEnvelopeAdmissible q) : q ≤ 1275 := by
  exact Collatz4.General.q_le_of_envelope_boundary
    (cutoff := 1275)
    gEnvelope_monotone
    residualTwoExponent_antitone
    (by simpa using q1276_envelope_too_small)
    hq

/--
旧 API との互換用。

以前は `q<5498` の5498点を `native_decide` で走査していたが、
現在は一般境界定理から直ちに従う派生定理であり、有限計算は行わない。
-/
theorem finite_q_envelope_cutoff :
    ∀ q : Fin 5498, qEnvelopeAdmissible q.1 → q.1 ≤ 1275 := by
  intro q hq
  exact q_le_1275_of_envelope hq

/-- `q≥5498` では自然数差として残り2指数が0になる。互換用補助定理。 -/
theorem residualTwoExponent_eq_zero_of_large {q : ℕ} (hq : 5498 ≤ q) :
    residualTwoExponent q = 0 := by
  simp [residualTwoExponent, targetTwoExponent]
  omega

/-- `G_*` は正。互換用補助定理。 -/
theorem gStar_pos : 0 < gStar := by
  decide

/-- 包絡線の0点。互換用補助定理。 -/
theorem gEnvelope_zero : gEnvelope 0 = 0 := by
  decide

/--
有限領域の外側では m=7 の包絡線必要条件自体が不可能。

これも現在は `q≤1275` の一般境界定理から導く派生定理である。
-/
theorem q_envelope_impossible_of_large {q : ℕ} (hq : 5498 ≤ q) :
    ¬ qEnvelopeAdmissible q := by
  intro hadm
  have hcut : q ≤ 1275 := q_le_1275_of_envelope hadm
  omega

end Collatz4.M7
