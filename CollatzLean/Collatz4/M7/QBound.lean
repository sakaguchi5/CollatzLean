import CollatzLean.Collatz4.General.QCutoff
import CollatzLean.Collatz4.M7.Constants

set_option exponentiation.threshold 10996
set_option linter.style.nativeDecide false
/-!
# Collatz4.M7.QBound

m=7 固有の包絡線データを、一般理論 `Collatz4.General` へ代入する特殊化。

`q≤1275` の論理骨格は General.QCutoff 側にあり、このファイルに残るのは
m=7 固有定数と有限 certificate だけである。
-/

namespace Collatz4.M7

/-- m=7 の包絡線必要条件。一般定義への単なる特殊化。 -/
def qEnvelopeAdmissible (q : ℕ) : Prop :=
  Collatz4.General.EnvelopeAdmissible gStar gEnvelope residualTwoExponent q

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
`q<5498` の有限領域について、m=7 の包絡線必要条件を満たすなら `q≤1275`。

ここだけが m=7 固有の有限計算。
-/
theorem finite_q_envelope_cutoff :
    ∀ q : Fin 5498, qEnvelopeAdmissible q.1 → q.1 ≤ 1275 := by
  simp only [qEnvelopeAdmissible, Collatz4.General.EnvelopeAdmissible]
  native_decide

/-- 有限領域の外側では m=7 の包絡線必要条件自体が不可能。 -/
theorem q_envelope_impossible_of_large {q : ℕ} (hq : 5498 ≤ q) :
    ¬ qEnvelopeAdmissible q := by
  intro hadm
  have hz : residualTwoExponent q = 0 :=
    residualTwoExponent_eq_zero_of_large hq
  unfold qEnvelopeAdmissible Collatz4.General.EnvelopeAdmissible at hadm
  rw [hz, gEnvelope_zero] at hadm
  have hg := gStar_pos
  omega

/--
包絡線必要条件を満たす任意の m=7 の q は 1275 以下。

一般 cutoff 定理に m=7 の二つの certificate を渡すだけで得る。
-/
theorem q_le_1275_of_envelope {q : ℕ} (hq : qEnvelopeAdmissible q) : q ≤ 1275 := by
  exact Collatz4.General.q_le_of_finite_cutoff
    finite_q_envelope_cutoff
    (fun n hn => q_envelope_impossible_of_large hn)
    hq

end Collatz4.M7
