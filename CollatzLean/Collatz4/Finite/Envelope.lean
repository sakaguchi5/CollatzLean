import CollatzLean.Collatz4.Finite.Forward

/-!
# Collatz4.Finite.Envelope

m に依存しない包絡線条件の最小語彙。

`required` は到達に必要な量、`residual q` は q を固定した後に残る資源、
`envelope` はその資源から作れる量の上界を表す。

m=7 の `G_*`, `residualTwoExponent`, `gEnvelope` は、この一般定義への
単なる代入として扱う。
-/

namespace Collatz4.Finite

/--
`q` が包絡線による必要条件を満たすことを表す。

この定義自体には Collatz 固有の数値を一切含めない。
-/
def EnvelopeAdmissible
    (required : ℕ) (envelope residual : ℕ → ℕ) (q : ℕ) : Prop :=
  required ≤ envelope (residual q)

/-- 包絡線値が必要量より小さければ、その q は admissible ではない。 -/
theorem not_envelopeAdmissible_of_lt
    {required : ℕ} {envelope residual : ℕ → ℕ} {q : ℕ}
    (h : envelope (residual q) < required) :
    ¬ EnvelopeAdmissible required envelope residual q := by
  intro hq
  exact (Nat.not_le_of_lt h) hq

end Collatz4.Finite
