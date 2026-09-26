import CollatzLean.Collatz4.General.Envelope

/-!
# Collatz4.General.QCutoff

有限領域の certificate と、その外側を一括排除する定理を組み合わせて、
一般の `q ≤ Q` を得る層。

ここでは各特殊化に固有な数値定数を一切使わない。
-/

namespace Collatz4.General

/--
有限領域では `cutoff` 以下であることを検証し、有限領域の外では
admissible 自体が不可能なら、任意の admissible q は `cutoff` 以下。

`native_decide` を使うかどうかは特殊化側の自由であり、この一般定理は
純粋な論理だけを担当する。
-/
theorem q_le_of_finite_cutoff
    {admissible : ℕ → Prop} {searchBound cutoff q : ℕ}
    (hfinite : ∀ i : Fin searchBound, admissible i.1 → i.1 ≤ cutoff)
    (houtside : ∀ n : ℕ, searchBound ≤ n → ¬ admissible n)
    (hq : admissible q) :
    q ≤ cutoff := by
  by_cases hs : q < searchBound
  · exact hfinite ⟨q, hs⟩ hq
  · have hlarge : searchBound ≤ q := Nat.le_of_not_gt hs
    exact False.elim ((houtside q hlarge) hq)

/--
`EnvelopeAdmissible` に対する上の一般 cutoff 定理の直接版。
-/
theorem q_le_of_envelope_finite_cutoff
    {required : ℕ} {envelope residual : ℕ → ℕ}
    {searchBound cutoff q : ℕ}
    (hfinite : ∀ i : Fin searchBound,
      EnvelopeAdmissible required envelope residual i.1 → i.1 ≤ cutoff)
    (houtside : ∀ n : ℕ, searchBound ≤ n →
      ¬ EnvelopeAdmissible required envelope residual n)
    (hq : EnvelopeAdmissible required envelope residual q) :
    q ≤ cutoff := by
  exact q_le_of_finite_cutoff hfinite houtside hq

end Collatz4.General
