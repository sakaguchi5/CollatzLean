import CollatzLean.Collatz4.General.Envelope

/-!
# Collatz4.General.QCutoff

包絡線必要条件から `q` の上限を得る一般理論。

中心となるのは有限全探索ではなく、次の単調性である。

* `envelope` は残り資源に対して単調増加。
* `residual` は `q` に対して反単調。
* `cutoff + 1` の一点で既に必要量へ届かない。

この三条件だけで、任意の admissible `q` が `cutoff` 以下と分かる。
有限領域を直接 certificate する旧形式も、他の特殊化で使えるよう補助定理として残す。
-/

namespace Collatz4.General

/--
単調増加な包絡線と反単調な残余量を合成すると、`q` に関して反単調になる。

これが「境界一点だけを調べれば、その右側をすべて排除できる」ことの一般的な核である。
-/
theorem envelope_residual_antitone
    {envelope residual : ℕ → ℕ}
    (henvelope : Monotone envelope)
    (hresidual : Antitone residual) :
    Antitone (fun q => envelope (residual q)) := by
  intro a b hab
  exact henvelope (hresidual hab)

/--
包絡線 cutoff の一般定理。

`cutoff + 1` の時点で包絡線値が必要量 `required` より小さく、
さらに `envelope (residual q)` が `q` に関して反単調なら、
包絡線必要条件を満たすすべての `q` は `cutoff` 以下である。

各 m の特殊化では、有限区間全体を走査する必要はなく、
境界一点の不等式だけを確認すればよい。
-/
theorem q_le_of_envelope_boundary
    {required : ℕ}
    {envelope residual : ℕ → ℕ}
    {cutoff q : ℕ}
    (henvelope : Monotone envelope)
    (hresidual : Antitone residual)
    (hboundary : envelope (residual (cutoff + 1)) < required)
    (hq : EnvelopeAdmissible required envelope residual q) :
    q ≤ cutoff := by
  by_contra hle
  have hlarge : cutoff + 1 ≤ q := by
    omega
  have hanti : Antitone (fun n => envelope (residual n)) :=
    envelope_residual_antitone henvelope hresidual
  have hupper : envelope (residual q) ≤ envelope (residual (cutoff + 1)) :=
    hanti hlarge
  unfold EnvelopeAdmissible at hq
  omega

/--
有限領域では `cutoff` 以下であることを検証し、有限領域の外では
admissible 自体が不可能なら、任意の admissible q は `cutoff` 以下。

境界一点の単調性を利用できない別の特殊化のために残す一般補助定理。
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
`EnvelopeAdmissible` に対する有限 cutoff 定理の直接版。
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
