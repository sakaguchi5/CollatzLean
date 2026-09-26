import CollatzLean.Collatz4.Finite.ValuationGap

/-!
# Collatz4.Finite.RepresentativeCompression

一般 `ForwardProblem` の候補終点を少数の代表終点へ圧縮した後、
代表だけの certificate から元の候補全体を排除する一般層。

このファイルは合流の作り方を知らない。
必要なのは「各候補の finalState が、対応する代表 final state と等しい」ことだけである。
その等式は `Dynamics.MergeCompression` / `ThreePowerCompression` などから供給できる。

したがって Collatz 固有の合流理論と finite exclusion の間の薄い論理 bridge になる。
-/

namespace Collatz4.Finite

/--
`ForwardProblem P` の全候補終点を代表型 `ρ` の終点へ圧縮する certificate。
-/
structure FinalStateCompression
    {ι : Type} (ρ : Type) (P : ForwardProblem ι) where
  representativeFinal : ρ → ForwardState
  representativeOf : ι → ρ
  final_eq_representative : ∀ i : ι,
    P.finalState i = representativeFinal (representativeOf i)

namespace FinalStateCompression

/--
代表終点が性質 `Q` をすべて満たすなら、元候補終点もすべて `Q` を満たす。
-/
theorem final_property_of_representatives
    {ι ρ : Type} {P : ForwardProblem ι}
    (C : FinalStateCompression ρ P)
    (Q : ForwardState → Prop)
    (hrep : ∀ r : ρ, Q (C.representativeFinal r)) :
    ∀ i : ι, Q (P.finalState i) := by
  intro i
  rw [C.final_eq_representative i]
  exact hrep (C.representativeOf i)

/--
代表終点の 2 指数に禁止帯があれば、元候補終点にも同じ禁止帯が成り立つ。
-/
theorem t_gap_of_representatives
    {ι ρ : Type} {P : ForwardProblem ι}
    (C : FinalStateCompression ρ P)
    {lower upper : ℕ}
    (hrep : ∀ r : ρ,
      OutsideOpenInterval lower upper (C.representativeFinal r).t) :
    ∀ i : ι,
      OutsideOpenInterval lower upper (P.finalState i).t := by
  intro i
  rw [C.final_eq_representative i]
  exact hrep (C.representativeOf i)

/--
代表終点だけについて 2 指数禁止帯を証明すれば、
目標2指数が帯の内部にある `ForwardProblem` 全体を一括排除できる。
-/
theorem no_candidate_of_representative_t_gap
    {ι ρ : Type} {P : ForwardProblem ι}
    (C : FinalStateCompression ρ P)
    {lower upper : ℕ}
    (hrep : ∀ r : ρ,
      OutsideOpenInterval lower upper (C.representativeFinal r).t)
    (hlower : lower < P.targetState.t)
    (hupper : P.targetState.t < upper) :
    ¬ P.Candidate := by
  apply no_candidate_of_t_gap P
  · exact C.t_gap_of_representatives hrep
  · exact hlower
  · exact hupper

/--
禁止帯を `≤ lower ∨ upper ≤` の直接形で代表について与える版。
-/
theorem no_candidate_of_representative_t_gap'
    {ι ρ : Type} {P : ForwardProblem ι}
    (C : FinalStateCompression ρ P)
    {lower upper : ℕ}
    (hrep : ∀ r : ρ,
      (C.representativeFinal r).t ≤ lower ∨
        upper ≤ (C.representativeFinal r).t)
    (hlower : lower < P.targetState.t)
    (hupper : P.targetState.t < upper) :
    ¬ P.Candidate := by
  apply C.no_candidate_of_representative_t_gap
  · intro r
    exact hrep r
  · exact hlower
  · exact hupper

end FinalStateCompression

end Collatz4.Finite
