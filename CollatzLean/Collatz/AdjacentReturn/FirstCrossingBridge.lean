import CollatzLean.Collatz.AdjacentReturn.FirstCrossingArithmetic
import CollatzLean.Collatz.Selection.Cofinal

/-!
# contracting towerのfirst-crossing bridge

contracting adjacent towerに付けたfirst-crossing長が無限大へ進むことと、
Exact / Late のcofinal二分岐を復元する。
-/

namespace Collatz
namespace AdjacentReturn
namespace ContractingFirstCrossingTower

/-- towerのfirst-crossing長は無限大へ進む。 -/
theorem lengths_tend_to_infinity
    {O : OddOrbit} {T : ContractingTower O}
    (F : ContractingFirstCrossingTower T) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ n : ℕ, J ≤ n → M < F.length n := by
  intro M
  obtain ⟨J, hJ⟩ := T.minima.values_eventually_large (M * 3 ^ M)
  refine ⟨J, ?_⟩
  intro n hn
  by_contra hnot
  have hpLe : F.length n ≤ M := Nat.le_of_not_gt hnot
  have hstartRaw := (F.tower_at n).startValue_le_length_mul_threePow
  have hpow : 3 ^ (F.length n) ≤ 3 ^ M :=
    Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hpLe
  have hbound : F.length n * 3 ^ (F.length n) ≤ M * 3 ^ M :=
    Nat.mul_le_mul hpLe hpow
  have hstartLe : (T.tower_at n).startValue ≤ M * 3 ^ M :=
    le_trans hstartRaw hbound
  have hsel : J ≤ T.select n :=
    le_trans hn (T.select_ge n)
  have hlarge := hJ (T.select n) hsel
  change M * 3 ^ M < O.value (T.minima.index (T.select n)) at hlarge
  change O.value (T.minima.index (T.select n)) ≤ M * 3 ^ M at hstartLe
  omega

/-- exact項かlate項のどちらかがcofinal。 -/
theorem exact_or_late_cofinal
    {O : OddOrbit} {T : ContractingTower O}
    (F : ContractingFirstCrossingTower T) :
    Selection.Cofinal F.ExactAt ∨ Selection.Cofinal F.LateAt := by
  by_cases hExact : Selection.Cofinal F.ExactAt
  · exact Or.inl hExact
  · obtain ⟨N, hN⟩ := Selection.Cofinal.eventually_not_of_not F.ExactAt hExact
    have hLate : Selection.Cofinal F.LateAt := by
      intro M
      let n := max M N
      have hnM : M ≤ n := le_max_left M N
      have hnN : N ≤ n := le_max_right M N
      have hnotExact := hN n hnN
      rcases F.exact_or_late n with hE | hL
      · exact False.elim (hnotExact hE)
      · exact ⟨n, hnM, hL⟩
    exact Or.inr hLate

/-- Exact / Lateのどちらかから狭義単調な無限部分列を明示できる。 -/
theorem exact_or_late_subsequence
    {O : OddOrbit} {T : ContractingTower O}
    (F : ContractingFirstCrossingTower T) :
    (∃ s : ℕ → ℕ, StrictMono s ∧ ∀ n, F.ExactAt (s n)) ∨
      (∃ s : ℕ → ℕ, StrictMono s ∧ ∀ n, F.LateAt (s n)) := by
  classical
  rcases F.exact_or_late_cofinal with hE | hL
  · let s := Selection.Cofinal.select F.ExactAt hE
    exact Or.inl ⟨s, Selection.Cofinal.select_strict F.ExactAt hE,
      Selection.Cofinal.select_spec F.ExactAt hE⟩
  · let s := Selection.Cofinal.select F.LateAt hL
    exact Or.inr ⟨s, Selection.Cofinal.select_strict F.LateAt hL,
      Selection.Cofinal.select_spec F.LateAt hL⟩

end ContractingFirstCrossingTower
end AdjacentReturn
end Collatz
