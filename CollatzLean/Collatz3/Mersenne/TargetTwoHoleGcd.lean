import CollatzLean.Collatz3.Mersenne.GeometricSum
import CollatzLean.Collatz3.Mersenne.TargetTwoHoleGeometric
import CollatzLean.Collatz3.Mersenne.TwoAdicArithmetic
import CollatzLean.Collatz3.Mersenne.TargetOneHoleGcd
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum


/-!
# Collatz3 Mersenne: target-two triple-gcd reduction

三つの geometric length `q,u,t` の共通因子 `d` が非自明なら、
`G_d(2^n)` は geometric equation の全 block を割る。
no-hole 完全分類へ戻すと `n=3,d=2` だけが候補なので、
現在の target-two geometric layer `n≥4` では triple gcd は必ず 1。
-/

namespace Collatz3
namespace Mersenne

/-- target-two で使う三長さの gcd。 -/
def targetTwoTripleGcd (q u t : ℕ) : ℕ :=
  Nat.gcd q (Nat.gcd u t)

private theorem targetTwoTripleGcd_dvd_left (q u t : ℕ) :
    targetTwoTripleGcd q u t ∣ q := by
  exact Nat.gcd_dvd_left _ _

private theorem targetTwoTripleGcd_dvd_middle (q u t : ℕ) :
    targetTwoTripleGcd q u t ∣ u := by
  exact dvd_trans (Nat.gcd_dvd_right q (Nat.gcd u t))
    (Nat.gcd_dvd_left u t)

private theorem targetTwoTripleGcd_dvd_right (q u t : ℕ) :
    targetTwoTripleGcd q u t ∣ t := by
  exact dvd_trans (Nat.gcd_dvd_right q (Nat.gcd u t))
    (Nat.gcd_dvd_right u t)

private theorem targetTwo_nontrivial_geomSum_forces_three_two
    {k n d : ℕ}
    (hn : 3 ≤ n)
    (hd : 1 < d)
    (hDvd : targetGeomSum (2 ^ n) d ∣ 3 ^ k) :
    n = 3 ∧ d = 2 := by
  rcases (Nat.dvd_prime_pow Nat.prime_three).mp hDvd with
    ⟨a, _haLe, hGa⟩
  have hx : 2 ≤ 2 ^ n := by
    have hp := Nat.pow_le_pow_right
      (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ n)
    norm_num at hp ⊢
    exact hp
  have hGgt : 1 < targetGeomSum (2 ^ n) d :=
    one_lt_targetGeomSum hx (by omega)
  have haPos : 0 < a := by
    by_contra hNot
    have ha0 : a = 0 := by omega
    rw [ha0] at hGa
    norm_num at hGa
    omega
  have hNo : NoHoleEquation a n 1 (n * d - 1) :=
    noHole_of_targetGeomSum_eq_threePow
      (a := a) (n := n) (t := d)
      (by omega) (by omega) hGa
  have hClass :=
    noHoleCompleteClassification
      a n 1 (n * d - 1)
      haPos (by omega) (by norm_num)
      (by
        have hndSix : 6 ≤ n * d := by
          calc
            6 = 3 * 2 := by norm_num
            _ ≤ n * d := Nat.mul_le_mul hn (by omega)
        omega)
      hNo
  rcases hClass with h1 | h2 | h3 | h4
  · rcases h1 with ⟨_, hn1, _, _⟩
    omega
  · rcases h2 with ⟨_, hn2, _, _⟩
    omega
  · rcases h3 with ⟨_, hn1, _, _⟩
    omega
  · rcases h4 with ⟨_, hn3, _, hLen⟩
    subst n
    norm_num at hLen
    exact ⟨rfl, by omega⟩

/-- wrapped phase では triple-gcd geometric sum が `3^k` を割る。 -/
theorem TargetTwoHoleWrappedGeometricData.gcdGeomSum_dvd_threePow
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b) :
    targetGeomSum (2 ^ n) (targetTwoTripleGcd h.q h.u h.t) ∣ 3 ^ k := by
  let d := targetTwoTripleGcd h.q h.u h.t
  have hGq : targetGeomSum (2 ^ n) d ∣ targetGeomSum (2 ^ n) h.q :=
    targetGeomSum_dvd_of_dvd _ (targetTwoTripleGcd_dvd_left _ _ _)
  have hGu : targetGeomSum (2 ^ n) d ∣ targetGeomSum (2 ^ n) h.u :=
    targetGeomSum_dvd_of_dvd _ (targetTwoTripleGcd_dvd_middle _ _ _)
  have hGt : targetGeomSum (2 ^ n) d ∣ targetGeomSum (2 ^ n) h.t :=
    targetGeomSum_dvd_of_dvd _ (targetTwoTripleGcd_dvd_right _ _ _)
  have hRhs : targetGeomSum (2 ^ n) d ∣
      2 ^ (r + 1) * targetGeomSum (2 ^ n) h.t :=
    dvd_mul_of_dvd_right hGt _
  have hAll : targetGeomSum (2 ^ n) d ∣
      2 * 3 ^ k + targetGeomSum (2 ^ n) h.q + targetGeomSum (2 ^ n) h.u := by
    rw [h.equation]
    exact hRhs
  have hTwoThree : targetGeomSum (2 ^ n) d ∣ 2 * 3 ^ k := by
    have h12 : targetGeomSum (2 ^ n) d ∣
        2 * 3 ^ k + targetGeomSum (2 ^ n) h.q :=
      (Nat.dvd_add_iff_left hGu).mpr hAll
    exact (Nat.dvd_add_iff_left hGq).mpr h12
  have hdPos : 0 < d := by
    dsimp [d, targetTwoTripleGcd]
    exact Nat.gcd_pos_of_pos_left _ h.q_pos
  have hnPos : 0 < n := by
    have hphase := h.a_phase_eq
    by_contra hNot
    have hn0 : n = 0 := by
      omega
    have hMulZero : n * h.q = 0 := by
      calc
        n * h.q = 0 * h.q := by
          exact congrArg (fun z : ℕ => z * h.q) hn0
        _ = 0 := by
          simp
    have hphaseZero :
        a + r + 1 = 0 := by
      exact hphase.trans hMulZero
    omega
  have hOdd : Odd (targetGeomSum (2 ^ n) d) := by
    apply targetGeomSum_odd_of_even_base
    · exact twoPow_even_of_pos hnPos
    · exact hdPos
  have hCoprime : (targetGeomSum (2 ^ n) d).Coprime 2 :=
    hOdd.coprime_two_right
  exact hCoprime.dvd_of_dvd_mul_left hTwoThree

/-- split-forward phase でも triple-gcd geometric sum が `3^k` を割る。 -/
theorem TargetTwoHoleSplitForwardGeometricData.gcdGeomSum_dvd_threePow
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b) :
    targetGeomSum (2 ^ n) (targetTwoTripleGcd h.q h.u h.t) ∣ 3 ^ k := by
  let d := targetTwoTripleGcd h.q h.u h.t
  have hGq := targetGeomSum_dvd_of_dvd (2 ^ n)
    (targetTwoTripleGcd_dvd_left h.q h.u h.t)
  have hGu := targetGeomSum_dvd_of_dvd (2 ^ n)
    (targetTwoTripleGcd_dvd_middle h.q h.u h.t)
  have hGt := targetGeomSum_dvd_of_dvd (2 ^ n)
    (targetTwoTripleGcd_dvd_right h.q h.u h.t)
  have hRhs : targetGeomSum (2 ^ n) d ∣
      2 ^ (r + 1) * targetGeomSum (2 ^ n) h.t :=
    dvd_mul_of_dvd_right hGt _
  have hAll : targetGeomSum (2 ^ n) d ∣
      3 ^ k + targetGeomSum (2 ^ n) h.q +
        2 ^ r * targetGeomSum (2 ^ n) h.u := by
    rw [h.equation]
    exact hRhs
  have hGuR : targetGeomSum (2 ^ n) d ∣
      2 ^ r * targetGeomSum (2 ^ n) h.u :=
    dvd_mul_of_dvd_right hGu _
  have h12 : targetGeomSum (2 ^ n) d ∣
      3 ^ k + targetGeomSum (2 ^ n) h.q :=
    (Nat.dvd_add_iff_left hGuR).mpr hAll
  exact (Nat.dvd_add_iff_left hGq).mpr h12

/-- split-reverse は同じ geometric equation なので同じ gcd reduction。 -/
theorem TargetTwoHoleSplitReverseGeometricData.gcdGeomSum_dvd_threePow
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b) :
    targetGeomSum (2 ^ n) (targetTwoTripleGcd h.q h.u h.t) ∣ 3 ^ k := by
  let d := targetTwoTripleGcd h.q h.u h.t
  have hGq := targetGeomSum_dvd_of_dvd (2 ^ n)
    (targetTwoTripleGcd_dvd_left h.q h.u h.t)
  have hGu := targetGeomSum_dvd_of_dvd (2 ^ n)
    (targetTwoTripleGcd_dvd_middle h.q h.u h.t)
  have hGt := targetGeomSum_dvd_of_dvd (2 ^ n)
    (targetTwoTripleGcd_dvd_right h.q h.u h.t)
  have hRhs : targetGeomSum (2 ^ n) d ∣
      2 ^ (r + 1) * targetGeomSum (2 ^ n) h.t :=
    dvd_mul_of_dvd_right hGt _
  have hAll : targetGeomSum (2 ^ n) d ∣
      3 ^ k + targetGeomSum (2 ^ n) h.q +
        2 ^ r * targetGeomSum (2 ^ n) h.u := by
    rw [h.equation]
    exact hRhs
  have hGuR : targetGeomSum (2 ^ n) d ∣
      2 ^ r * targetGeomSum (2 ^ n) h.u :=
    dvd_mul_of_dvd_right hGu _
  have h12 : targetGeomSum (2 ^ n) d ∣
      3 ^ k + targetGeomSum (2 ^ n) h.q :=
    (Nat.dvd_add_iff_left hGuR).mpr hAll
  exact (Nat.dvd_add_iff_left hGq).mpr h12

/-- wrapped phase, `n≥4` なら triple gcd は 1。 -/
theorem TargetTwoHoleWrappedGeometricData.tripleGcd_eq_one
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b)
    (hn4 : 4 ≤ n) :
    targetTwoTripleGcd h.q h.u h.t = 1 := by
  have hPos : 0 < targetTwoTripleGcd h.q h.u h.t := by
    exact Nat.gcd_pos_of_pos_left _ h.q_pos
  by_contra hNe
  have hGt : 1 < targetTwoTripleGcd h.q h.u h.t := by omega
  have hForce := targetTwo_nontrivial_geomSum_forces_three_two
    (k := k) (n := n) (d := targetTwoTripleGcd h.q h.u h.t)
    (by omega) hGt h.gcdGeomSum_dvd_threePow
  omega

/-- split-forward phase, `n≥4` なら triple gcd は 1。 -/
theorem TargetTwoHoleSplitForwardGeometricData.tripleGcd_eq_one
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b)
    (hn4 : 4 ≤ n) :
    targetTwoTripleGcd h.q h.u h.t = 1 := by
  have hPos : 0 < targetTwoTripleGcd h.q h.u h.t := by
    exact Nat.gcd_pos_of_pos_left _ h.q_pos
  by_contra hNe
  have hGt : 1 < targetTwoTripleGcd h.q h.u h.t := by omega
  have hForce := targetTwo_nontrivial_geomSum_forces_three_two
    (k := k) (n := n) (d := targetTwoTripleGcd h.q h.u h.t)
    (by omega) hGt h.gcdGeomSum_dvd_threePow
  omega

/-- split-reverse phase, `n≥4` なら triple gcd は 1。 -/
theorem TargetTwoHoleSplitReverseGeometricData.tripleGcd_eq_one
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b)
    (hn4 : 4 ≤ n) :
    targetTwoTripleGcd h.q h.u h.t = 1 := by
  have hPos : 0 < targetTwoTripleGcd h.q h.u h.t := by
    exact Nat.gcd_pos_of_pos_left _ h.q_pos
  by_contra hNe
  have hGt : 1 < targetTwoTripleGcd h.q h.u h.t := by omega
  have hForce := targetTwo_nontrivial_geomSum_forces_three_two
    (k := k) (n := n) (d := targetTwoTripleGcd h.q h.u h.t)
    (by omega) hGt h.gcdGeomSum_dvd_threePow
  omega

end Mersenne
end Collatz3
