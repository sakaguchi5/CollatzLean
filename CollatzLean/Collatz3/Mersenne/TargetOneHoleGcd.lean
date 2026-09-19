import CollatzLean.Collatz3.Mersenne.TargetOneHoleValuation
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum


/-!
# Collatz3 Mersenne: target-one の gcd reduction

二つの geometric length `q,t` が非自明な共通因子 `d` を持つなら、
`G_d(2^n)` は `G_q(2^n)` と `G_t(2^n)` の両方を割る。
したがって geometric equation から `G_d(2^n) ∣ 3^k`。

3 が素数なので `G_d(2^n)=3^a` となり、これは既存 no-hole equation へ戻る。
no-hole 完全分類と `n≥3,d>1` を衝突させると唯一

`n=3, d=2`

だけが残る。

このファイルでは新しい structure は導入せず、すべて derived theorem とする。
-/

namespace Collatz3
namespace Mersenne

/-- `x≥2`, `d≥2` なら geometric sum は 1 より大きい。 -/
private theorem one_lt_targetGeomSum
    {x d : ℕ}
    (hx : 2 ≤ x)
    (hd : 2 ≤ d) :
    1 < targetGeomSum x d := by
  have hdEq : d = 2 + (d - 2) := by omega
  rw [hdEq, targetGeomSum_add]
  have hG2 : targetGeomSum x 2 = x + 1 := by
    simp [targetGeomSum]
  rw [hG2]
  omega

/--
`d=gcd(q,t)` に対応する geometric sum は `3^k` を割る。
-/
theorem TargetOneHoleGeometricData.gcdGeomSum_dvd_threePow
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b) :
    targetGeomSum (2 ^ n) (Nat.gcd h.q h.t) ∣ 3 ^ k := by
  let d : ℕ := Nat.gcd h.q h.t
  have hdq : d ∣ h.q := by
    dsimp [d]
    exact Nat.gcd_dvd_left h.q h.t
  have hdt : d ∣ h.t := by
    dsimp [d]
    exact Nat.gcd_dvd_right h.q h.t
  have hGq :
      targetGeomSum (2 ^ n) d ∣ targetGeomSum (2 ^ n) h.q :=
    targetGeomSum_dvd_of_dvd (2 ^ n) hdq
  have hGt :
      targetGeomSum (2 ^ n) d ∣ targetGeomSum (2 ^ n) h.t :=
    targetGeomSum_dvd_of_dvd (2 ^ n) hdt
  have hRhs :
      targetGeomSum (2 ^ n) d ∣
        2 ^ r * targetGeomSum (2 ^ n) h.t :=
    dvd_mul_of_dvd_right hGt _
  have hSum :
      targetGeomSum (2 ^ n) d ∣
        3 ^ k + targetGeomSum (2 ^ n) h.q := by
    rw [h.equation]
    exact hRhs
  exact (Nat.dvd_add_iff_left hGq).mpr hSum

/--
非自明 gcd は no-hole 完全分類により `n=3, gcd(q,t)=2` を強制する。
-/
theorem TargetOneHoleGeometricData.gcd_gt_one_forces_three_two
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn : 3 ≤ n)
    (hGcd : 1 < Nat.gcd h.q h.t) :
    n = 3 ∧ Nat.gcd h.q h.t = 2 := by
  let d : ℕ := Nat.gcd h.q h.t
  have hdTwo : 2 ≤ d := by
    dsimp [d]
    omega
  have hDvd : targetGeomSum (2 ^ n) d ∣ 3 ^ k := by
    simpa [d] using h.gcdGeomSum_dvd_threePow
  rcases (Nat.dvd_prime_pow Nat.prime_three).mp hDvd with
    ⟨a, haLe, hGa⟩
  have hx : 2 ≤ 2 ^ n := by
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ n)
    norm_num at hp ⊢
    exact hp
  have hGgt : 1 < targetGeomSum (2 ^ n) d :=
    one_lt_targetGeomSum hx hdTwo
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
            _ ≤ n * d := Nat.mul_le_mul hn hdTwo
        omega)
      hNo
  rcases hClass with h1 | h2 | h3 | h4
  · rcases h1 with ⟨ha, hn1, _, _⟩
    omega
  · rcases h2 with ⟨ha, hn2, _, _⟩
    omega
  · rcases h3 with ⟨ha, hn1, _, _⟩
    omega
  · rcases h4 with ⟨ha, hn3, _, hLen⟩
    subst n
    have hd : d = 2 := by
      norm_num at hLen
      omega
    exact ⟨rfl, by simpa [d] using hd⟩

/--
`n≥3` では gcd は 1、または唯一の exceptional shape `(n,d)=(3,2)`。
-/
theorem TargetOneHoleGeometricData.gcd_dichotomy
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn : 3 ≤ n) :
    Nat.gcd h.q h.t = 1 ∨
      (n = 3 ∧ Nat.gcd h.q h.t = 2) := by
  have hGcdPos : 0 < Nat.gcd h.q h.t :=
    Nat.gcd_pos_of_pos_left h.t h.q_pos
  by_cases hOne : Nat.gcd h.q h.t = 1
  · exact Or.inl hOne
  · have hGt : 1 < Nat.gcd h.q h.t := by omega
    exact Or.inr (h.gcd_gt_one_forces_three_two hn hGt)

end Mersenne
end Collatz3
