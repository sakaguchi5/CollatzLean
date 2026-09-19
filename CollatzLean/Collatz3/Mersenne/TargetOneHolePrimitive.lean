import CollatzLean.Collatz3.Mersenne.TargetOneHoleLocks
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Collatz3 Mersenne: primitive gcd-one branch の局所合同制約

`gcd(q,t)=1` の primitive branch では、base `2^n` を小さい 3 冪法で見るだけで
`n` の residue class がさらに制限される。

* even exit-depth `r=1` では `n` は必ず even。
* odd exit-depth `r=2` では `n ≡ 3 (mod 6)` は不可能。

証明は geometric sum を `x=-1` で評価した

`G_j(-1) = 0  (j even)`
`G_j(-1) = 1  (j odd)`

だけを使う。非零 residue が残る場合は equation と矛盾し、両方 0 なら
`q,t` がともに even となって `gcd(q,t)=1` と矛盾する。
-/

namespace Collatz3
namespace Mersenne

open scoped BigOperators

/-- base の cast が `-1` なら geometric sum の cast は parity だけで決まる。 -/
private theorem targetGeomSum_cast_neg_one
    {m x t : ℕ}
    (hx : (x : ZMod m) = -1) :
    ((targetGeomSum x t : ℕ) : ZMod m) =
      if Even t then 0 else 1 := by
  calc
    ((targetGeomSum x t : ℕ) : ZMod m) =
        ∑ i ∈ Finset.range t, ((x : ZMod m) ^ i) := by
          simp [targetGeomSum]
    _ = ∑ i ∈ Finset.range t, (-1 : ZMod m) ^ i := by rw [hx]
    _ = if Even t then 0 else 1 := by
      exact neg_one_geom_sum

/--
`mod m` で `a^p = 1` なら、
指数 `p*q+r` は `r` まで還元できる。
-/
private theorem natPow_cast_period_reduce
    {m a p q r : ℕ}
    (hPeriod : (a : ZMod m) ^ p = 1) :
    ((a ^ (p * q + r) : ℕ) : ZMod m) =
      (a : ZMod m) ^ r := by
  rw [Nat.cast_pow, pow_add, pow_mul, hPeriod, one_pow, one_mul]

/-- `n` が odd なら `2^n = -1 (mod 3)`。 -/
private theorem twoPow_cast_neg_one_mod_three_of_odd
    {n : ℕ}
    (hn : n % 2 = 1) :
    ((2 ^ n : ℕ) : ZMod 3) = -1 := by
  have hDecomp : n = 2 * (n / 2) + 1 := by
    have h := Nat.mod_add_div n 2
    omega
  rw [hDecomp]
  calc
    ((2 ^ (2 * (n / 2) + 1) : ℕ) : ZMod 3)
        = (2 : ZMod 3) ^ 1 := by
            exact natPow_cast_period_reduce
              (q := n / 2) (r := 1)
              (by decide)
    _ = -1 := by
          decide


/-- `n ≡ 3 (mod 6)` なら `2^n = -1 (mod 9)`。 -/
private theorem twoPow_cast_neg_one_mod_nine_of_mod_six_three
    {n : ℕ}
    (hn : n % 6 = 3) :
    ((2 ^ n : ℕ) : ZMod 9) = -1 := by
  have hDecomp : n = 6 * (n / 6) + 3 := by
    have h := Nat.mod_add_div n 6
    omega
  rw [hDecomp]
  calc
    ((2 ^ (6 * (n / 6) + 3) : ℕ) : ZMod 9)
        = (2 : ZMod 9) ^ 3 := by
            exact natPow_cast_period_reduce
              (q := n / 6) (r := 3)
              (by decide)
    _ = -1 := by
          decide


/-- positive `k` では `3^k = 0 (mod 3)`。 -/
private theorem threePow_cast_zero_mod_three
    {k : ℕ}
    (hk : 0 < k) :
    ((3 ^ k : ℕ) : ZMod 3) = 0 := by
  simpa using
    (ZMod.natCast_pow_eq_zero_of_le
      3 (m := k) (n := 1) (by omega))


/-- `k≥2` では `3^k = 0 (mod 9)`。 -/
private theorem threePow_cast_zero_mod_nine
    {k : ℕ}
    (hk : 2 ≤ k) :
    ((3 ^ k : ℕ) : ZMod 9) = 0 := by
  simpa using
    (ZMod.natCast_pow_eq_zero_of_le
      3 (m := k) (n := 2) hk)
/--
primitive even branch では source width `n` は必ず even。

`n` を odd とすると base は `-1 mod 3`。geometric equation は
`G_q(-1)=2G_t(-1)` となり、唯一可能なのは両方 0、すなわち `q,t` とも even。
これは `gcd(q,t)=1` と矛盾する。
-/
theorem TargetOneHoleGeometricData.even_gcd_one_width_even
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 0 < k)
    (hGcd : Nat.gcd h.q h.t = 1) :
    Even n := by
  rcases Nat.mod_two_eq_zero_or_one n with hnEven | hnOdd
  · apply even_iff_two_dvd.mpr
    exact Nat.dvd_iff_mod_eq_zero.mpr hnEven
  · have hBase : ((2 ^ n : ℕ) : ZMod 3) = -1 :=
      twoPow_cast_neg_one_mod_three_of_odd hnOdd
    have hGq :
        ((targetGeomSum (2 ^ n) h.q : ℕ) : ZMod 3) =
          if Even h.q then 0 else 1 :=
      targetGeomSum_cast_neg_one hBase
    have hGt :
        ((targetGeomSum (2 ^ n) h.t : ℕ) : ZMod 3) =
          if Even h.t then 0 else 1 :=
      targetGeomSum_cast_neg_one hBase
    have hThree : ((3 ^ k : ℕ) : ZMod 3) = 0 :=
      threePow_cast_zero_mod_three hk
    have hEqCast := congrArg (fun z : ℕ => (z : ZMod 3)) h.equation
    simp only [Nat.cast_add, Nat.cast_mul] at hEqCast
    rw [hThree, hGq, hGt] at hEqCast
    norm_num at hEqCast
    have hBoth : Even h.q ∧ Even h.t := by
      by_cases hq : Even h.q
      · by_cases ht : Even h.t
        · exact ⟨hq, ht⟩
        · exfalso
          have hBad : (0 : ZMod 3) = 2 := by
            simpa [hq, ht] using hEqCast
          exact (by decide : (0 : ZMod 3) ≠ 2) hBad
      · by_cases ht : Even h.t
        · exfalso
          have hBad : (1 : ZMod 3) = 0 := by
            simp [hq, ht] at hEqCast
          exact (by decide : (1 : ZMod 3) ≠ 0) hBad
        · exfalso
          have hBad : (1 : ZMod 3) = 2 := by
            simpa [hq, ht] using hEqCast
          exact (by decide : (1 : ZMod 3) ≠ 2) hBad
    have hTwoQ : 2 ∣ h.q := even_iff_two_dvd.mp hBoth.1
    have hTwoT : 2 ∣ h.t := even_iff_two_dvd.mp hBoth.2
    have hTwoGcd : 2 ∣ Nat.gcd h.q h.t := Nat.dvd_gcd hTwoQ hTwoT
    rw [hGcd] at hTwoGcd
    norm_num at hTwoGcd

/-- primitive even branch の剰余表示版。 -/
theorem TargetOneHoleGeometricData.even_gcd_one_width_mod_two_eq_zero
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 0 < k)
    (hGcd : Nat.gcd h.q h.t = 1) :
    n % 2 = 0 := by
  exact Nat.dvd_iff_mod_eq_zero.mp
    (even_iff_two_dvd.mp (h.even_gcd_one_width_even hk hGcd))

/--
primitive odd branch では `n ≡ 3 (mod 6)` は不可能。

この residue class では base は `-1 mod 9`。`k≥2` なら `3^k=0 mod 9` なので
`G_q(-1)=4G_t(-1)`。再び唯一可能なのは `q,t` とも even だが、primitive gcd と矛盾する。
-/
theorem TargetOneHoleGeometricData.odd_gcd_one_width_mod_six_ne_three
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 2 ≤ k)
    (hGcd : Nat.gcd h.q h.t = 1) :
    n % 6 ≠ 3 := by
  intro hnThree
  have hBase : ((2 ^ n : ℕ) : ZMod 9) = -1 :=
    twoPow_cast_neg_one_mod_nine_of_mod_six_three hnThree
  have hGq :
      ((targetGeomSum (2 ^ n) h.q : ℕ) : ZMod 9) =
        if Even h.q then 0 else 1 :=
    targetGeomSum_cast_neg_one hBase
  have hGt :
      ((targetGeomSum (2 ^ n) h.t : ℕ) : ZMod 9) =
        if Even h.t then 0 else 1 :=
    targetGeomSum_cast_neg_one hBase
  have hThree : ((3 ^ k : ℕ) : ZMod 9) = 0 :=
    threePow_cast_zero_mod_nine hk
  have hEqCast := congrArg (fun z : ℕ => (z : ZMod 9)) h.equation
  simp only [Nat.cast_add, Nat.cast_mul] at hEqCast
  rw [hThree, hGq, hGt] at hEqCast
  norm_num at hEqCast
  have hBoth : Even h.q ∧ Even h.t := by
    by_cases hq : Even h.q
    · by_cases ht : Even h.t
      · exact ⟨hq, ht⟩
      · exfalso
        have hBad : (0 : ZMod 9) = 4 := by
          simpa [hq, ht] using hEqCast
        exact (by decide : (0 : ZMod 9) ≠ 4) hBad
    · by_cases ht : Even h.t
      · exfalso
        have hBad : (1 : ZMod 9) = 0 := by
          simpa [hq, ht] using hEqCast
        exact (by decide : (1 : ZMod 9) ≠ 0) hBad
      · exfalso
        have hBad : (1 : ZMod 9) = 4 := by
          simpa [hq, ht] using hEqCast
        exact (by decide : (1 : ZMod 9) ≠ 4) hBad
  have hTwoQ : 2 ∣ h.q := even_iff_two_dvd.mp hBoth.1
  have hTwoT : 2 ∣ h.t := even_iff_two_dvd.mp hBoth.2
  have hTwoGcd : 2 ∣ Nat.gcd h.q h.t := Nat.dvd_gcd hTwoQ hTwoT
  rw [hGcd] at hTwoGcd
  norm_num at hTwoGcd

end Mersenne
end Collatz3
