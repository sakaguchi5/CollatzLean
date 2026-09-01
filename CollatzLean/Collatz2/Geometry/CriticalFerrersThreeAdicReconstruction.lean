import CollatzLean.Collatz2.Geometry.CriticalFerrersThreeAdicRange
import Mathlib.Tactic.IntervalCases


/-!
# Collatz2 Geometry: anchored 3進 code の有限復元

二つの valid FirstCrossing word が同じ `(r,H)` を持つとする。

* 幾何から code 差は 4 の倍数。
* 3進 code の一致から code 差は `3^(r+s)` の倍数。
* したがって差は `4 * 3^(r+s)` の倍数。
* 一方、critical width がそれより小さければ非零差は存在できない。

よって `affineConst` が一致し、既存の lossless triple theorem から word 自体が一致する。
-/

namespace Collatz2
namespace Word

/-- 4 と 3冪の両方で割れる整数は、その積でも割れる。 -/
theorem four_mul_threePow_dvd_of_both
    {N : ℕ}
    {z : ℤ}
    (h4 : (4 : ℤ) ∣ z)
    (h3 : (3 : ℤ) ^ N ∣ z) :
    ((4 : ℤ) * (3 : ℤ) ^ N ∣ z) := by
  rcases h3 with ⟨t, ht⟩
  have h4Abs : 4 ∣ z.natAbs := by
    rw [← Int.natCast_dvd]
    simpa using h4
  have hAbsEq : z.natAbs = 3 ^ N * t.natAbs := by
    rw [ht, Int.natAbs_mul, Int.natAbs_pow]
    norm_num
  rw [hAbsEq, Nat.mul_comm] at h4Abs
  have hCop : Nat.Coprime 4 (3 ^ N) := by
    exact (show Nat.Coprime 4 3 by decide).pow_right N
  have h4tAbs : 4 ∣ t.natAbs :=
    hCop.dvd_of_dvd_mul_right h4Abs
  have h4t : (4 : ℤ) ∣ t := by
    have h4t' := h4tAbs
    rw [← Int.natCast_dvd] at h4t'
    simpa using h4t'
  rcases h4t with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  rw [ht, hq]
  ring

/--
critical width が collision quantum より小さければ、3進合同する二つの codes は等しい。
-/
theorem affineConst_eq_of_threeAdic_congruence_of_width
    {u v : Word}
    {s : ℕ}
    (hVu : Valid u)
    (hVv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    (hLen : 2 ≤ oddSteps u)
    (hThree :
      ((3 : ℤ) ^ (oddSteps u + s) ∣
        (affineConst u : ℤ) - (affineConst v : ℤ)))
    (hWidth :
      criticalFerrersWidth (oddSteps u) <
        4 * 3 ^ (oddSteps u + s)) :
    affineConst u = affineConst v := by
  let D : ℤ := (affineConst u : ℤ) - (affineConst v : ℤ)
  have hFour : (4 : ℤ) ∣ D := by
    dsimp [D]
    exact four_dvd_affineConst_diff_of_valid_firstCrossing
      hVu hVv hFu hFv hp hLen
  have hThree' : (3 : ℤ) ^ (oddSteps u + s) ∣ D := by
    simpa [D] using hThree
  have hQuantum :
      ((4 : ℤ) * (3 : ℤ) ^ (oddSteps u + s) ∣ D) :=
    four_mul_threePow_dvd_of_both hFour hThree'
  have hAbsLe : D.natAbs ≤ criticalFerrersWidth (oddSteps u) := by
    simpa [D] using affineConst_diff_natAbs_le_criticalFerrersWidth
      hVu hVv hFu hFv hp
  by_contra hNe
  have hDNe : D ≠ 0 := by
    dsimp [D]
    exact sub_ne_zero.mpr (by exact_mod_cast hNe)
  have hQuantumLe := Int.natAbs_le_of_dvd_ne_zero hQuantum hDNe
  have hQAbs :
      Int.natAbs ((4 : ℤ) * (3 : ℤ) ^ (oddSteps u + s)) =
        4 * 3 ^ (oddSteps u + s) := by
    simp [Int.natAbs_mul, Int.natAbs_pow]
  rw [hQAbs] at hQuantumLe
  omega

/--
一般の anchored 3進復元定理。
同じ `(r,H)` の valid FirstCrossing words に対し、幅条件と mod `3^(r+s)` 一致から word 一致。
-/
theorem word_eq_of_threeAdic_congruence_of_width
    {u v : Word}
    {s : ℕ}
    (hVu : Valid u)
    (hVv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hLen : 2 ≤ oddSteps u)
    (hThree :
      ((3 : ℤ) ^ (oddSteps u + s) ∣
        (affineConst u : ℤ) - (affineConst v : ℤ)))
    (hWidth :
      criticalFerrersWidth (oddSteps u) <
        4 * 3 ^ (oddSteps u + s)) :
    u = v := by
  have hB := affineConst_eq_of_threeAdic_congruence_of_width
    hVu hVv hFu hFv hp hLen hThree hWidth
  exact word_eq_of_same_losslessTriple hVu hVv hp hH hB

/-- 通常の `s=0` では長さ 20 まで width criterion が成立する。 -/
theorem criticalFerrersWidth_lt_quantum_of_le_twenty
    {r : ℕ}
    (hr : r ≤ 20) :
    criticalFerrersWidth r < 4 * 3 ^ r := by
  interval_cases r <;>
    decide

/-- `3 | start` が与える一桁追加 `s=1` では長さ 53 まで width criterion が成立する。 -/
theorem criticalFerrersWidth_lt_anchoredQuantum_of_le_fiftyThree
    {r : ℕ}
    (hr : r ≤ 53) :
    criticalFerrersWidth r < 4 * 3 ^ (r + 1) := by
  interval_cases r <;>
    decide

/--
通常の mod `3^r` code は、`2 <= r <= 20` の valid FirstCrossing class で単射。
-/
theorem word_eq_of_threeAdic_code_of_le_twenty
    {u v : Word}
    (hVu : Valid u)
    (hVv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hLen : 2 ≤ oddSteps u)
    (hr : oddSteps u ≤ 20)
    (hThree :
      ((3 : ℤ) ^ oddSteps u ∣
        (affineConst u : ℤ) - (affineConst v : ℤ))) :
    u = v := by
  apply word_eq_of_threeAdic_congruence_of_width
    (s := 0) hVu hVv hFu hFv hp hH hLen
  · simpa using hThree
  · simpa using criticalFerrersWidth_lt_quantum_of_le_twenty hr

/--
一桁追加された mod `3^(r+1)` code は、`2 <= r <= 53` で単射。
-/
theorem word_eq_of_threeAdic_code_succ_of_le_fiftyThree
    {u v : Word}
    (hVu : Valid u)
    (hVv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hLen : 2 ≤ oddSteps u)
    (hr : oddSteps u ≤ 53)
    (hThree :
      ((3 : ℤ) ^ (oddSteps u + 1) ∣
        (affineConst u : ℤ) - (affineConst v : ℤ))) :
    u = v := by
  apply word_eq_of_threeAdic_congruence_of_width
    (s := 1) hVu hVv hFu hFv hp hH hLen hThree
  exact criticalFerrersWidth_lt_anchoredQuantum_of_le_fiftyThree hr

/--
`3 | start` を actual realization として与えた版。
同じ `(r,H)` と同じ出口を持つ二候補は `r <= 53` なら一致する。
-/
theorem word_eq_of_three_divisible_starts_same_end_of_le_fiftyThree
    {u v : Word}
    {xu xv y : ℕ}
    (hVu : Valid u)
    (hVv : Valid v)
    (hFu : FirstCrossing u)
    (hFv : FirstCrossing v)
    (hRu : Realizes u xu y)
    (hRv : Realizes v xv y)
    (hxu : 3 ∣ xu)
    (hxv : 3 ∣ xv)
    (hp : oddSteps u = oddSteps v)
    (hH : twoSteps u = twoSteps v)
    (hLen : 2 ≤ oddSteps u)
    (hr : oddSteps u ≤ 53) :
    u = v := by
  have hThree :=
    threePow_dvd_affineConst_diff_of_anchored_realizations
      (s := 1) hRu hRv (by simpa using hxu) (by simpa using hxv) hp hH
  exact word_eq_of_threeAdic_code_succ_of_le_fiftyThree
    hVu hVv hFu hFv hp hH hLen hr (by simpa using hThree)

end Word
end Collatz2
