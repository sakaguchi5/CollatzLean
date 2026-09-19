import CollatzLean.Collatz3.Mersenne.TargetOneHoleGeometric
import Mathlib.NumberTheory.Multiplicity

import Mathlib.Tactic.NormNum

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: target-one の 2-adic rigidity

`TargetOneHoleGeometricData` の `q<t` branch に対し、
source width `n` が depth `k` の 2-adic valuation から exact に決まることを示す。

結論は次の四式。

* even `k`, `r=1`, `q=1`  : `n = 1 + v₂(k)`
* even `k`, `r=1`, `q≥2` : `n = 2 + v₂(k)`
* odd  `k`, `r=2`, `q=1` : `n = v₂(k-1)`
* odd  `k`, `r=2`, `q≥2` : `n = 2 + v₂(k-1)`

ここで `v₂(m)` は `padicValNat 2 m`。
-/

namespace Collatz3
namespace Mersenne

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- 正の 2 冪は偶数。 -/
private theorem twoPow_even_of_pos
    {n : ℕ} (hn : 0 < n) :
    Even (2 ^ n) := by
  apply even_iff_two_dvd.mpr
  exact pow_dvd_pow 2 (by omega : 1 ≤ n)

/-- 偶数 base の正長 geometric sum は奇数。 -/
private theorem targetGeomSum_odd_of_even_base
    {x t : ℕ}
    (hx : Even x)
    (ht : 0 < t) :
    Odd (targetGeomSum x t) := by
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  change Odd (targetGeomSum x (s + 1))
  rw [targetGeomSum_succ]
  rcases hx with ⟨a, ha⟩
  refine ⟨a * targetGeomSum x s, ?_⟩
  rw [ha]
  ring

/-- `2^n * odd` の 2-adic valuationは exact に `n`。 -/
private theorem padicValNat_twoPow_mul_odd
    (n m : ℕ)
    (hm : Odd m) :
    padicValNat 2 (2 ^ n * m) = n := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm
  have hNot : ¬2 ∣ m := by
    rintro hDvd
    rcases hDvd with ⟨c, hc⟩
    rcases hm with ⟨a, ha⟩
    omega
  rw [padicValNat.mul (by positivity) hm0]
  rw [padicValNat.prime_pow]
  rw [padicValNat.eq_zero_of_not_dvd hNot]
  omega

/-- even exponent に対する `v₂(3^m-1)=2+v₂(m)`。 -/
private theorem padicValNat_threePow_sub_one
    {m : ℕ}
    (hm : 0 < m)
    (hmEven : Even m) :
    padicValNat 2 (3 ^ m - 1) = 2 + padicValNat 2 m := by
  have hLTE :=
    padicValNat.pow_two_sub_one
      (x := 3) (n := m)
      (by norm_num) (by norm_num)
      (Nat.ne_of_gt hm) hmEven
  have hFour : padicValNat 2 4 = 2 := by
    change padicValNat 2 (2 ^ 2) = 2
    rw [padicValNat.prime_pow]
  have hTwo : padicValNat 2 2 = 1 := by
    simp only [Order.lt_two_iff, Std.le_refl, padicValNat_base]
  rw [hFour, hTwo] at hLTE
  omega

/-- `q≤t` に対応する tail length と geometric sum 分解。 -/
private theorem targetGeomSum_split
    {x q t : ℕ}
    (hqt : q ≤ t) :
    targetGeomSum x t =
      targetGeomSum x q +
        x ^ q * targetGeomSum x (t - q) := by
  have hDecomp : q + (t - q) = t := by omega
  calc
    targetGeomSum x t =
        targetGeomSum x (q + (t - q)) := by rw [hDecomp]
    _ =
        targetGeomSum x q +
          x ^ q * targetGeomSum x (t - q) :=
      targetGeomSum_add x q (t - q)

/-- `q<t` なら tail geometric sum も正長で奇数。 -/
private theorem targetTail_odd
    {n q t : ℕ}
    (hn : 0 < n)
    (hqt : q < t) :
    Odd (targetGeomSum (2 ^ n) (t - q)) := by
  apply targetGeomSum_odd_of_even_base (twoPow_even_of_pos hn)
  omega

/-! ## even k / r=1 -/

/-- even branch, `q=1` の exact 2-adic formula。 -/
theorem TargetOneHoleGeometricData.even_q_one_width_eq
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 0 < k)
    (hkEven : Even k)
    (hn : 0 < n)
    (hqt : h.q < h.t)
    (hq : h.q = 1) :
    n = 1 + padicValNat 2 k := by
  let x : ℕ := 2 ^ n
  let s : ℕ := h.t - 1
  have hSplit := targetGeomSum_split (x := x) h.q_le_t
  have hTailOdd : Odd (targetGeomSum x s) := by
    have hOdd := targetTail_odd hn hqt
    simpa [x, s, hq] using hOdd
  have hEq := h.equation
  rw [hq] at hEq hSplit
  have hG1 : targetGeomSum x 1 = 1 := by
    simp [targetGeomSum]
  rw [hG1] at hEq hSplit
  have hPowOne : x ^ 1 = x := by
    simp
  rw [hPowOne] at hSplit
  have hSplit' :
      targetGeomSum x h.t =
        1 + x * targetGeomSum x s := by
    simpa [s] using hSplit
  have hAdd :
      3 ^ k =
        1 + 2 ^ (n + 1) * targetGeomSum x s := by
    rw [hSplit'] at hEq
    have hLinear :
        3 ^ k =
          1 + 2 * (2 ^ n * targetGeomSum x s) := by
      dsimp [x] at hEq ⊢
      omega
    calc
      3 ^ k =
          1 + 2 * (2 ^ n * targetGeomSum x s) := hLinear
      _ =
          1 + 2 ^ (n + 1) * targetGeomSum x s := by
            rw [pow_succ]
            ring
  have hDiff :
      3 ^ k - 1 =
        2 ^ (n + 1) * targetGeomSum x s := by
    omega
  have hValEq :=
    congrArg (padicValNat 2) hDiff
  have hValRight :=
    padicValNat_twoPow_mul_odd
      (n + 1) (targetGeomSum x s) hTailOdd
  rw [hValRight] at hValEq
  have hLTE :=
    padicValNat_threePow_sub_one hk hkEven
  rw [hLTE] at hValEq
  omega

/-- even branch, `q≥2` の exact 2-adic formula。 -/
theorem TargetOneHoleGeometricData.even_q_ge_two_width_eq
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 0 < k)
    (hkEven : Even k)
    (hn : 0 < n)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q) :
    n = 2 + padicValNat 2 k := by
  let x : ℕ := 2 ^ n
  let p : ℕ := h.q - 1
  let s : ℕ := h.t - h.q
  have hpPos : 0 < p := by dsimp [p]; omega
  have hqEq : h.q = p + 1 := by dsimp [p]; omega
  have hSplit := targetGeomSum_split (x := x) h.q_le_t
  have hTailOdd : Odd (targetGeomSum x s) := by
    dsimp [x, s]
    exact targetTail_odd hn hqt
  have hGpOdd : Odd (targetGeomSum x p) :=
    targetGeomSum_odd_of_even_base
      (by dsimp [x]; exact twoPow_even_of_pos hn) hpPos
  let H : ℕ :=
    targetGeomSum x p + 2 * x ^ p * targetGeomSum x s
  have hHOdd : Odd H := by
    rcases hGpOdd with ⟨a, ha⟩
    refine ⟨a + x ^ p * targetGeomSum x s, ?_⟩
    dsimp [H]
    rw [ha]
    ring
  have hGq :
      targetGeomSum x h.q = x * targetGeomSum x p + 1 := by
    rw [hqEq]
    exact targetGeomSum_succ x p
  have hPowQ : x ^ h.q = x * x ^ p := by
    rw [hqEq, pow_succ]
    ring
  have hEq := h.equation
  rw [hSplit, hGq, hPowQ] at hEq
  have hAdd : 3 ^ k = 1 + 2 ^ n * H := by
    dsimp [H, x] at hEq ⊢
    nlinarith
  have hDiff : 3 ^ k - 1 = 2 ^ n * H := by
    omega
  have hValEq := congrArg (padicValNat 2) hDiff
  have hValRight := padicValNat_twoPow_mul_odd n H hHOdd
  rw [hValRight] at hValEq
  have hLTE := padicValNat_threePow_sub_one hk hkEven
  rw [hLTE] at hValEq
  omega

/-- even branch の `q=1 / q≥2` dichotomy。 -/
theorem TargetOneHoleGeometricData.even_width_cases
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 0 < k)
    (hkEven : Even k)
    (hn : 0 < n)
    (hqt : h.q < h.t) :
    (h.q = 1 ∧ n = 1 + padicValNat 2 k) ∨
      (2 ≤ h.q ∧ n = 2 + padicValNat 2 k) := by
  have hqPos : 0 < h.q := h.q_pos
  have hqCases : h.q = 1 ∨ 2 ≤ h.q := by omega
  rcases hqCases with hq | hq
  · exact Or.inl ⟨hq, h.even_q_one_width_eq hk hkEven hn hqt hq⟩
  · exact Or.inr ⟨hq, h.even_q_ge_two_width_eq hk hkEven hn hqt hq⟩

/-! ## odd k / r=2 -/

/--
odd branch では tail geometric sum が 3 の倍数となり、3 を一つ落とした exact equation を得る。
-/
private theorem oddBranch_divided_equation
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 0 < k)
    (hn : 0 < n)
    (hqt : h.q < h.t) :
    ∃ H : ℕ,
      Odd H ∧
      3 ^ (k - 1) =
        targetGeomSum (2 ^ n) h.q +
          4 * (2 ^ n) ^ h.q * H := by
  let x : ℕ := 2 ^ n
  let s : ℕ := h.t - h.q
  have hSplit := targetGeomSum_split (x := x) h.q_le_t
  have hTailOdd : Odd (targetGeomSum x s) := by
    dsimp [x, s]
    exact targetTail_odd hn hqt
  have hEq := h.equation
  rw [hSplit] at hEq
  norm_num at hEq
  have hCore :
      3 ^ k =
        3 * targetGeomSum x h.q +
          4 * x ^ h.q * targetGeomSum x s := by
    nlinarith
  have hThreePow : 3 ∣ 3 ^ k := by
    exact dvd_pow_self 3 (Nat.ne_of_gt hk)
  rcases hThreePow with ⟨C, hC⟩
  have hTermDvd : 3 ∣ 4 * x ^ h.q * targetGeomSum x s := by
    refine ⟨C - targetGeomSum x h.q, ?_⟩
    rw [hC] at hCore
    omega
  have hxNot : ¬3 ∣ x := by
    dsimp [x]
    intro hDvd
    have hTwo : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hDvd
    norm_num at hTwo
  have hxPowNot : ¬3 ∣ x ^ h.q := by
    intro hDvd
    exact hxNot (Nat.prime_three.dvd_of_dvd_pow hDvd)
  have hCoeffNot : ¬3 ∣ 4 * x ^ h.q := by
    intro hDvd
    rcases Nat.prime_three.dvd_mul.mp hDvd with h4 | hxq
    · norm_num at h4
    · exact hxPowNot hxq
  have hTailDvd : 3 ∣ targetGeomSum x s := by
    rcases Nat.prime_three.dvd_mul.mp hTermDvd with hCoeff | hTail
    · exact (hCoeffNot hCoeff).elim
    · exact hTail
  rcases hTailDvd with ⟨H, hH⟩
  have hHOdd : Odd H := by
    apply Nat.not_even_iff_odd.mp
    intro hEven
    rcases hEven with ⟨a, ha⟩
    rcases hTailOdd with ⟨c, hc⟩
    rw [hH, ha] at hc
    omega
  refine ⟨H, hHOdd, ?_⟩
  have hkEq : k = (k - 1) + 1 := by omega
  have hPowK : 3 ^ k = 3 ^ (k - 1) * 3 := by
    calc
      3 ^ k = 3 ^ ((k - 1) + 1) :=
        congrArg (fun e : ℕ => 3 ^ e) hkEq
      _ = 3 ^ (k - 1) * 3 := by rw [pow_succ]
  rw [hPowK, hH] at hCore
  dsimp [x] at hCore ⊢
  nlinarith

/-- odd branch, `q=1` の exact 2-adic formula。 -/
theorem TargetOneHoleGeometricData.odd_q_one_width_eq
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 1 < k)
    (hkOdd : k % 2 = 1)
    (hn : 0 < n)
    (hqt : h.q < h.t)
    (hq : h.q = 1) :
    n = padicValNat 2 (k - 1) := by
  rcases oddBranch_divided_equation h (by omega) hn hqt with
    ⟨H, hHOdd, hDiv⟩
  rw [hq] at hDiv
  have hG1 : targetGeomSum (2 ^ n) 1 = 1 := by
    simp [targetGeomSum]
  rw [hG1, pow_one] at hDiv
  have hPow :
      2 ^ (n + 2) = 4 * 2 ^ n := by
    rw [pow_add]
    norm_num
    ring
  have hAdd :
      3 ^ (k - 1) = 1 + 2 ^ (n + 2) * H := by
    rw [hPow]
    simpa [mul_assoc] using hDiv
  have hDiff :
      3 ^ (k - 1) - 1 = 2 ^ (n + 2) * H := by
    omega
  have hValEq := congrArg (padicValNat 2) hDiff
  have hValRight := padicValNat_twoPow_mul_odd (n + 2) H hHOdd
  rw [hValRight] at hValEq
  have hPredPos : 0 < k - 1 := by omega
  have hPredEven : Even (k - 1) := by
    apply even_iff_two_dvd.mpr
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  have hLTE := padicValNat_threePow_sub_one hPredPos hPredEven
  rw [hLTE] at hValEq
  omega

/-- odd branch, `q≥2` の exact 2-adic formula。 -/
theorem TargetOneHoleGeometricData.odd_q_ge_two_width_eq
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 1 < k)
    (hkOdd : k % 2 = 1)
    (hn : 0 < n)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q) :
    n = 2 + padicValNat 2 (k - 1) := by
  rcases oddBranch_divided_equation h (by omega) hn hqt with
    ⟨H, hHOdd, hDiv⟩
  let x : ℕ := 2 ^ n
  let p : ℕ := h.q - 1
  have hpPos : 0 < p := by dsimp [p]; omega
  have hqEq : h.q = p + 1 := by dsimp [p]; omega
  have hGpOdd : Odd (targetGeomSum x p) :=
    targetGeomSum_odd_of_even_base
      (by dsimp [x]; exact twoPow_even_of_pos hn) hpPos
  let J : ℕ :=
    targetGeomSum x p + 4 * x ^ p * H
  have hJOdd : Odd J := by
    rcases hGpOdd with ⟨a, ha⟩
    refine ⟨a + 2 * x ^ p * H, ?_⟩
    dsimp [J]
    rw [ha]
    ring
  have hGq :
      targetGeomSum x h.q = x * targetGeomSum x p + 1 := by
    rw [hqEq]
    exact targetGeomSum_succ x p
  have hPowQ : x ^ h.q = x * x ^ p := by
    rw [hqEq, pow_succ]
    ring
  change 3 ^ (k - 1) =
      targetGeomSum x h.q + 4 * x ^ h.q * H at hDiv
  rw [hGq, hPowQ] at hDiv
  have hAdd : 3 ^ (k - 1) = 1 + 2 ^ n * J := by
    dsimp [J, x] at hDiv ⊢
    nlinarith
  have hDiff : 3 ^ (k - 1) - 1 = 2 ^ n * J := by
    omega
  have hValEq := congrArg (padicValNat 2) hDiff
  have hValRight := padicValNat_twoPow_mul_odd n J hJOdd
  rw [hValRight] at hValEq
  have hPredPos : 0 < k - 1 := by omega
  have hPredEven : Even (k - 1) := by
    apply even_iff_two_dvd.mpr
    apply Nat.dvd_iff_mod_eq_zero.mpr
    omega
  have hLTE := padicValNat_threePow_sub_one hPredPos hPredEven
  rw [hLTE] at hValEq
  omega

/-- odd branch の `q=1 / q≥2` dichotomy。 -/
theorem TargetOneHoleGeometricData.odd_width_cases
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 1 < k)
    (hkOdd : k % 2 = 1)
    (hn : 0 < n)
    (hqt : h.q < h.t) :
    (h.q = 1 ∧ n = padicValNat 2 (k - 1)) ∨
      (2 ≤ h.q ∧ n = 2 + padicValNat 2 (k - 1)) := by
  have hqPos : 0 < h.q := h.q_pos
  have hqCases : h.q = 1 ∨ 2 ≤ h.q := by omega
  rcases hqCases with hq | hq
  · exact Or.inl ⟨hq, h.odd_q_one_width_eq hk hkOdd hn hqt hq⟩
  · exact Or.inr ⟨hq, h.odd_q_ge_two_width_eq hk hkOdd hn hqt hq⟩

end Mersenne
end Collatz3
