import CollatzLean.Collatz3.Mersenne.TargetTwoHoleTwoAdicCuts
import CollatzLean.Collatz3.Mersenne.TwoAdicArithmetic
import CollatzLean.Collatz3.Arithmetic.ThreeOrderModTwoPow
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.NormNum

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: target-two width bound

三 phase の first cut はすべて

`A = (2^n-1)3^k + (2^r-1)`

の 2-adic valuationを読む。
ここでは exact branch formula より先に、Stephan 接続に十分な共通上界

* even `k`, `r=1`: `n ≤ 3 + v₂(k)`
* odd  `k`, `r=2`: `n ≤ 3 + v₂(k-1)`

を内部 theorem として固定する。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem padicValNat_ge_of_pow_dvd
    {e m : ℕ}
    (hm : m ≠ 0)
    (hDvd : 2 ^ e ∣ m) :
    e ≤ padicValNat 2 m := by
  exact (padicValNat_dvd_iff_le hm).mp hDvd

private theorem even_cut_width_from_val
    {k n E : ℕ}
    (hk : 0 < k)
    (hkEven : Even k)
    (hn4 : 4 ≤ n)
    (hVal :
      padicValNat 2 ((2 ^ n - 1) * 3 ^ k + 1) = E)
    (hLower : n - 1 ≤ E) :
    n ≤ 3 + padicValNat 2 k := by
  by_contra hNot
  have hStrong : 3 + padicValNat 2 k < n := by
    omega
  have hKVal :=
    padicValNat_threePow_sub_one hk hkEven
  have hApos : 0 < (2 ^ n - 1) * 3 ^ k + 1 := by
    positivity
  have hPowDvdA :
      2 ^ (n - 1) ∣ (2 ^ n - 1) * 3 ^ k + 1 := by
    apply (padicValNat_dvd_iff_le (Nat.ne_of_gt hApos)).2
    rw [hVal]
    exact hLower
  have hPowDvdTop :
      2 ^ (n - 1) ∣ 2 ^ n * 3 ^ k := by
    refine dvd_mul_of_dvd_left ?_ _
    exact pow_dvd_pow 2 (by omega : n - 1 ≤ n)
  have hIdentity :
      ((2 ^ n - 1) * 3 ^ k + 1) + (3 ^ k - 1) =
        2 ^ n * 3 ^ k := by
    have hTwoOne : 1 ≤ 2 ^ n :=
      Nat.one_le_pow n 2 (by norm_num)
    have hThreeOne : 1 ≤ 3 ^ k :=
      Nat.one_le_pow k 3 (by norm_num)
    calc
      ((2 ^ n - 1) * 3 ^ k + 1) + (3 ^ k - 1) =
          (2 ^ n - 1) * 3 ^ k + ((3 ^ k - 1) + 1) := by
            ring
      _ = (2 ^ n - 1) * 3 ^ k + 3 ^ k := by
            rw [Nat.sub_add_cancel hThreeOne]
      _ = ((2 ^ n - 1) + 1) * 3 ^ k := by
            ring
      _ = 2 ^ n * 3 ^ k := by
            rw [Nat.sub_add_cancel hTwoOne]
  have hDiffDvd :
      2 ^ (n - 1) ∣ 3 ^ k - 1 := by
    rw [← hIdentity] at hPowDvdTop
    have hPowDvdTop' :
        2 ^ (n - 1) ∣
          (3 ^ k - 1) + ((2 ^ n - 1) * 3 ^ k + 1) := by
      simpa [Nat.add_comm] using hPowDvdTop
    exact
      (Nat.dvd_add_iff_left hPowDvdA).mpr hPowDvdTop'
  have hKSubPos : 3 ^ k - 1 ≠ 0 := by
    have hThreeGt : 1 < 3 ^ k :=
      one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hk)
    omega
  have hValLower :
      n - 1 ≤ padicValNat 2 (3 ^ k - 1) :=
    padicValNat_ge_of_pow_dvd hKSubPos hDiffDvd
  rw [hKVal] at hValLower
  omega

private theorem odd_cut_width_from_val
    {k n E : ℕ}
    (hk2 : 2 ≤ k)
    (hkOdd : k % 2 = 1)
    (hn4 : 4 ≤ n)
    (hVal :
      padicValNat 2 ((2 ^ n - 1) * 3 ^ k + 3) = E)
    (hLower : n - 1 ≤ E) :
    n ≤ 3 + padicValNat 2 (k - 1) := by
  have hk : 0 < k := by
    omega
  have hkPredPos : 0 < k - 1 := by
    omega
  have hkPredEven : Even (k - 1) := by
    refine ⟨k / 2, ?_⟩
    have hdecomp := Nat.mod_add_div k 2
    rw [hkOdd] at hdecomp
    omega
  by_contra hNot
  have hStrong :
      3 + padicValNat 2 (k - 1) < n := by
    omega
  have hPredVal :=
    padicValNat_threePow_sub_one hkPredPos hkPredEven
  have hApos :
      0 < (2 ^ n - 1) * 3 ^ k + 3 := by
    positivity
  have hPowDvdA :
      2 ^ (n - 1) ∣ (2 ^ n - 1) * 3 ^ k + 3 := by
    apply (padicValNat_dvd_iff_le (Nat.ne_of_gt hApos)).2
    rw [hVal]
    exact hLower
  have hPowDvdTop :
      2 ^ (n - 1) ∣ 2 ^ n * 3 ^ k := by
    refine dvd_mul_of_dvd_left ?_ _
    exact pow_dvd_pow 2 (by omega : n - 1 ≤ n)
  have hkEq : k = (k - 1) + 1 := by
    omega
  have hPowK :
      3 ^ k = 3 ^ (k - 1) * 3 := by
    calc
      3 ^ k = 3 ^ ((k - 1) + 1) :=
        congrArg (fun e : ℕ => 3 ^ e) hkEq
      _ = 3 ^ (k - 1) * 3 := by
        rw [pow_succ]
  have hIdentity :
      ((2 ^ n - 1) * 3 ^ k + 3) +
          3 * (3 ^ (k - 1) - 1) =
        2 ^ n * 3 ^ k := by
    have hTwoOne : 1 ≤ 2 ^ n :=
      Nat.one_le_pow n 2 (by norm_num)
    have hPredOne : 1 ≤ 3 ^ (k - 1) :=
      Nat.one_le_pow (k - 1) 3 (by norm_num)
    rw [hPowK]
    calc
      ((2 ^ n - 1) * (3 ^ (k - 1) * 3) + 3) +
            3 * (3 ^ (k - 1) - 1) =
          (2 ^ n - 1) * (3 ^ (k - 1) * 3) +
            3 * ((3 ^ (k - 1) - 1) + 1) := by
              ring
      _ =
          (2 ^ n - 1) * (3 ^ (k - 1) * 3) +
            3 * 3 ^ (k - 1) := by
              rw [Nat.sub_add_cancel hPredOne]
      _ =
          ((2 ^ n - 1) + 1) *
            (3 ^ (k - 1) * 3) := by
              ring
      _ =
          2 ^ n * (3 ^ (k - 1) * 3) := by
              rw [Nat.sub_add_cancel hTwoOne]
  have hThreeDiffDvd :
      2 ^ (n - 1) ∣
        3 * (3 ^ (k - 1) - 1) := by
    rw [← hIdentity] at hPowDvdTop
    have hPowDvdTop' :
        2 ^ (n - 1) ∣
          3 * (3 ^ (k - 1) - 1) +
            ((2 ^ n - 1) * 3 ^ k + 3) := by
      simpa [Nat.add_comm] using hPowDvdTop
    exact
      (Nat.dvd_add_iff_left hPowDvdA).mpr hPowDvdTop'
  have hCoprime :
      (2 ^ (n - 1)).Coprime 3 := by
    exact (by decide : Nat.Coprime 2 3).pow_left _
  have hDiffDvd :
      2 ^ (n - 1) ∣ 3 ^ (k - 1) - 1 := by
    exact hCoprime.dvd_of_dvd_mul_left hThreeDiffDvd
  have hDiffNe :
      3 ^ (k - 1) - 1 ≠ 0 := by
    have hThreeGt :
        1 < 3 ^ (k - 1) :=
      one_lt_pow₀
        (by norm_num)
        (Nat.ne_of_gt hkPredPos)
    omega
  have hValLower :
      n - 1 ≤
        padicValNat 2 (3 ^ (k - 1) - 1) :=
    padicValNat_ge_of_pow_dvd hDiffNe hDiffDvd
  rw [hPredVal] at hValLower
  omega

/-- wrapped first cut は常に `n-1` 以上。 -/
theorem TargetTwoHoleWrappedGeometricData.firstCut_ge_width_pred
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b) :
    n - 1 ≤ n * h.q - 1 := by
  have hq : 1 ≤ h.q := by
    exact h.q_pos
  have hnq : n ≤ n * h.q :=
    Nat.le_mul_of_pos_right n h.q_pos
  omega

/-- forward first cut は常に `n` 以上。 -/
theorem TargetTwoHoleSplitForwardGeometricData.firstCut_ge_width
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b) :
    n ≤ n * h.q := by
  exact Nat.le_mul_of_pos_right n h.q_pos

/-- reverse first cut は常に `n` 以上。 -/
theorem TargetTwoHoleSplitReverseGeometricData.firstCut_ge_width
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b) :
    n ≤ n * h.u + r := by
  have hu : 0 < h.u := h.u_pos
  have hn : n ≤ n * h.u := Nat.le_mul_of_pos_right n hu
  omega

/-- wrapped/even の共通 width upper bound。 -/
theorem TargetTwoHoleWrappedGeometricData.even_width_le
    {k n L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n 1 L a b)
    (hk : 0 < k)
    (hkEven : Even k)
    (hn4 : 4 ≤ n) :
    n ≤ 3 + padicValNat 2 k := by
  have hVal := h.firstCut_eq (by omega : 0 < n) (by norm_num : 0 < 1)
  norm_num at hVal
  apply even_cut_width_from_val hk hkEven hn4 hVal h.firstCut_ge_width_pred

/-- wrapped/odd の共通 width upper bound。 -/
theorem TargetTwoHoleWrappedGeometricData.odd_width_le
    {k n L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n 2 L a b)
    (hk2 : 2 ≤ k)
    (hkOdd : k % 2 = 1)
    (hn4 : 4 ≤ n) :
    n ≤ 3 + padicValNat 2 (k - 1) := by
  have hVal := h.firstCut_eq (by omega : 0 < n) (by norm_num : 0 < 2)
  norm_num at hVal
  apply odd_cut_width_from_val hk2 hkOdd hn4 hVal h.firstCut_ge_width_pred

/-- split-forward/even の共通 width upper bound。 -/
theorem TargetTwoHoleSplitForwardGeometricData.even_width_le
    {k n L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n 1 L a b)
    (hk : 0 < k)
    (hkEven : Even k)
    (hn4 : 4 ≤ n) :
    n ≤ 3 + padicValNat 2 k := by
  have hVal := h.firstCut_eq (by norm_num : 0 < 1)
  norm_num at hVal
  apply even_cut_width_from_val hk hkEven hn4 hVal
  exact le_trans (by omega : n - 1 ≤ n) h.firstCut_ge_width

/-- split-forward/odd の共通 width upper bound。 -/
theorem TargetTwoHoleSplitForwardGeometricData.odd_width_le
    {k n L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n 2 L a b)
    (hk2 : 2 ≤ k)
    (hkOdd : k % 2 = 1)
    (hn4 : 4 ≤ n) :
    n ≤ 3 + padicValNat 2 (k - 1) := by
  have hVal := h.firstCut_eq (by norm_num : 0 < 2)
  norm_num at hVal
  apply odd_cut_width_from_val hk2 hkOdd hn4 hVal
  exact le_trans (by omega : n - 1 ≤ n) h.firstCut_ge_width

/-- split-reverse/even の共通 width upper bound。 -/
theorem TargetTwoHoleSplitReverseGeometricData.even_width_le
    {k n L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n 1 L a b)
    (hk : 0 < k)
    (hkEven : Even k)
    (hn4 : 4 ≤ n) :
    n ≤ 3 + padicValNat 2 k := by
  have hVal := h.firstCut_eq hn4 (Or.inl rfl)
  norm_num at hVal
  apply even_cut_width_from_val hk hkEven hn4 hVal
  exact le_trans (by omega : n - 1 ≤ n) h.firstCut_ge_width

/-- split-reverse/odd の共通 width upper bound。 -/
theorem TargetTwoHoleSplitReverseGeometricData.odd_width_le
    {k n L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n 2 L a b)
    (hk2 : 2 ≤ k)
    (hkOdd : k % 2 = 1)
    (hn4 : 4 ≤ n) :
    n ≤ 3 + padicValNat 2 (k - 1) := by
  have hVal := h.firstCut_eq hn4 (Or.inr rfl)
  norm_num at hVal
  apply odd_cut_width_from_val hk2 hkOdd hn4 hVal
  exact le_trans (by omega : n - 1 ≤ n) h.firstCut_ge_width

end Mersenne
end Collatz3
