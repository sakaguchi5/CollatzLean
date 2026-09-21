import CollatzLean.Collatz3.Mersenne.SplitTwoHoleMinimalCertificate
import CollatzLean.Collatz3.Mersenne.SmallHoleModular
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: split-two proper residual の内部排除

split-two の minimal certificate が full six-term でないとき、
選ばれなかった項の補集合は exact zero-sum になる。

このファイルでは、その補集合を六 index の有限組合せとして完全に整理する。
well-formed 条件

* `0 < k`,
* `0 < a < n`,
* `0 < b < L`,
* `0 < r`,

の下では、補集合の zero-sum はごく少数の型しか残らない。
残る型は最終的に

* `3^k + 1 = 2^e`, または
* `3^k = 1 + 2^e`

へ落ち、前者は `k=1`、後者は `k≤2` となる。

したがって non-full minimal certificate は `k≤2` を強制する。
特に `k≥3` では split-two の minimal pattern は full six-term しか残らない。

外部 ESS / Baker / S-unit finiteness は使用しない。
-/

namespace Collatz3
namespace Mersenne

open Arithmetic

private theorem twoPow_zmod2_eq_zero_of_pos
    {e : ℕ}
    (he : 0 < e) :
    (2 : ZMod 2) ^ e = 0 := by
  simpa using ZMod.natCast_pow_eq_zero_of_le 2 he

private theorem twoPow_zmod8_eq_zero_of_three_le
    {e : ℕ}
    (he : 3 ≤ e) :
    (2 : ZMod 8) ^ e = 0 := by
  simpa using ZMod.natCast_pow_eq_zero_of_le 2 he

private theorem twoPow_zmod16_eq_zero_of_four_le
    {e : ℕ}
    (he : 4 ≤ e) :
    (2 : ZMod 16) ^ e = 0 := by
  simpa using ZMod.natCast_pow_eq_zero_of_le 2 he

private theorem threePow_zmod3_eq_zero_of_pos
    {k : ℕ}
    (hk : 0 < k) :
    (3 : ZMod 3) ^ k = 0 := by
  simpa using ZMod.natCast_pow_eq_zero_of_le 3 hk

private theorem twoPow_ne_zero_zmod3
    (e : ℕ) :
    (2 : ZMod 3) ^ e ≠ 0 := by
  have hUnit : IsUnit (2 : ZMod 3) := by
    exact (ZMod.isUnit_iff_coprime 2 3).2 (by decide)
  exact (hUnit.pow e).ne_zero

/-- `3^k+1` が 2 冪なら、正の `k` では `k=1`。 -/
private theorem threePow_add_one_eq_twoPow_depth_one
    {k e : ℕ}
    (hk : 0 < k)
    (hEq : 3 ^ k + 1 = 2 ^ e) :
    k = 1 := by
  by_contra hkOne
  have hkTwo : 2 ≤ k := by omega
  have hNine : 9 ≤ 3 ^ k := by
    calc
      9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hkTwo
  have heThree : 3 ≤ e := by
    by_contra hNot
    have heLe : e ≤ 2 := by omega
    have hPowLe : 2 ^ e ≤ 2 ^ 2 :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) heLe
    norm_num at hPowLe
    omega
  have hCast := congrArg (fun z : ℕ => (z : ZMod 8)) hEq
  push_cast at hCast
  have hTwo : (2 : ZMod 8) ^ e = 0 :=
    twoPow_zmod8_eq_zero_of_three_le heThree
  have hPeriod : (3 : ZMod 8) ^ 2 = 1 := by decide
  rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 8) (e := k) hPeriod] at hCast
  rw [hTwo] at hCast
  have hkCases : k % 2 = 0 ∨ k % 2 = 1 :=
    Nat.mod_two_eq_zero_or_one k
  rcases hkCases with hkEven | hkOdd
  · norm_num [hkEven] at hCast
    exact (by decide : (2 : ZMod 8) ≠ 0) hCast
  · norm_num [hkOdd] at hCast
    exact (by decide : (4 : ZMod 8) ≠ 0) hCast

/-- `3^k = 1+2^e` なら、正の `k,e` では `k≤2`。 -/
private theorem threePow_eq_one_add_twoPow_depth_le_two
    {k e : ℕ}
    (he : 0 < e)
    (hEq : 3 ^ k = 1 + 2 ^ e) :
    k ≤ 2 := by
  by_contra hNot
  have hkThree : 3 ≤ k := by omega
  rcases Nat.mod_two_eq_zero_or_one k with hkEven | hkOdd
  · have hkFour : 4 ≤ k := by omega
    have hCompat : (k % 4) % 2 = k % 2 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    have hkModLt : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have hkMod : k % 4 = 0 ∨ k % 4 = 2 := by
      rw [hkEven] at hCompat
      omega
    rcases hkMod with hk0 | hk2
    · have hCast := congrArg (fun z : ℕ => (z : ZMod 5)) hEq
      push_cast at hCast
      have hPeriod : (3 : ZMod 5) ^ 4 = 1 := by decide
      rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 5) (e := k) hPeriod] at hCast
      rw [hk0] at hCast
      norm_num at hCast
      have hZero : (2 : ZMod 5) ^ e = 0 := by
        linear_combination hCast
      let : Fact (1 < (5 : ℕ)) := ⟨by norm_num⟩
      have hUnit : IsUnit (2 : ZMod 5) := by
        exact (ZMod.isUnit_iff_coprime 2 5).2 (by decide)
      exact (hUnit.pow e).ne_zero hZero
    · have hkSix : 6 ≤ k := by omega
      have h729 : 729 ≤ 3 ^ k := by
        calc
          729 = 3 ^ 6 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hkSix
      have heFour : 4 ≤ e := by
        by_contra hNotE
        have heLe : e ≤ 3 := by omega
        have hPowLe : 2 ^ e ≤ 2 ^ 3 :=
          Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) heLe
        norm_num at hPowLe
        omega
      have hCast := congrArg (fun z : ℕ => (z : ZMod 16)) hEq
      push_cast at hCast
      have hPeriod : (3 : ZMod 16) ^ 4 = 1 := by decide
      rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 16) (e := k) hPeriod] at hCast
      rw [hk2, twoPow_zmod16_eq_zero_of_four_le heFour] at hCast
      norm_num at hCast
      exact (by decide : (9 : ZMod 16) ≠ 1) hCast
  · have h27 : 27 ≤ 3 ^ k := by
      calc
        27 = 3 ^ 3 := by norm_num
        _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < (3 : ℕ)) hkThree
    have heThree : 3 ≤ e := by
      by_contra hNotE
      have heLe : e ≤ 2 := by omega
      have hPowLe : 2 ^ e ≤ 2 ^ 2 :=
        Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) heLe
      norm_num at hPowLe
      omega
    have hCast := congrArg (fun z : ℕ => (z : ZMod 8)) hEq
    push_cast at hCast
    have hPeriod : (3 : ZMod 8) ^ 2 = 1 := by decide
    rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 8) (e := k) hPeriod] at hCast
    rw [hkOdd, twoPow_zmod8_eq_zero_of_three_le heThree] at hCast
    norm_num at hCast
    exact (by decide : (3 : ZMod 8) ≠ 1) hCast

/-- `2^a * odd = 2^r * odd` なら 2 冪指数は一致する。 -/
private theorem twoPow_mul_oddWitness_exponents_eq
    {a r u v : ℕ}
    (hu : ∃ q : ℕ, u = 2 * q + 1)
    (hv : ∃ q : ℕ, v = 2 * q + 1)
    (hEq : 2 ^ a * u = 2 ^ r * v) :
    a = r := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with har | hra
  · let d : ℕ := r - a
    have hd : 0 < d := by dsimp [d]; omega
    have hrEq : r = a + d := by dsimp [d]; omega
    have hEq' : 2 ^ a * u = 2 ^ a * (2 ^ d * v) := by
      rw [hrEq, pow_add] at hEq
      simpa [mul_assoc] using hEq
    have hCancel : u = 2 ^ d * v :=
      Nat.mul_left_cancel (by positivity) hEq'
    rcases hu with ⟨q, hq⟩
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    have hEven : ∃ t : ℕ, 2 ^ d * v = 2 * t := by
      refine ⟨2 ^ j * v, ?_⟩
      rw [hj, pow_succ]
      ring
    rcases hEven with ⟨t, ht⟩
    rw [hq, ht] at hCancel
    omega
  · let d : ℕ := a - r
    have hd : 0 < d := by dsimp [d]; omega
    have haEq : a = r + d := by dsimp [d]; omega
    have hEq' : 2 ^ r * (2 ^ d * u) = 2 ^ r * v := by
      rw [haEq, pow_add] at hEq
      simpa [mul_assoc] using hEq
    have hCancel : 2 ^ d * u = v :=
      Nat.mul_left_cancel (by positivity) hEq'
    rcases hv with ⟨q, hq⟩
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    have hEven : ∃ t : ℕ, 2 ^ d * u = 2 * t := by
      refine ⟨2 ^ j * u, ?_⟩
      rw [hj, pow_succ]
      ring
    rcases hEven with ⟨t, ht⟩
    rw [ht, hq] at hCancel
    omega

private theorem one_add_twoPow_oddWitness
    {b : ℕ}
    (hb : 0 < b) :
    ∃ q : ℕ, 1 + 2 ^ b = 2 * q + 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  refine ⟨2 ^ j, ?_⟩
  rw [pow_succ]
  ring

/--
`2^n*3^k + 2^s = 2^(s+T)` で `T>0` なら、二つの左項の 2-adic 位相は一致する。
-/
private theorem sourceTop_plus_twoPow_forces_same_twoExp
    {k n s T : ℕ}
    (hT : 0 < T)
    (hEq : 2 ^ n * 3 ^ k + 2 ^ s = 2 ^ (s + T)) :
    n = s := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hns | hsn
  · let d : ℕ := s - n
    have hd : 0 < d := by dsimp [d]; omega
    have hsEq : s = n + d := by dsimp [d]; omega
    have hExp : s + T = n + (d + T) := by omega
    have hFactor :
        2 ^ n * (3 ^ k + 2 ^ d) = 2 ^ n * 2 ^ (d + T) := by
      calc
        2 ^ n * (3 ^ k + 2 ^ d)
            = 2 ^ n * 3 ^ k + 2 ^ (n + d) := by
                rw [pow_add]
                ring
        _ = 2 ^ n * 3 ^ k + 2 ^ s := by rw [← hsEq]
        _ = 2 ^ (s + T) := hEq
        _ = 2 ^ (n + (d + T)) := by rw [hExp]
        _ = 2 ^ n * 2 ^ (d + T) := by rw [pow_add]
    have hCancel : 3 ^ k + 2 ^ d = 2 ^ (d + T) :=
      Nat.mul_left_cancel (by positivity) hFactor
    rcases SignedTwoThreeUnit.threePow_eq_two_mul_add_one k with ⟨q, hq⟩
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    have hEvenD : ∃ x : ℕ, 2 ^ d = 2 * x := by
      refine ⟨2 ^ j, ?_⟩
      rw [hj, pow_succ]
      ring
    have hdT : 0 < d + T := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdT)
    have hEvenDT : ∃ y : ℕ, 2 ^ (d + T) = 2 * y := by
      refine ⟨2 ^ m, ?_⟩
      rw [hm, pow_succ]
      ring
    rcases hEvenD with ⟨x, hx⟩
    rcases hEvenDT with ⟨y, hy⟩
    rw [hq, hx, hy] at hCancel
    omega
  · let d : ℕ := n - s
    have hd : 0 < d := by dsimp [d]; omega
    have hnEq : n = s + d := by dsimp [d]; omega
    have hFactor :
        2 ^ s * (2 ^ d * 3 ^ k + 1) = 2 ^ s * 2 ^ T := by
      calc
        2 ^ s * (2 ^ d * 3 ^ k + 1)
            = 2 ^ (s + d) * 3 ^ k + 2 ^ s := by
                rw [pow_add]
                ring
        _ = 2 ^ n * 3 ^ k + 2 ^ s := by rw [← hnEq]
        _ = 2 ^ (s + T) := hEq
        _ = 2 ^ s * 2 ^ T := by rw [pow_add]
    have hCancel : 2 ^ d * 3 ^ k + 1 = 2 ^ T :=
      Nat.mul_left_cancel (by positivity) hFactor
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    have hEvenLeft : ∃ x : ℕ, 2 ^ d * 3 ^ k = 2 * x := by
      refine ⟨2 ^ j * 3 ^ k, ?_⟩
      rw [hj, pow_succ]
      ring
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
    have hEvenRight : ∃ y : ℕ, 2 ^ T = 2 * y := by
      refine ⟨2 ^ m, ?_⟩
      rw [hm, pow_succ]
      ring
    rcases hEvenLeft with ⟨x, hx⟩
    rcases hEvenRight with ⟨y, hy⟩
    rw [hx, hy] at hCancel
    omega

/-- 上の 2-adic 一致により、同型方程式は `3^k+1=2^T` へ落ちる。 -/
private theorem sourceTop_plus_twoPow_depth_one
    {k n s T : ℕ}
    (hk : 0 < k)
    (hT : 0 < T)
    (hEq : 2 ^ n * 3 ^ k + 2 ^ s = 2 ^ (s + T)) :
    k = 1 := by
  have hns := sourceTop_plus_twoPow_forces_same_twoExp hT hEq
  subst n
  have hFactor :
      2 ^ s * (3 ^ k + 1) = 2 ^ s * 2 ^ T := by
    rw [pow_add] at hEq
    simpa [mul_add, mul_assoc] using hEq
  have hCore : 3 ^ k + 1 = 2 ^ T := Nat.mul_left_cancel (by positivity) hFactor
  exact threePow_add_one_eq_twoPow_depth_one hk hCore

/-- source top は source hole より真に大きい。 -/
private theorem sourceHole_lt_sourceTop
    {k n a : ℕ}
    (han : a < n) :
    (2 : ℤ) ^ a * (3 : ℤ) ^ k <
      (2 : ℤ) ^ n * (3 : ℤ) ^ k := by
  have hPow : 2 ^ a < 2 ^ n :=
    Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) han
  have hMul : 2 ^ a * 3 ^ k < 2 ^ n * 3 ^ k :=
    Nat.mul_lt_mul_of_pos_right hPow (by positivity)
  exact_mod_cast hMul

/-- target top は base と hole の和より真に大きい。 -/
private theorem targetBase_add_hole_lt_targetTop
    {r L b : ℕ}
    (hb : 0 < b)
    (hbL : b < L) :
    (2 : ℤ) ^ r + (2 : ℤ) ^ (r + b) < (2 : ℤ) ^ (r + L) := by
  have hOneLt : 1 < 2 ^ b :=
    one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) (Nat.ne_of_gt hb)
  have hBL : b + 1 ≤ L := by omega
  have hPowLe : 2 ^ (b + 1) ≤ 2 ^ L :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hBL
  have hSmall : 1 + 2 ^ b < 2 ^ (b + 1) := by
    rw [pow_succ]
    omega
  have hInner : 1 + 2 ^ b < 2 ^ L := lt_of_lt_of_le hSmall hPowLe
  have hMul : 2 ^ r * (1 + 2 ^ b) < 2 ^ r * 2 ^ L :=
    Nat.mul_lt_mul_of_pos_left hInner (by positivity)
  have hNat : 2 ^ r + 2 ^ (r + b) < 2 ^ (r + L) := by
    rw [pow_add, pow_add]
    simpa [mul_add, mul_assoc] using hMul
  exact_mod_cast hNat

/-! ## 補集合の有限組合せ分類 -/

private theorem noNegative_complement_cases :
    ∀ u : Finset SplitTwoUnitIndex,
      SplitTwoUnitIndex.negThree ∉ u →
      SplitTwoUnitIndex.sourceHole ∉ u →
      SplitTwoUnitIndex.targetTop ∉ u →
      u.Nonempty →
      u = { .sourceTop } ∨
      u = { .targetBase } ∨
      u = { .targetHole } ∨
      u = { .sourceTop, .targetBase } ∨
      u = { .sourceTop, .targetHole } ∨
      u = { .targetBase, .targetHole } ∨
      u = { .sourceTop, .targetBase, .targetHole } := by
  native_decide

private theorem noPositive_complement_cases :
    ∀ u : Finset SplitTwoUnitIndex,
      SplitTwoUnitIndex.negThree ∉ u →
      SplitTwoUnitIndex.sourceTop ∉ u →
      SplitTwoUnitIndex.targetBase ∉ u →
      SplitTwoUnitIndex.targetHole ∉ u →
      u.Nonempty →
      u = { .sourceHole } ∨
      u = { .targetTop } ∨
      u = { .sourceHole, .targetTop } := by
  native_decide

private theorem targetTop_without_sourceTop_cases :
    ∀ u : Finset SplitTwoUnitIndex,
      SplitTwoUnitIndex.negThree ∉ u →
      SplitTwoUnitIndex.sourceTop ∉ u →
      SplitTwoUnitIndex.targetTop ∈ u →
      u = { .targetTop } ∨
      u = { .sourceHole, .targetTop } ∨
      u = { .targetTop, .targetBase } ∨
      u = { .targetTop, .targetHole } ∨
      u = { .sourceHole, .targetTop, .targetBase } ∨
      u = { .sourceHole, .targetTop, .targetHole } ∨
      u = { .targetTop, .targetBase, .targetHole } ∨
      u = { .sourceHole, .targetTop, .targetBase, .targetHole } := by
  native_decide

private theorem sourceTop_without_targetTop_cases :
    ∀ u : Finset SplitTwoUnitIndex,
      SplitTwoUnitIndex.negThree ∉ u →
      SplitTwoUnitIndex.sourceTop ∈ u →
      SplitTwoUnitIndex.targetTop ∉ u →
      u = { .sourceTop } ∨
      u = { .sourceTop, .sourceHole } ∨
      u = { .sourceTop, .targetBase } ∨
      u = { .sourceTop, .targetHole } ∨
      u = { .sourceTop, .sourceHole, .targetBase } ∨
      u = { .sourceTop, .sourceHole, .targetHole } ∨
      u = { .sourceTop, .targetBase, .targetHole } ∨
      u = { .sourceTop, .sourceHole, .targetBase, .targetHole } := by
  native_decide

/--
符号混合と `sourceTop ↔ targetTop` が分かれば、zero-sum 補集合は11型だけ。
-/
private theorem properComplement_eleven_cases :
    ∀ u : Finset SplitTwoUnitIndex,
      SplitTwoUnitIndex.negThree ∉ u →
      u.Nonempty →
      (SplitTwoUnitIndex.sourceHole ∈ u ∨ SplitTwoUnitIndex.targetTop ∈ u) →
      (SplitTwoUnitIndex.sourceTop ∈ u ∨
        SplitTwoUnitIndex.targetBase ∈ u ∨ SplitTwoUnitIndex.targetHole ∈ u) →
      (SplitTwoUnitIndex.targetTop ∈ u → SplitTwoUnitIndex.sourceTop ∈ u) →
      (SplitTwoUnitIndex.sourceTop ∈ u → SplitTwoUnitIndex.targetTop ∈ u) →
      u = { .sourceTop, .targetTop } ∨
      u = { .sourceTop, .targetTop, .targetBase } ∨
      u = { .sourceTop, .targetTop, .targetHole } ∨
      u = { .sourceTop, .targetTop, .targetBase, .targetHole } ∨
      u = { .sourceTop, .sourceHole, .targetTop } ∨
      u = { .sourceTop, .sourceHole, .targetTop, .targetBase } ∨
      u = { .sourceTop, .sourceHole, .targetTop, .targetHole } ∨
      u = { .sourceTop, .sourceHole, .targetTop, .targetBase, .targetHole } ∨
      u = { .sourceHole, .targetBase } ∨
      u = { .sourceHole, .targetHole } ∨
      u = { .sourceHole, .targetBase, .targetHole } := by
  native_decide

/--
full equation と certificate の `sum=1` を引くと、選ばれなかった補集合は zero-sum。
-/
private theorem splitTwo_complement_sum_zero
    {k n r L a b : ℕ}
    {selected : Finset SplitTwoUnitIndex}
    (hEq : SplitTwoHoleEquation k n r L a b)
    (hCert : SplitTwoMinimalPatternCertificate k n r L a b selected) :
    Finset.sum ((Finset.univ : Finset SplitTwoUnitIndex) \ selected)
        (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0 := by
  have hAll := hEq.sixUnit_sum_eq_one
  have hSelected := hCert.nondegenerate.sum_eq_one
  have hSub : selected ⊆ (Finset.univ : Finset SplitTwoUnitIndex) := by
    intro i hi
    simp
  rw [← Finset.sum_sdiff hSub] at hAll
  rw [hSelected] at hAll
  omega

/--
proper complement が空なら selected は full。したがって non-full では補集合は非空。
-/
private theorem splitTwo_complement_nonempty
    {selected : Finset SplitTwoUnitIndex}
    (hNotFull : selected ≠ (Finset.univ : Finset SplitTwoUnitIndex)) :
    ((Finset.univ : Finset SplitTwoUnitIndex) \ selected).Nonempty := by
  by_contra hNot
  have hEmpty : (Finset.univ : Finset SplitTwoUnitIndex) \ selected = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hNot
  apply hNotFull
  ext i
  constructor
  · intro _
    simp
  · intro _
    by_contra hi
    have hiDiff : i ∈ (Finset.univ : Finset SplitTwoUnitIndex) \ selected := by
      simp [hi]
    rw [hEmpty] at hiDiff
    simp at hiDiff

/--
zero-sum 補集合には負項 `sourceHole` または `targetTop` が必ず含まれる。
-/
private theorem complement_has_negative
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (hN : SplitTwoUnitIndex.negThree ∉ u)
    (hu : u.Nonempty)
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    SplitTwoUnitIndex.sourceHole ∈ u ∨ SplitTwoUnitIndex.targetTop ∈ u := by
  by_contra hNot
  simp only [not_or] at hNot
  rcases noNegative_complement_cases u hN hNot.1 hNot.2 hu with
    h | h | h | h | h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hA : 0 < (2 : ℤ) ^ n * (3 : ℤ) ^ k := by positivity
    have hB : 0 < (2 : ℤ) ^ r := by positivity
    have hC : 0 < (2 : ℤ) ^ (r + b) := by positivity
    linarith

/--
zero-sum 補集合には正項 `sourceTop` / `targetBase` / `targetHole` のどれかが必ず含まれる。
-/
private theorem complement_has_positive
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (hN : SplitTwoUnitIndex.negThree ∉ u)
    (hu : u.Nonempty)
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    SplitTwoUnitIndex.sourceTop ∈ u ∨
      SplitTwoUnitIndex.targetBase ∈ u ∨ SplitTwoUnitIndex.targetHole ∈ u := by
  by_contra hNot
  push Not at hNot
  rcases noPositive_complement_cases u hN hNot.1 hNot.2.1 hNot.2.2 hu with
    h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [splitTwoUnitTerm, reduceCtorEq,
    Finset.mem_singleton, not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hD : 0 < (2 : ℤ) ^ a * (3 : ℤ) ^ k := by positivity
    have hE : 0 < (2 : ℤ) ^ (r + L) := by positivity
    linarith

/-- target top が補集合に入る zero-sum なら source top も必ず入る。 -/
private theorem complement_targetTop_imp_sourceTop
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (hb0 : 0 < b)
    (hbL : b < L)
    (hN : SplitTwoUnitIndex.negThree ∉ u)
    (hE : SplitTwoUnitIndex.targetTop ∈ u)
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    SplitTwoUnitIndex.sourceTop ∈ u := by
  by_contra hA
  have hTop := targetBase_add_hole_lt_targetTop (r := r) hb0 hbL
  rcases targetTop_without_sourceTop_cases u hN hA hE with
    h | h | h | h | h | h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hD : 0 < (2 : ℤ) ^ a * (3 : ℤ) ^ k := by positivity
    have hB : 0 < (2 : ℤ) ^ r := by positivity
    have hC : 0 < (2 : ℤ) ^ (r + b) := by positivity
    linarith

/-- source top が補集合に入る zero-sum なら target top も必ず入る。 -/
private theorem complement_sourceTop_imp_targetTop
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (han : a < n)
    (hN : SplitTwoUnitIndex.negThree ∉ u)
    (hA : SplitTwoUnitIndex.sourceTop ∈ u)
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    SplitTwoUnitIndex.targetTop ∈ u := by
  by_contra hE
  have hSource := sourceHole_lt_sourceTop (k := k) han
  rcases sourceTop_without_targetTop_cases u hN hA hE with
    h | h | h | h | h | h | h | h
  all_goals rw [h] at hZero
  all_goals simp only [splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  all_goals
    have hApos : 0 < (2 : ℤ) ^ n * (3 : ℤ) ^ k := by positivity
    have hB : 0 < (2 : ℤ) ^ r := by positivity
    have hC : 0 < (2 : ℤ) ^ (r + b) := by positivity
    linarith


/-- 補集合が具体化されたとき、selected はその universe 補集合に一致する。 -/
private theorem selected_eq_univ_sdiff_of_univ_sdiff_eq
    {selected omitted : Finset SplitTwoUnitIndex}
    (h : (Finset.univ : Finset SplitTwoUnitIndex) \ selected = omitted) :
    selected = (Finset.univ : Finset SplitTwoUnitIndex) \ omitted := by
  ext i
  have hi :
      (i ∈ (Finset.univ : Finset SplitTwoUnitIndex) \ selected) ↔ i ∈ omitted := by
    rw [h]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hi ⊢
  constructor
  · intro hSel hOmit
    exact (hi.mpr hOmit) hSel
  · intro hOmit
    by_contra hSel
    exact hOmit (hi.mp hSel)

/-- `{sourceTop,targetTop}` residual は mod 3 で不可能。 -/
private theorem complement_AE_impossible
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (hk : 0 < k)
    (hAE0 : u = { .sourceTop, .targetTop })
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    False := by
  rw [hAE0] at hZero
  simp only [splitTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_pos,
    SignedTwoThreeUnit.value_neg, pow_zero, mul_one, Finset.sum_singleton] at hZero
  have hMod := congrArg (fun z : ℤ => (z : ZMod 3)) hZero
  push_cast at hMod
  rw [threePow_zmod3_eq_zero_of_pos hk] at hMod
  have hPowZero : (2 : ZMod 3) ^ (r + L) = 0 := by
    simpa using hMod
  exact twoPow_ne_zero_zmod3 (r + L) hPowZero

/-- `{sourceTop,targetTop,targetBase}` residual は `k=1` を強制する。 -/
private theorem complement_AEB_depth_one
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (hk : 0 < k)
    (hL : 0 < L)
    (hAEB : u = { .sourceTop, .targetTop, .targetBase })
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    k = 1 := by
  rw [hAEB] at hZero
  simp only [splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  have hInt :
      (2 : ℤ) ^ n * (3 : ℤ) ^ k + (2 : ℤ) ^ r =
        (2 : ℤ) ^ (r + L) := by
    linarith
  have hNat : 2 ^ n * 3 ^ k + 2 ^ r = 2 ^ (r + L) := by
    exact_mod_cast hInt
  exact sourceTop_plus_twoPow_depth_one hk hL hNat

/-- `{sourceTop,targetTop,targetHole}` residual は `k=1` を強制する。 -/
private theorem complement_AEC_depth_one
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (hk : 0 < k)
    (hbL : b < L)
    (hAEC : u = { .sourceTop, .targetTop, .targetHole })
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    k = 1 := by
  rw [hAEC] at hZero
  simp only [splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  have hInt :
      (2 : ℤ) ^ n * (3 : ℤ) ^ k + (2 : ℤ) ^ (r + b) =
        (2 : ℤ) ^ (r + L) := by
    linarith
  have hNat : 2 ^ n * 3 ^ k + 2 ^ (r + b) = 2 ^ (r + L) := by
    exact_mod_cast hInt
  have hExp : r + L = (r + b) + (L - b) := by omega
  rw [hExp] at hNat
  have hTail : 0 < L - b := by omega
  exact sourceTop_plus_twoPow_depth_one hk hTail hNat

/-- complement `A,E,B,C` では selected は負二項だけになり、sum=1 に反する。 -/
private theorem complement_AEBC_impossible
    {k n r L a b : ℕ}
    {selected u : Finset SplitTwoUnitIndex}
    (hCert : SplitTwoMinimalPatternCertificate k n r L a b selected)
    (hu : u = (Finset.univ : Finset SplitTwoUnitIndex) \ selected)
    (hAEBC : u = { .sourceTop, .targetTop, .targetBase, .targetHole }) :
    False := by
  have hComp :
      (Finset.univ : Finset SplitTwoUnitIndex) \ selected =
        { .sourceTop, .targetTop, .targetBase, .targetHole } := by
    rw [← hu]
    exact hAEBC
  have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
  have hSelected : selected = { .negThree, .sourceHole } := by
    rw [hSel0]
    native_decide
  have hSum := hCert.nondegenerate.sum_eq_one
  rw [hSelected] at hSum
  simp only [splitTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
    SignedTwoThreeUnit.value_neg, Finset.sum_singleton] at hSum
  have hPosD : 0 < (2 : ℤ) ^ a * (3 : ℤ) ^ k := by positivity
  have hPosK : 0 < (3 : ℤ) ^ k := by positivity
  linarith

/-- `{sourceTop,sourceHole,targetTop}` residual は mod 3 で不可能。 -/
private theorem complement_ADE_impossible
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (hk : 0 < k)
    (hADE : u = { .sourceTop, .sourceHole, .targetTop })
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    False := by
  rw [hADE] at hZero
  simp only [splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_pos, SignedTwoThreeUnit.value_neg,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  have hMod := congrArg (fun z : ℤ => (z : ZMod 3)) hZero
  push_cast at hMod
  rw [threePow_zmod3_eq_zero_of_pos hk] at hMod
  have hPowZero : (2 : ZMod 3) ^ (r + L) = 0 := by
    simpa using hMod
  exact twoPow_ne_zero_zmod3 (r + L) hPowZero

/-- complement `A,D,E,B` では selected は `{negThree,targetHole}`。 -/
private theorem complement_ADEB_depth_one
    {k n r L a b : ℕ}
    {selected u : Finset SplitTwoUnitIndex}
    (hk : 0 < k)
    (hCert : SplitTwoMinimalPatternCertificate k n r L a b selected)
    (hu : u = (Finset.univ : Finset SplitTwoUnitIndex) \ selected)
    (hADEB : u = { .sourceTop, .sourceHole, .targetTop, .targetBase }) :
    k = 1 := by
  have hComp :
      (Finset.univ : Finset SplitTwoUnitIndex) \ selected =
        { .sourceTop, .sourceHole, .targetTop, .targetBase } := by
    rw [← hu]
    exact hADEB
  have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
  have hSelected : selected = { .negThree, .targetHole } := by
    rw [hSel0]
    native_decide
  have hSum := hCert.nondegenerate.sum_eq_one
  rw [hSelected] at hSum
  simp only [splitTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
    SignedTwoThreeUnit.value_pos, pow_zero, mul_one, Finset.sum_singleton] at hSum
  have hInt : (3 : ℤ) ^ k + 1 = (2 : ℤ) ^ (r + b) := by linarith
  have hNat : 3 ^ k + 1 = 2 ^ (r + b) := by exact_mod_cast hInt
  exact threePow_add_one_eq_twoPow_depth_one hk hNat

/-- complement `A,D,E,C` では selected は `{negThree,targetBase}`。 -/
private theorem complement_ADEC_depth_one
    {k n r L a b : ℕ}
    {selected u : Finset SplitTwoUnitIndex}
    (hk : 0 < k)
    (hCert : SplitTwoMinimalPatternCertificate k n r L a b selected)
    (hu : u = (Finset.univ : Finset SplitTwoUnitIndex) \ selected)
    (hADEC : u = { .sourceTop, .sourceHole, .targetTop, .targetHole }) :
    k = 1 := by
  have hComp :
      (Finset.univ : Finset SplitTwoUnitIndex) \ selected =
        { .sourceTop, .sourceHole, .targetTop, .targetHole } := by
    rw [← hu]
    exact hADEC
  have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
  have hSelected : selected = { .negThree, .targetBase } := by
    rw [hSel0]
    native_decide
  have hSum := hCert.nondegenerate.sum_eq_one
  rw [hSelected] at hSum
  simp only [splitTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_negThree,
    SignedTwoThreeUnit.value_pos, pow_zero, mul_one, Finset.sum_singleton] at hSum
  have hInt : (3 : ℤ) ^ k + 1 = (2 : ℤ) ^ r := by linarith
  have hNat : 3 ^ k + 1 = 2 ^ r := by exact_mod_cast hInt
  exact threePow_add_one_eq_twoPow_depth_one hk hNat

/-- complement `A,D,E,B,C` では selected は anchor 一項だけで、sum=1 に反する。 -/
private theorem complement_ADEBC_impossible
    {k n r L a b : ℕ}
    {selected u : Finset SplitTwoUnitIndex}
    (hCert : SplitTwoMinimalPatternCertificate k n r L a b selected)
    (hu : u = (Finset.univ : Finset SplitTwoUnitIndex) \ selected)
    (hADEBC :
      u = { .sourceTop, .sourceHole, .targetTop, .targetBase, .targetHole }) :
    False := by
  have hComp :
      (Finset.univ : Finset SplitTwoUnitIndex) \ selected =
        { .sourceTop, .sourceHole, .targetTop, .targetBase, .targetHole } := by
    rw [← hu]
    exact hADEBC
  have hSel0 := selected_eq_univ_sdiff_of_univ_sdiff_eq hComp
  have hSelected : selected = { .negThree } := by
    rw [hSel0]
    native_decide
  have hSum := hCert.nondegenerate.sum_eq_one
  rw [hSelected] at hSum
  simp only [splitTwoUnitTerm, Finset.sum_singleton,
    SignedTwoThreeUnit.value_negThree] at hSum
  have hPosK : 0 < (3 : ℤ) ^ k := by positivity
  linarith

/-- `{sourceHole,targetBase}` residual は mod 3 で不可能。 -/
private theorem complement_DB_impossible
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (hk : 0 < k)
    (hDB : u = { .sourceHole, .targetBase })
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    False := by
  rw [hDB] at hZero
  simp only [splitTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_neg,
    SignedTwoThreeUnit.value_pos, pow_zero, mul_one, Finset.sum_singleton] at hZero
  have hMod := congrArg (fun z : ℤ => (z : ZMod 3)) hZero
  push_cast at hMod
  rw [threePow_zmod3_eq_zero_of_pos hk] at hMod
  have hPowZero : (2 : ZMod 3) ^ r = 0 := by
    simpa using hMod
  exact twoPow_ne_zero_zmod3 r hPowZero

/-- `{sourceHole,targetHole}` residual は mod 3 で不可能。 -/
private theorem complement_DC_impossible
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (hk : 0 < k)
    (hDC : u = { .sourceHole, .targetHole })
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    False := by
  rw [hDC] at hZero
  simp only [splitTwoUnitTerm, Finset.mem_singleton, reduceCtorEq,
    not_false_eq_true, Finset.sum_insert, SignedTwoThreeUnit.value_neg,
    SignedTwoThreeUnit.value_pos, pow_zero, mul_one, Finset.sum_singleton] at hZero
  have hMod := congrArg (fun z : ℤ => (z : ZMod 3)) hZero
  push_cast at hMod
  rw [threePow_zmod3_eq_zero_of_pos hk] at hMod
  have hPowZero : (2 : ZMod 3) ^ (r + b) = 0 := by
    simpa using hMod
  exact twoPow_ne_zero_zmod3 (r + b) hPowZero

/-- `{sourceHole,targetBase,targetHole}` residual は `k≤2` を強制する。 -/
private theorem complement_DBC_depth_le_two
    {k n r L a b : ℕ}
    {u : Finset SplitTwoUnitIndex}
    (hb0 : 0 < b)
    (hDBC : u = { .sourceHole, .targetBase, .targetHole })
    (hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0) :
    k ≤ 2 := by
  rw [hDBC] at hZero
  simp only [splitTwoUnitTerm, Finset.mem_insert, reduceCtorEq,
    Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
    SignedTwoThreeUnit.value_neg, SignedTwoThreeUnit.value_pos,
    pow_zero, mul_one, Finset.sum_singleton] at hZero
  have hInt :
      (2 : ℤ) ^ a * (3 : ℤ) ^ k =
        (2 : ℤ) ^ r + (2 : ℤ) ^ (r + b) := by
    linarith
  have hNat : 2 ^ a * 3 ^ k = 2 ^ r + 2 ^ (r + b) := by
    exact_mod_cast hInt
  have hNatFactor : 2 ^ a * 3 ^ k = 2 ^ r * (1 + 2 ^ b) := by
    rw [pow_add] at hNat
    simpa [mul_add, mul_assoc] using hNat
  have hOddThree : ∃ q : ℕ, 3 ^ k = 2 * q + 1 :=
    SignedTwoThreeUnit.threePow_eq_two_mul_add_one k
  have hOddTarget := one_add_twoPow_oddWitness hb0
  have har :=
    twoPow_mul_oddWitness_exponents_eq hOddThree hOddTarget hNatFactor
  subst a
  have hCore : 3 ^ k = 1 + 2 ^ b :=
    Nat.mul_left_cancel (by positivity) hNatFactor
  exact threePow_eq_one_add_twoPow_depth_le_two hb0 hCore

/--
non-full minimal certificate は depth `k≤2` を強制する。

主定理自身は補集合を構成して 11 型へ分類するだけに留め、
各 residual の算術排除は上の小補題へ分離する。
-/
theorem SplitTwoMinimalPatternCertificate.nonfull_depth_le_two
    {k n r L a b : ℕ}
    {selected : Finset SplitTwoUnitIndex}
    (hk : 0 < k)
    (han : a < n)
    (hb0 : 0 < b)
    (hbL : b < L)
    (hEq : SplitTwoHoleEquation k n r L a b)
    (hCert : SplitTwoMinimalPatternCertificate k n r L a b selected)
    (hNotFull : selected ≠ (Finset.univ : Finset SplitTwoUnitIndex)) :
    k ≤ 2 := by
  let u : Finset SplitTwoUnitIndex :=
    (Finset.univ : Finset SplitTwoUnitIndex) \ selected
  have huEq : u = (Finset.univ : Finset SplitTwoUnitIndex) \ selected := rfl
  have huNonempty : u.Nonempty := by
    dsimp [u]
    exact splitTwo_complement_nonempty hNotFull
  have hN : SplitTwoUnitIndex.negThree ∉ u := by
    simp [u, hCert.anchor_mem]
  have hZero :
      Finset.sum u (fun i => (splitTwoUnitTerm k n r L a b i).value) = 0 := by
    dsimp [u]
    exact splitTwo_complement_sum_zero hEq hCert
  have hNeg := complement_has_negative hN huNonempty hZero
  have hPos := complement_has_positive hN huNonempty hZero
  have hEA :=
    complement_targetTop_imp_sourceTop
      (k := k) (n := n) (r := r) (L := L) (a := a) (b := b) (u := u)
      hb0 hbL hN
  have hAE :=
    complement_sourceTop_imp_targetTop
      (k := k) (n := n) (r := r) (L := L) (a := a) (b := b) (u := u)
      han hN
  have hCases :=
    properComplement_eleven_cases u hN huNonempty hNeg hPos
      (fun h => hEA h hZero) (fun h => hAE h hZero)
  rcases hCases with
      hAE0 | hAEB | hAEC | hAEBC |
      hADE | hADEB | hADEC | hADEBC |
      hDB | hDC | hDBC
  · exact False.elim (complement_AE_impossible hk hAE0 hZero)
  · have hL : 0 < L := by omega
    have hkOne := complement_AEB_depth_one hk hL hAEB hZero
    omega
  · have hkOne := complement_AEC_depth_one hk hbL hAEC hZero
    omega
  · exact False.elim (complement_AEBC_impossible hCert huEq hAEBC)
  · exact False.elim (complement_ADE_impossible hk hADE hZero)
  · have hkOne := complement_ADEB_depth_one hk hCert huEq hADEB
    omega
  · have hkOne := complement_ADEC_depth_one hk hCert huEq hADEC
    omega
  · exact False.elim (complement_ADEBC_impossible hCert huEq hADEBC)
  · exact False.elim (complement_DB_impossible hk hDB hZero)
  · exact False.elim (complement_DC_impossible hk hDC hZero)
  · exact complement_DBC_depth_le_two hb0 hDBC hZero

/-- proper residual なら特に `k≤2`。 -/
theorem SplitTwoMinimalPatternCertificate.properResidual_depth_le_two
    {k n r L a b : ℕ}
    {selected : Finset SplitTwoUnitIndex}
    (hk : 0 < k)
    (han : a < n)
    (hb0 : 0 < b)
    (hbL : b < L)
    (hEq : SplitTwoHoleEquation k n r L a b)
    (hCert : SplitTwoMinimalPatternCertificate k n r L a b selected)
    (hProper : SplitTwoProperResidualPattern selected) :
    k ≤ 2 := by
  apply hCert.nonfull_depth_le_two hk han hb0 hbL hEq
  intro hFull
  have hCard : selected.card = 6 := by
    rw [hFull]
    simp [splitTwoUnitIndex_card]
  have hSmall : selected.card ≤ 5 := hProper.1
  omega

/--
`k≥3` の well-formed split-two では、minimal certificate は full six-term しか残らない。
-/
theorem SplitTwoHoleEquation.largeDepth_exists_fullMinimalPattern
    {k n r L a b : ℕ}
    (hk3 : 3 ≤ k)
    (ha0 : 0 < a)
    (han : a < n)
    (hr : 0 < r)
    (hb0 : 0 < b)
    (hbL : b < L)
    (hEq : SplitTwoHoleEquation k n r L a b) :
    ∃ selected : Finset SplitTwoUnitIndex,
      SplitTwoMinimalPatternCertificate k n r L a b selected ∧
        SplitTwoFullPattern selected := by
  rcases hEq.exists_minimalPatternCertificate (by omega) ha0 hr with
    ⟨selected, hCert⟩
  refine ⟨selected, hCert, ?_⟩
  unfold SplitTwoFullPattern
  by_contra hNotFull
  have hkLe :=
    hCert.nonfull_depth_le_two (by omega) han hb0 hbL hEq hNotFull
  omega

end Mersenne
end Collatz3
