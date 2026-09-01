import CollatzLean.Collatz2.Geometry.CriticalProfile
import Mathlib.Data.Nat.GCD.Basic


/-!
# Collatz2 Geometry: 臨界 Ferrers の 3進符号と最初の相違列

このファイルでは、臨界 Ferrers 高さ列

  h_0, h_1, ..., h_{r-1}

に対する自然な符号

  C_r(h) = Σ_{k<r} 2^(h_k) 3^(r-1-k)

を、右端から一列ずつ付け足す再帰

  C_0(h) = 0,
  C_(n+1)(h) = 3 C_n(h) + 2^(h_n)

として定義する。

中心命題は次の二つ。

* 補題A:
  二つの高さ列が最初に column `j` で異なり、
  それ以後の高さが `a = min (h j) (h' j)` より strict に高いなら、

      C_r(h) - C_r(h')

  に含まれる 2 の冪は exact に `2^a`。

* 補題B:
  さらに

      C_r(h) - C_r(h') = q * 3^r

  なら、`3^r` は odd なので multiplier `q` に含まれる 2 の冪も exact に `2^a`。

`padicVal` は使わず、

  2^a ∣ D かつ 2^(a+1) ∤ D

という形で保持する。
-/

namespace Collatz2
namespace Word

open scoped BigOperators

/--
高さ列 `h` の長さ `r` の臨界 Ferrers 符号。

再帰形は

  C_(n+1) = 3 C_n + 2^(h_n)

であり、既存 `affinePathSum` と同じ重みを逆向きに蓄積する。
-/
def criticalFerrersCode : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 0
  | Nat.succ n, h =>
      3 * criticalFerrersCode n h + 2 ^ h n

@[simp] theorem criticalFerrersCode_zero
    (h : ℕ → ℕ) :
    criticalFerrersCode 0 h = 0 := by
  rfl

@[simp] theorem criticalFerrersCode_succ
    (n : ℕ)
    (h : ℕ → ℕ) :
    criticalFerrersCode (Nat.succ n) h =
      3 * criticalFerrersCode n h + 2 ^ h n := by
  rfl

/--
再帰定義した Ferrers 符号は、通常の affine path sum 展開と一致する。
-/
theorem criticalFerrersCode_eq_sum
    (r : ℕ)
    (h : ℕ → ℕ) :
    criticalFerrersCode r h =
      Finset.sum (Finset.range r)
        (fun k => 2 ^ h k * 3 ^ (r - (k + 1))) := by
  induction r with
  | zero =>
      simp [criticalFerrersCode]
  | succ r ih =>
      rw [criticalFerrersCode_succ, ih]
      rw [Finset.sum_range_succ]
      have hPrefix :
          Finset.sum (Finset.range r)
              (fun k => 2 ^ h k * 3 ^ (Nat.succ r - (k + 1))) =
            3 *
              Finset.sum (Finset.range r)
                (fun k => 2 ^ h k * 3 ^ (r - (k + 1))) := by
        calc
          Finset.sum (Finset.range r)
              (fun k => 2 ^ h k * 3 ^ (Nat.succ r - (k + 1)))
              =
            Finset.sum (Finset.range r)
              (fun k => 3 * (2 ^ h k * 3 ^ (r - (k + 1)))) := by
                apply Finset.sum_congr rfl
                intro k hk
                have hkLt : k < r := Finset.mem_range.mp hk
                have hSub :
                    Nat.succ r - (k + 1) =
                      (r - (k + 1)) + 1 := by
                  omega
                rw [hSub, pow_succ]
                ring
          _ =
            3 *
              Finset.sum (Finset.range r)
                (fun k => 2 ^ h k * 3 ^ (r - (k + 1))) := by
                  rw [Finset.mul_sum]
      rw [hPrefix]
      simp

/--
実際の exponent word の prefix-two-depth profile を入れると、
臨界 Ferrers 符号は既存の `affineConst` そのものになる。
-/
theorem criticalFerrersCode_prefixTwoDepth_eq_affineConst
    (w : Word) :
    criticalFerrersCode (oddSteps w)
        (fun k => prefixTwoDepth w k) =
      affineConst w := by
  rw [criticalFerrersCode_eq_sum]
  rw [← affinePathSum_eq_affineConst]
  unfold affinePathSum affinePathTerm
  rfl

/-- 二つの Ferrers 符号の signed difference。 -/
def criticalFerrersCodeDiffZ
    (r : ℕ)
    (h h' : ℕ → ℕ) : ℤ :=
  (criticalFerrersCode r h : ℤ) -
    (criticalFerrersCode r h' : ℤ)

@[simp] theorem criticalFerrersCodeDiffZ_zero
    (h h' : ℕ → ℕ) :
    criticalFerrersCodeDiffZ 0 h h' = 0 := by
  simp [criticalFerrersCodeDiffZ]

/-- signed difference の一列追加 recurrence。 -/
theorem criticalFerrersCodeDiffZ_succ
    (n : ℕ)
    (h h' : ℕ → ℕ) :
    criticalFerrersCodeDiffZ (Nat.succ n) h h' =
      3 * criticalFerrersCodeDiffZ n h h' +
        ((2 : ℤ) ^ h n - (2 : ℤ) ^ h' n) := by
  unfold criticalFerrersCodeDiffZ
  rw [criticalFerrersCode_succ, criticalFerrersCode_succ]
  push_cast
  ring

/--
最初の `n` 列が等しければ、長さ `n` の Ferrers 符号も等しい。
-/
theorem criticalFerrersCode_eq_of_eq_before
    (n : ℕ)
    (h h' : ℕ → ℕ)
    (hEq : ∀ i : ℕ, i < n → h i = h' i) :
    criticalFerrersCode n h = criticalFerrersCode n h' := by
  revert h h'
  induction n with
  | zero =>
      intro h h' hEq
      rfl
  | succ n ih =>
      intro h h' hEq
      rw [criticalFerrersCode_succ, criticalFerrersCode_succ]
      have hPrefix : ∀ i : ℕ, i < n → h i = h' i := by
        intro i hi
        exact hEq i (by omega)
      have hLast : h n = h' n := hEq n (by omega)
      rw [ih h h' hPrefix, hLast]

/--
整数 `z` に含まれる 2 の冪が exact に `2^a` である、という `padicVal` なしの表現。
-/
def ExactTwoPowZ
    (a : ℕ)
    (z : ℤ) : Prop :=
  ((2 : ℤ) ^ a ∣ z) ∧
    ¬ ((2 : ℤ) ^ (a + 1) ∣ z)

/--
`2^a * odd` は exact に `2^a` を因子として持つ。
-/
theorem exactTwoPowZ_of_eq_twoPow_mul_odd
    {a : ℕ}
    {z q : ℤ}
    (hqOdd : Odd q)
    (hz : z = (2 : ℤ) ^ a * q) :
    ExactTwoPowZ a z := by
  subst z
  constructor
  · exact ⟨q, rfl⟩
  · intro hNext
    rcases hNext with ⟨t, ht⟩
    have hEq :
        (2 : ℤ) ^ a * q =
          (2 : ℤ) ^ a * (2 * t) := by
      calc
        (2 : ℤ) ^ a * q
            = (2 : ℤ) ^ (a + 1) * t := ht
        _ = (2 : ℤ) ^ a * (2 * t) := by
              rw [pow_succ]
              ring
    have hPowNe : (2 : ℤ) ^ a ≠ 0 :=
      pow_ne_zero _ (by norm_num)
    have hqEven : q = 2 * t :=
      mul_left_cancel₀ hPowNe hEq
    rcases hqOdd with ⟨k, hk⟩
    rw [hqEven] at hk
    omega
/--
異なる 2 冪の差では、小さい指数側をくくった quotient は odd。
-/
theorem twoPow_sub_twoPow_eq_twoPow_mul_odd
    {x y a : ℕ}
    (hne : x ≠ y)
    (ha : a = min x y) :
    ∃ q : ℤ,
      Odd q ∧
      (2 : ℤ) ^ x - (2 : ℤ) ^ y =
        (2 : ℤ) ^ a * q := by
  rcases lt_or_gt_of_ne hne with hxy | hyx
  · have haEq : a = x := by
      rw [ha, Nat.min_eq_left (Nat.le_of_lt hxy)]
    let d := y - x
    have hdPos : 0 < d := Nat.sub_pos_of_lt hxy
    have hy : y = x + d := by
      dsimp [d]
      omega
    refine ⟨1 - (2 : ℤ) ^ d, ?_, ?_⟩
    · have hEven : Even ((2 : ℤ) ^ d) :=
        (show Even (2 : ℤ) by norm_num).pow_of_ne_zero
          (Nat.ne_of_gt hdPos)
      exact odd_one.sub_even hEven
    · rw [hy, pow_add, haEq]
      ring
  · have haEq : a = y := by
      rw [ha, Nat.min_eq_right (Nat.le_of_lt hyx)]
    let d := x - y
    have hdPos : 0 < d := Nat.sub_pos_of_lt hyx
    have hx : x = y + d := by
      dsimp [d]
      omega
    refine ⟨(2 : ℤ) ^ d - 1, ?_, ?_⟩
    · have hEven : Even ((2 : ℤ) ^ d) :=
        (show Even (2 : ℤ) by norm_num).pow_of_ne_zero
          (Nat.ne_of_gt hdPos)
      exact hEven.sub_odd odd_one
    · rw [hx, pow_add, haEq]
      ring

/--
両指数が `a` より上なら、2冪差は `2^a * even` の形になる。
-/
theorem twoPow_sub_twoPow_eq_twoPow_mul_even_above
    {a x y : ℕ}
    (hax : a < x)
    (hay : a < y) :
    ∃ t : ℤ,
      (2 : ℤ) ^ x - (2 : ℤ) ^ y =
        (2 : ℤ) ^ a * (2 * t) := by
  let dx := x - (a + 1)
  let dy := y - (a + 1)
  have hx : x = (a + 1) + dx := by
    dsimp [dx]
    omega
  have hy : y = (a + 1) + dy := by
    dsimp [dy]
    omega
  refine ⟨(2 : ℤ) ^ dx - (2 : ℤ) ^ dy, ?_⟩
  rw [hx, hy, pow_add, pow_add, pow_succ]
  ring

/--
補題Aの強い形。

最初の相違列 `j` で低い側の高さを `a` とする。
それ以降の両 profile がすべて `a` より上なら、
符号差は

  2^a * odd

と exact に因数分解できる。
-/
theorem firstDifference_twoPow_oddFactor
    {r j a : ℕ}
    {h h' : ℕ → ℕ}
    (hjLt : j < r)
    (hBefore : ∀ i : ℕ, i < j → h i = h' i)
    (hNe : h j ≠ h' j)
    (ha : a = min (h j) (h' j))
    (hAfter :
      ∀ i : ℕ, j < i → i < r →
        a < h i ∧ a < h' i) :
    ∃ q : ℤ,
      Odd q ∧
        criticalFerrersCodeDiffZ r h h' =
          (2 : ℤ) ^ a * q := by
  revert j a
  induction r with
  | zero =>
      intro j a hjLt hBefore hNe ha hAfter
      omega
  | succ n ih =>
      intro j a hjLt hBefore hNe ha hAfter
      by_cases hjLast : j = n
      · subst j
        have hCodeEq :
            criticalFerrersCode n h =
              criticalFerrersCode n h' :=
          criticalFerrersCode_eq_of_eq_before n h h'
            (fun i hi => hBefore i hi)
        have hPrefixZero :
            criticalFerrersCodeDiffZ n h h' = 0 := by
          unfold criticalFerrersCodeDiffZ
          rw [hCodeEq]
          ring
        rcases twoPow_sub_twoPow_eq_twoPow_mul_odd
            hNe ha with ⟨q, hqOdd, hPow⟩
        refine ⟨q, hqOdd, ?_⟩
        rw [criticalFerrersCodeDiffZ_succ, hPrefixZero]
        simpa using hPow
      · have hjN : j < n := by
          omega
        have hAfterN :
            ∀ i : ℕ, j < i → i < n →
              a < h i ∧ a < h' i := by
          intro i hji hin
          exact hAfter i hji (by omega)
        rcases ih (j := j) (a := a) hjN hBefore hNe ha hAfterN with
          ⟨q, hqOdd, hqEq⟩
        have hAtN : a < h n ∧ a < h' n :=
          hAfter n hjN (by omega)
        rcases twoPow_sub_twoPow_eq_twoPow_mul_even_above
            hAtN.1 hAtN.2 with ⟨t, ht⟩
        refine ⟨3 * q + 2 * t, ?_, ?_⟩
        · rcases hqOdd with ⟨k, hk⟩
          refine ⟨3 * k + t + 1, ?_⟩
          rw [hk]
          ring
        · rw [criticalFerrersCodeDiffZ_succ, hqEq, ht]
          ring

/--
補題A。

最初の相違列の低い高さ `a` は、Ferrers 符号差の exact 2進深さである。
-/
theorem firstDifference_twoPow_exact
    {r j a : ℕ}
    {h h' : ℕ → ℕ}
    (hjLt : j < r)
    (hBefore : ∀ i : ℕ, i < j → h i = h' i)
    (hNe : h j ≠ h' j)
    (ha : a = min (h j) (h' j))
    (hAfter :
      ∀ i : ℕ, j < i → i < r →
        a < h i ∧ a < h' i) :
    ((2 : ℤ) ^ a ∣ criticalFerrersCodeDiffZ r h h') ∧
      ¬ ((2 : ℤ) ^ (a + 1) ∣ criticalFerrersCodeDiffZ r h h') := by
  rcases firstDifference_twoPow_oddFactor
      hjLt hBefore hNe ha hAfter with ⟨q, hqOdd, hEq⟩
  exact exactTwoPowZ_of_eq_twoPow_mul_odd hqOdd hEq

/--
補題B。

  D = q * 3^r

で `D` が exact に `2^a` を持つなら、odd な `3^r` を除いた multiplier `q` も
exact に `2^a` を持つ。
-/
theorem collisionMultiplier_twoPow_exact
    {r a : ℕ}
    {h h' : ℕ → ℕ}
    {q : ℤ}
    (hExact : ExactTwoPowZ a (criticalFerrersCodeDiffZ r h h'))
    (hCollision :
      criticalFerrersCodeDiffZ r h h' =
        q * (3 : ℤ) ^ r) :
    ExactTwoPowZ a q := by
  constructor
  · have hDivAbs :
        2 ^ a ∣ (criticalFerrersCodeDiffZ r h h').natAbs := by
      rw [← Int.natCast_dvd]
      simpa using hExact.1
    have hAbsEq :
        (criticalFerrersCodeDiffZ r h h').natAbs =
          q.natAbs * 3 ^ r := by
      rw [hCollision, Int.natAbs_mul, Int.natAbs_pow]
      norm_num
    rw [hAbsEq] at hDivAbs
    have h23 : Nat.Coprime 2 3 := by
      decide
    have hCop : Nat.Coprime (2 ^ a) (3 ^ r) := by
      exact ((h23.pow_left a).symm.pow_left r).symm
    have hDivQAbs : 2 ^ a ∣ q.natAbs :=
      hCop.dvd_of_dvd_mul_right hDivAbs
    have hDivQCast : ((2 ^ a : ℕ) : ℤ) ∣ q :=
      (Int.natCast_dvd).2 hDivQAbs
    simpa using hDivQCast
  · intro hNext
    apply hExact.2
    rw [hCollision]
    exact dvd_mul_of_dvd_left hNext ((3 : ℤ) ^ r)

end Word
end Collatz2
