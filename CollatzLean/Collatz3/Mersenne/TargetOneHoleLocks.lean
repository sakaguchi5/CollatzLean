import CollatzLean.Collatz3.Mersenne.TargetOneHoleGcd
import CollatzLean.Collatz3.Critical.Beatty
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: target-one の上端・下端 lock

`TargetOneHoleGeometricData` の `q<t` branch では、geometric equation は
単なる二つの幾何和の差ではなく、base `2^n` で二つの定数 block を持つ。

このファイルでは新しい structure を導入せず、次の三種類を derived theorem として固定する。

* `baseBlock_normalForm`:
  `3^k` を lower block と upper block の和に exact に分ける。
* `beattyIndex_eq`:
  最上位桁の位置 `r+n(t-1)` が既存 `Critical.beattyIndex k` と exact に一致する。
* `twoAdicCut_eq`:
  block の切替位置 `nq` が一つの整数の exact 2-adic valuation になる。

従って large-depth residual では、`t` は Beatty roof から、`q` は 2-adic valuation から
それぞれ復元できる。
-/

namespace Collatz3
namespace Mersenne

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- 正の長さの geometric sum は正。 -/
private theorem targetGeomSum_pos
    {x t : ℕ}
    (ht : 0 < t) :
    0 < targetGeomSum x t := by
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [targetGeomSum_succ]
  omega

/-- 長さを増やすと geometric sum は減らない。 -/
private theorem targetGeomSum_mono_length
    {x a b : ℕ}
    (hab : a ≤ b) :
    targetGeomSum x a ≤ targetGeomSum x b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [targetGeomSum_add]
  omega

/-- base が 2 以上なら `G_t(x) < x^t`。 -/
private theorem targetGeomSum_lt_pow
    {x t : ℕ}
    (hx : 2 ≤ x) :
    targetGeomSum x t < x ^ t := by
  induction t with
  | zero =>
      simp [targetGeomSum]
  | succ t ih =>
      rw [targetGeomSum_succ, pow_succ]
      have hOneLt : 1 < x := by omega
      have hSuccLe : targetGeomSum x t + 1 ≤ x ^ t := by
        omega
      calc
        x * targetGeomSum x t + 1
            < x * targetGeomSum x t + x := Nat.add_lt_add_left hOneLt _
        _ = x * (targetGeomSum x t + 1) := by ring
        _ ≤ x * x ^ t := Nat.mul_le_mul_left x hSuccLe
        _ = x ^ t * x := by ring

/-- 正長の geometric sum は最上位項の 2 倍より小さい。 -/
private theorem targetGeomSum_lt_two_mul_last
    {x t : ℕ}
    (hx : 2 ≤ x)
    (ht : 0 < t) :
    targetGeomSum x t < 2 * x ^ (t - 1) := by
  obtain ⟨s, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have hPrev := targetGeomSum_lt_pow (x := x) (t := s) hx
  have hG1 : targetGeomSum x 1 = 1 := by
    simp [targetGeomSum]
  change
    targetGeomSum x (s + 1) <
      2 * x ^ s
  rw [targetGeomSum_add, hG1, mul_one]
  omega
/--
base `2^n` で見た二つの定数 block の exact normal form。

`q` 桁の lower block の digit は `2^r-1`、残り `t-q` 桁の upper block の digit は `2^r`。
特に `r=1` では `1...1 | 2...2`、`r=2` では `3...3 | 4...4` になる。
-/
theorem TargetOneHoleGeometricData.baseBlock_normalForm
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b) :
    3 ^ k =
      (2 ^ r - 1) * targetGeomSum (2 ^ n) h.q +
        2 ^ r * (2 ^ n) ^ h.q *
          targetGeomSum (2 ^ n) (h.t - h.q) := by
  have hDecomp : h.q + (h.t - h.q) = h.t := by
    exact Nat.add_sub_of_le h.q_le_t
  have hSplit :
      targetGeomSum (2 ^ n) h.t =
        targetGeomSum (2 ^ n) h.q +
          (2 ^ n) ^ h.q * targetGeomSum (2 ^ n) (h.t - h.q) := by
    calc
      targetGeomSum (2 ^ n) h.t =
          targetGeomSum (2 ^ n) (h.q + (h.t - h.q)) := by rw [hDecomp]
      _ = _ := targetGeomSum_add (2 ^ n) h.q (h.t - h.q)
  have hPowOne : 1 ≤ 2 ^ r :=
    Nat.one_le_pow r 2 (by norm_num)
  have hCoeff :
      2 ^ r * targetGeomSum (2 ^ n) h.q =
        (2 ^ r - 1) * targetGeomSum (2 ^ n) h.q +
          targetGeomSum (2 ^ n) h.q := by
    calc
      2 ^ r * targetGeomSum (2 ^ n) h.q =
          ((2 ^ r - 1) + 1) * targetGeomSum (2 ^ n) h.q := by
            rw [Nat.sub_add_cancel hPowOne]
      _ = _ := by ring
  have hEq := h.equation
  rw [hSplit, Nat.mul_add, hCoeff] at hEq
  simp only [mul_assoc] at hEq ⊢
  omega

/-- even exit-depth `r=1` の block normal form。 -/
theorem TargetOneHoleGeometricData.even_baseBlock_normalForm
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b) :
    3 ^ k =
      targetGeomSum (2 ^ n) h.q +
        2 * (2 ^ n) ^ h.q * targetGeomSum (2 ^ n) (h.t - h.q) := by
  have hMain := h.baseBlock_normalForm
  norm_num at hMain ⊢
  exact hMain

/-- odd exit-depth `r=2` の block normal form。 -/
theorem TargetOneHoleGeometricData.odd_baseBlock_normalForm
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b) :
    3 ^ k =
      3 * targetGeomSum (2 ^ n) h.q +
        4 * (2 ^ n) ^ h.q * targetGeomSum (2 ^ n) (h.t - h.q) := by
  have hMain := h.baseBlock_normalForm
  norm_num at hMain ⊢
  exact hMain

/--
`q<t` では `3^k` の最上位 base-`2^n` digit の位置が exact に決まる。

`2^(r+n(t-1)) < 3^k < 2^(r+n(t-1)+1)` を示し、
既存の power-form Beatty index の最小性と衝突させる。
-/
theorem TargetOneHoleGeometricData.beattyIndex_eq
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn : 0 < n)
    (hr : 0 < r)
    (hqt : h.q < h.t) :
    Critical.beattyIndex k = r + n * (h.t - 1) := by
  let x : ℕ := 2 ^ n
  let R : ℕ := 2 ^ r
  have hxTwo : 2 ≤ x := by
    dsimp [x]
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ n)
    norm_num at hp ⊢
    exact hp
  have hRPos : 0 < R := by
    dsimp [R]
    positivity
  have hRTwo : 2 ≤ R := by
    dsimp [R]
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ r)
    norm_num at hp ⊢
    exact hp
  have htPos : 0 < h.t := by omega
  have hqPrev : h.q ≤ h.t - 1 := by omega
  have hGtSplit :
      targetGeomSum x h.t =
        targetGeomSum x (h.t - 1) + x ^ (h.t - 1) := by
    have hAdd := targetGeomSum_add x (h.t - 1) 1
    have htEq : (h.t - 1) + 1 = h.t := by omega
    have hG1 : targetGeomSum x 1 = 1 := by
      simp [targetGeomSum]
    rw [htEq, hG1, mul_one] at hAdd
    exact hAdd
  have hGqLe :
      targetGeomSum x h.q ≤ targetGeomSum x (h.t - 1) :=
    targetGeomSum_mono_length hqPrev
  have hPrevPos : 0 < targetGeomSum x (h.t - 1) := by
    apply targetGeomSum_pos
    have hqPos : 0 < h.q := h.q_pos
    omega
  have hTailStrict :
      targetGeomSum x h.q < R * targetGeomSum x (h.t - 1) := by
    have hTwice :
        targetGeomSum x (h.t - 1) <
          2 * targetGeomSum x (h.t - 1) := by
      omega
    have hMul :
        2 * targetGeomSum x (h.t - 1) ≤
          R * targetGeomSum x (h.t - 1) :=
      Nat.mul_le_mul_right (targetGeomSum x (h.t - 1)) hRTwo
    exact lt_of_le_of_lt hGqLe (lt_of_lt_of_le hTwice hMul)
  have hEq := h.equation
  change 3 ^ k + targetGeomSum x h.q = R * targetGeomSum x h.t at hEq
  rw [hGtSplit, Nat.mul_add] at hEq
  have hLowerLead :
      R * x ^ (h.t - 1) < 3 ^ k := by
    omega
  have hGqPos : 0 < targetGeomSum x h.q :=
    targetGeomSum_pos h.q_pos
  have hKltRhs :
      3 ^ k < R * targetGeomSum x h.t := by
    have hEq0 := h.equation
    change 3 ^ k + targetGeomSum x h.q = R * targetGeomSum x h.t at hEq0
    omega
  have hGeomUpper :
      targetGeomSum x h.t < 2 * x ^ (h.t - 1) :=
    targetGeomSum_lt_two_mul_last hxTwo htPos
  have hUpperLead :
      3 ^ k < R * (2 * x ^ (h.t - 1)) := by
    exact lt_trans hKltRhs ((Nat.mul_lt_mul_left hRPos).2 hGeomUpper)
  have hPowLower :
      2 ^ (r + n * (h.t - 1)) = R * x ^ (h.t - 1) := by
    dsimp [R, x]
    rw [pow_add, pow_mul]
  have hPowUpper :
      2 ^ (r + n * (h.t - 1) + 1) =
        R * (2 * x ^ (h.t - 1)) := by
    rw [pow_succ, hPowLower]
    ring
  have hLower :
      2 ^ (r + n * (h.t - 1)) < 3 ^ k := by
    rw [hPowLower]
    exact hLowerLead
  have hUpper :
      3 ^ k < 2 ^ (r + n * (h.t - 1) + 1) := by
    rw [hPowUpper]
    exact hUpperLead
  apply le_antisymm
  · exact Critical.beattyIndex_le_of_upper (Nat.le_of_lt hUpper)
  · by_contra hNot
    have hIdxLt : Critical.beattyIndex k < r + n * (h.t - 1) := by
      omega
    have hBeattyUpper := Critical.beattyIndex_upper k
    have hExpLe :
        Critical.beattyIndex k + 1 ≤ r + n * (h.t - 1) := by
      omega
    have hPowLe :
        2 ^ (Critical.beattyIndex k + 1) ≤
          2 ^ (r + n * (h.t - 1)) :=
      Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hExpLe
    have hBad : 3 ^ k ≤ 2 ^ (r + n * (h.t - 1)) :=
      le_trans hBeattyUpper hPowLe
    exact (not_lt_of_ge hBad) hLower

/-- `2^a * odd` の 2-adic valuation は exact に `a`。 -/
private theorem padicValNat_twoPow_mul_odd
    (a m : ℕ)
    (hm : Odd m) :
    padicValNat 2 (2 ^ a * m) = a := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    norm_num at hm
  have hNot : ¬ 2 ∣ m := by
    rintro ⟨c, hc⟩
    rcases hm with ⟨d, hd⟩
    omega
  rw [padicValNat.mul (by positivity) hm0]
  rw [padicValNat.prime_pow]
  rw [padicValNat.eq_zero_of_not_dvd hNot]
  omega

/-- 正の 2 冪を因子に持つ積から 1 を引くと奇数。 -/
private theorem odd_twoPow_mul_sub_one
    {r m : ℕ}
    (hr : 0 < r)
    (hm : 0 < m) :
    Odd (2 ^ r * m - 1) := by
  obtain ⟨e, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  let C : ℕ := 2 ^ e * m
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  have hEvenForm : 2 ^ (e + 1) * m = 2 * C := by
    dsimp [C]
    rw [pow_succ]
    ring
  rw [hEvenForm]
  refine ⟨C - 1, ?_⟩
  omega

/--
block cut を exact factorization として書く。

左辺は元の target-one の affine numerator に対応し、右辺は
`(2^n)^q` と奇数因子の積になる。
-/
theorem TargetOneHoleGeometricData.twoAdicCut_factorization
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hqt : h.q < h.t) :
    (2 ^ n - 1) * 3 ^ k + (2 ^ r - 1) =
      (2 ^ n) ^ h.q *
        (2 ^ r * (2 ^ n) ^ (h.t - h.q) - 1) := by
  let x : ℕ := 2 ^ n
  let R : ℕ := 2 ^ r
  let s : ℕ := h.t - h.q
  have hxOne : 1 ≤ x := by
    dsimp [x]
    have hxPos : 0 < 2 ^ n := by positivity
    omega
  have hROne : 1 ≤ R := by
    dsimp [R]
    have hRPos : 0 < 2 ^ r := by positivity
    omega
  have hqOne : 1 ≤ x ^ h.q := by
    exact Nat.one_le_pow h.q x (by omega)
  have htOne : 1 ≤ x ^ h.t := by
    exact Nat.one_le_pow h.t x (by omega)
  have hsPos : 0 < s := by
    dsimp [s]
    omega
  have hRsOne : 1 ≤ R * x ^ s := by
    have hxPowPos : 0 < x ^ s := by
      positivity
    have hRPos : 0 < R := by
      positivity
    exact Nat.mul_pos hRPos hxPowPos
  have hGeomQ :
      targetGeomSum x h.q * (x - 1) = x ^ h.q - 1 := by
    unfold targetGeomSum
    exact geom_sum_mul_of_one_le hxOne h.q
  have hGeomT :
      targetGeomSum x h.t * (x - 1) = x ^ h.t - 1 := by
    unfold targetGeomSum
    exact geom_sum_mul_of_one_le hxOne h.t
  have hMul := congrArg (fun z : ℕ => z * (x - 1)) h.equation
  change
      (3 ^ k + targetGeomSum x h.q) * (x - 1) =
        (R * targetGeomSum x h.t) * (x - 1) at hMul
  rw [Nat.add_mul, hGeomQ, mul_assoc, hGeomT] at hMul
  have hXqDecomp : x ^ h.q = (x ^ h.q - 1) + 1 := by
    exact (Nat.sub_add_cancel hqOne).symm
  have hRtDecomp :
      R * (x ^ h.t - 1) + R = R * x ^ h.t := by
    calc
      R * (x ^ h.t - 1) + R = R * ((x ^ h.t - 1) + 1) := by ring
      _ = R * x ^ h.t := by rw [Nat.sub_add_cancel htOne]
  have hCommon :
      3 ^ k * (x - 1) + R + x ^ h.q = R * x ^ h.t + 1 := by
    omega
  have hDecomp : h.q + s = h.t := by
    dsimp [s]
    omega
  have hPowDecomp : x ^ h.q * x ^ s = x ^ h.t := by
    rw [← pow_add, hDecomp]
  have hFactorAdd :
      x ^ h.q * (R * x ^ s - 1) + x ^ h.q = R * x ^ h.t := by
    calc
      x ^ h.q * (R * x ^ s - 1) + x ^ h.q =
          x ^ h.q * ((R * x ^ s - 1) + 1) := by ring
      _ = x ^ h.q * (R * x ^ s) := by rw [Nat.sub_add_cancel hRsOne]
      _ = R * (x ^ h.q * x ^ s) := by ring
      _ = R * x ^ h.t := by rw [hPowDecomp]
  have hRDecomp : R = (R - 1) + 1 := by
    exact (Nat.sub_add_cancel hROne).symm
  change
      (x - 1) * 3 ^ k + (R - 1) =
        x ^ h.q * (R * x ^ s - 1)
  rw [Nat.mul_comm (x - 1) (3 ^ k)]
  omega

/--
`q<t` の切替位置は exact に一つの 2-adic valuation から復元できる。

`v₂((2^n-1)3^k + (2^r-1)) = nq`。
-/
theorem TargetOneHoleGeometricData.twoAdicCut_eq
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hr : 0 < r)
    (hqt : h.q < h.t) :
    padicValNat 2 ((2 ^ n - 1) * 3 ^ k + (2 ^ r - 1)) =
      n * h.q := by
  have hFact := h.twoAdicCut_factorization hqt
  let F : ℕ := 2 ^ r * (2 ^ n) ^ (h.t - h.q) - 1
  have hTailPos : 0 < (2 ^ n) ^ (h.t - h.q) := by
    positivity
  have hFOdd : Odd F := by
    dsimp [F]
    exact odd_twoPow_mul_sub_one hr hTailPos
  have hFact' :
      (2 ^ n - 1) * 3 ^ k + (2 ^ r - 1) =
        2 ^ (n * h.q) * F := by
    rw [hFact]
    dsimp [F]
    rw [← pow_mul]
  have hValEq := congrArg (padicValNat 2) hFact'
  have hValRight := padicValNat_twoPow_mul_odd (n * h.q) F hFOdd
  rw [hValRight] at hValEq
  exact hValEq

end Mersenne
end Collatz3
