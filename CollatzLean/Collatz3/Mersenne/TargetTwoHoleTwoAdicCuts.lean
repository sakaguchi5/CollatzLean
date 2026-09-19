import CollatzLean.Collatz3.Mersenne.TargetTwoHoleGeometric
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: target-two-hole の二段 2-adic cut

target-two-hole の三 geometric phase について、base `2^n` の二つの切替位置を
exact 2-adic valuation として回収する。

wrapped:

* first cut: `v2((2^n-1)3^k + (2^r-1)) = nq-1`
* second cut: normalized quotient `F` に対し `v2(F+1)=n(u-q)`

split-forward (`q<=u`):

* first cut: `v2((2^n-1)3^k + (2^r-1)) = nq`
* second cut: `v2(F+1)=r+n(u-q)`

split-reverse (`u<q`):

* first cut: `v2((2^n-1)3^k + (2^r-1)) = nu+r`
* second cut: normalized quotient `H` に対し
  `v2(H+1)=n(q-u)-r`

これにより、phase が決まれば二つの cut は整数から一意に復元できる。
-/

namespace Collatz3
namespace Mersenne

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- `2^a * odd` の 2-adic valuation は exact に `a`。 -/
private theorem targetTwo_padicValNat_twoPow_mul_odd
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

/-- `2*m` の valuation は positive `m` に対して一つ増える。 -/
private theorem targetTwo_padicValNat_two_mul
    (m : ℕ)
    (hm : m ≠ 0) :
    padicValNat 2 (2 * m) = 1 + padicValNat 2 m := by
  rw [padicValNat.mul (by norm_num) hm]
  have hTwo : padicValNat 2 2 = 1 := by
    simp only [Order.lt_two_iff, Std.le_refl, padicValNat_base]
  rw [hTwo]

/-- positive 2 冪を因子に持つ積から 1 を引くと奇数。 -/
private theorem targetTwo_odd_twoPow_mul_sub_one
    {e m : ℕ}
    (he : 0 < e)
    (hm : 0 < m) :
    Odd (2 ^ e * m - 1) := by
  obtain ⟨d, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  let C : ℕ := 2 ^ d * m
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  have hEvenForm : 2 ^ (d + 1) * m = 2 * C := by
    dsimp [C]
    rw [pow_succ]
    ring
  rw [hEvenForm]
  refine ⟨C - 1, ?_⟩
  omega

/-- `F+1=2^e*m`, `e>0`, `m>0` なら `F` は奇数。 -/
private theorem targetTwo_odd_of_succ_eq_twoPow_mul
    {F e m : ℕ}
    (he : 0 < e)
    (hm : 0 < m)
    (h : F + 1 = 2 ^ e * m) :
    Odd F := by
  obtain ⟨d, hd⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
  rw [hd, pow_succ] at h
  let C : ℕ := 2 ^ d * m
  have hCPos : 0 < C := by
    dsimp [C]
    positivity
  have hTwoC : 2 ^ d * 2 * m = 2 * C := by
    dsimp [C]
    ring
  rw [hTwoC] at h
  refine ⟨C - 1, ?_⟩
  omega

/-- positive base `x` の geometric sum identity。 -/
private theorem targetTwo_geom_mul
    {x t : ℕ}
    (hx : 1 ≤ x) :
    targetGeomSum x t * (x - 1) = x ^ t - 1 := by
  unfold targetGeomSum
  exact geom_sum_mul_of_one_le hx t

/-! ## wrapped phase -/

/-- wrapped phase の first-cut 後に残る odd quotient。 -/
def TargetTwoHoleWrappedGeometricData.cutQuotient
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b) : ℕ :=
  2 ^ (r + 1) * (2 ^ n) ^ (h.t - h.q) -
    (1 + (2 ^ n) ^ (h.u - h.q))

/-- wrapped quotient に 1 を足すと第二 cut が factor として現れる。 -/
theorem TargetTwoHoleWrappedGeometricData.cutQuotient_add_one_factorization
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b)
    (hr : 0 < r) :
    h.cutQuotient + 1 =
      (2 ^ n) ^ (h.u - h.q) *
        (2 ^ (r + 1) * (2 ^ n) ^ (h.t - h.u) - 1) := by
  let x : ℕ := 2 ^ n
  let R2 : ℕ := 2 ^ (r + 1)
  let d : ℕ := h.u - h.q
  let e : ℕ := h.t - h.u
  have hqLtU : h.q < h.u := h.q_lt_u
  have huLeT : h.u ≤ h.t := h.u_le_t
  have hqLeT : h.q ≤ h.t :=
    le_trans (Nat.le_of_lt hqLtU) huLeT
  have hdPos : 0 < d := by
    dsimp [d]
    exact Nat.sub_pos_of_lt hqLtU
  have hqe : h.q + d + e = h.t := by
    dsimp [d, e]
    omega
  have hde : d + e = h.t - h.q := by
    dsimp [d, e]
    omega
  have hR2Two : 2 ≤ R2 := by
    dsimp [R2]
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ r + 1)
    norm_num at hp ⊢
    exact hp
  have hxPos : 0 < x := by dsimp [x]; positivity
  have hA :
      R2 * x ^ (h.t - h.q) =
        x ^ d * (R2 * x ^ e) := by
    calc
      R2 * x ^ (h.t - h.q)
          = R2 * x ^ (d + e) := by rw [hde]
      _ = R2 * (x ^ d * x ^ e) := by rw [pow_add]
      _ = x ^ d * (R2 * x ^ e) := by ring
  have hCoeffOne : 1 ≤ R2 * x ^ e := by
    have hR2Pos : 0 < R2 := by omega
    have hxPowPos : 0 < x ^ e := Nat.pow_pos hxPos
    have hProdPos : 0 < R2 * x ^ e :=
      Nat.mul_pos hR2Pos hxPowPos
    omega
  have hProdAdd :
      x ^ d * (R2 * x ^ e - 1) + x ^ d =
        R2 * x ^ (h.t - h.q) := by
    calc
      x ^ d * (R2 * x ^ e - 1) + x ^ d =
          x ^ d * ((R2 * x ^ e - 1) + 1) := by ring
      _ = x ^ d * (R2 * x ^ e) := by
        rw [Nat.sub_add_cancel hCoeffOne]
      _ = R2 * x ^ (h.t - h.q) := hA.symm
  have hSubLe : 1 + x ^ d ≤ R2 * x ^ (h.t - h.q) := by
    have hxPowEPos : 0 < x ^ e := Nat.pow_pos hxPos
    have hTailPos : 0 < R2 * x ^ e - 1 := by
      have hFour : 2 ≤ R2 * x ^ e := by
        exact le_trans hR2Two (Nat.le_mul_of_pos_right R2 hxPowEPos)
      omega
    have hxPowDPos : 0 < x ^ d := Nat.pow_pos hxPos
    have hExtraPos :
        0 < x ^ d * (R2 * x ^ e - 1) :=
      Nat.mul_pos hxPowDPos hTailPos
    omega
  change
      R2 * x ^ (h.t - h.q) - (1 + x ^ d) + 1 =
        x ^ d * (R2 * x ^ e - 1)
  omega

/-- wrapped quotient は奇数。 -/
theorem TargetTwoHoleWrappedGeometricData.cutQuotient_odd
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b)
    (hn : 0 < n)
    (hr : 0 < r) :
    Odd h.cutQuotient := by
  have hSecond := h.cutQuotient_add_one_factorization hr
  let C : ℕ :=
    2 ^ (r + 1) * (2 ^ n) ^ (h.t - h.u) - 1
  have hCPos : 0 < C := by
    dsimp [C]
    have hCoeff : 2 ≤ 2 ^ (r + 1) := by
      have hp := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega : 1 ≤ r + 1)
      norm_num at hp ⊢
      exact hp
    have hMul : 2 ≤ 2 ^ (r + 1) * (2 ^ n) ^ (h.t - h.u) :=
      le_trans hCoeff (Nat.le_mul_of_pos_right _ (by positivity))
    omega
  have hePos : 0 < n * (h.u - h.q) := by
    have hGapPos : 0 < h.u - h.q :=
      Nat.sub_pos_of_lt h.q_lt_u
    exact Nat.mul_pos hn hGapPos
  have hSecond' :
      h.cutQuotient + 1 =
        2 ^ (n * (h.u - h.q)) * C := by
    dsimp [C]
    simpa [pow_mul] using hSecond
  exact targetTwo_odd_of_succ_eq_twoPow_mul hePos hCPos hSecond'

/-- wrapped first cut の exact factorization。 -/
theorem TargetTwoHoleWrappedGeometricData.firstCut_factorization
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b)
    (hr : 0 < r) :
    2 * ((2 ^ n - 1) * 3 ^ k + (2 ^ r - 1)) =
      (2 ^ n) ^ h.q * h.cutQuotient := by
  let x : ℕ := 2 ^ n
  let R : ℕ := 2 ^ r
  let R2 : ℕ := 2 ^ (r + 1)
  let d : ℕ := h.u - h.q
  have hxPos : 0 < x := by
    dsimp [x]
    exact Nat.pow_pos (by norm_num)
  have hxOne : 1 ≤ x := by omega
  have hGeomQ := targetTwo_geom_mul (x := x) (t := h.q) hxOne
  have hGeomU := targetTwo_geom_mul (x := x) (t := h.u) hxOne
  have hGeomT := targetTwo_geom_mul (x := x) (t := h.t) hxOne
  have hMul := congrArg (fun z : ℕ => z * (x - 1)) h.equation
  change
      (2 * 3 ^ k + targetGeomSum x h.q + targetGeomSum x h.u) * (x - 1) =
        R2 * targetGeomSum x h.t * (x - 1) at hMul
  rw [Nat.add_mul, Nat.add_mul, hGeomQ, hGeomU] at hMul
  rw [mul_assoc R2 (targetGeomSum x h.t) (x - 1), hGeomT] at hMul
  have hR2 : R2 = 2 * R := by
    dsimp [R2, R]
    rw [pow_succ]
    ring
  rw [hR2] at hMul
  have hCommon :
      2 * ((x - 1) * 3 ^ k + (R - 1)) + x ^ h.q + x ^ h.u =
        2 * R * x ^ h.t := by
    have hRPos : 0 < R := by
      dsimp [R]
      exact Nat.pow_pos (by norm_num)
    have hROne : 1 ≤ R := by omega
    have hQOne : 1 ≤ x ^ h.q := Nat.one_le_pow h.q x hxOne
    have hUOne : 1 ≤ x ^ h.u := Nat.one_le_pow h.u x hxOne
    have hTOne : 1 ≤ x ^ h.t := Nat.one_le_pow h.t x hxOne
    have hLeft :
        2 * ((x - 1) * 3 ^ k + (R - 1)) + x ^ h.q + x ^ h.u =
          (2 * 3 ^ k * (x - 1) + (x ^ h.q - 1) + (x ^ h.u - 1)) + 2 * R := by
      have hRSub : R - 1 + 1 = R := Nat.sub_add_cancel hROne
      have hQSub : x ^ h.q - 1 + 1 = x ^ h.q := Nat.sub_add_cancel hQOne
      have hUSub : x ^ h.u - 1 + 1 = x ^ h.u := Nat.sub_add_cancel hUOne
      ring_nf
      omega
    have hRight :
        2 * R * (x ^ h.t - 1) + 2 * R = 2 * R * x ^ h.t := by
      calc
        2 * R * (x ^ h.t - 1) + 2 * R =
            2 * R * ((x ^ h.t - 1) + 1) := by ring
        _ = 2 * R * x ^ h.t := by rw [Nat.sub_add_cancel hTOne]
    calc
      2 * ((x - 1) * 3 ^ k + (R - 1)) + x ^ h.q + x ^ h.u =
          (2 * 3 ^ k * (x - 1) + (x ^ h.q - 1) + (x ^ h.u - 1)) + 2 * R := hLeft
      _ = 2 * R * (x ^ h.t - 1) + 2 * R := by rw [hMul]
      _ = 2 * R * x ^ h.t := hRight
  have hFsum :
      h.cutQuotient + 1 + x ^ d =
        2 * R * x ^ (h.t - h.q) := by
    have hSecond := h.cutQuotient_add_one_factorization hr
    have hSecond' :
        h.cutQuotient + 1 =
          x ^ d * (2 * R * x ^ (h.t - h.u) - 1) := by
      simpa [x, R, d, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hSecond
    have hqLtU : h.q < h.u := h.q_lt_u
    have huLeT : h.u ≤ h.t := h.u_le_t
    have hdecomp : d + (h.t - h.u) = h.t - h.q := by
      dsimp [d]
      omega
    have hRPos : 0 < R := by
      dsimp [R]
      exact Nat.pow_pos (by norm_num)
    have hxTailPos : 0 < x ^ (h.t - h.u) :=
      Nat.pow_pos hxPos
    have hCoeffOne : 1 ≤ 2 * R * x ^ (h.t - h.u) := by
      have hTwoRPos : 0 < 2 * R :=
        Nat.mul_pos (by norm_num) hRPos
      have hProdPos : 0 < 2 * R * x ^ (h.t - h.u) :=
        Nat.mul_pos hTwoRPos hxTailPos
      omega
    change
      h.cutQuotient + 1 + x ^ d =
        2 * R * x ^ (h.t - h.q)
    rw [hSecond']
    calc
      x ^ d * (2 * R * x ^ (h.t - h.u) - 1) + x ^ d =
          x ^ d * ((2 * R * x ^ (h.t - h.u) - 1) + 1) := by ring
      _ = x ^ d * (2 * R * x ^ (h.t - h.u)) := by
        rw [Nat.sub_add_cancel hCoeffOne]
      _ = 2 * R * x ^ (h.t - h.q) := by
        calc
          x ^ d * (2 * R * x ^ (h.t - h.u)) =
              2 * R * (x ^ d * x ^ (h.t - h.u)) := by ring
          _ = 2 * R * x ^ (d + (h.t - h.u)) := by rw [← pow_add]
          _ = 2 * R * x ^ (h.t - h.q) := by rw [hdecomp]
  have hScaled := congrArg (fun z : ℕ => x ^ h.q * z) hFsum
  have hqd : h.q + d = h.u := by
    dsimp [d]
    exact Nat.add_sub_of_le (Nat.le_of_lt h.q_lt_u)
  have hqt : h.q + (h.t - h.q) = h.t := by
    have hqLeT : h.q ≤ h.t :=
      le_trans (Nat.le_of_lt h.q_lt_u) h.u_le_t
    exact Nat.add_sub_of_le hqLeT
  have hPowU : x ^ h.u = x ^ h.q * x ^ d := by
    calc
      x ^ h.u = x ^ (h.q + d) := by rw [hqd]
      _ = x ^ h.q * x ^ d := by rw [pow_add]
  have hPowT : x ^ h.t = x ^ h.q * x ^ (h.t - h.q) := by
    calc
      x ^ h.t = x ^ (h.q + (h.t - h.q)) := by rw [hqt]
      _ = x ^ h.q * x ^ (h.t - h.q) := by rw [pow_add]
  have hFactorAdd :
      x ^ h.q * h.cutQuotient + x ^ h.q + x ^ h.u =
        2 * R * x ^ h.t := by
    calc
      x ^ h.q * h.cutQuotient + x ^ h.q + x ^ h.u =
          x ^ h.q * (h.cutQuotient + 1 + x ^ d) := by
            rw [hPowU]
            ring
      _ = x ^ h.q * (2 * R * x ^ (h.t - h.q)) := by rw [hFsum]
      _ = 2 * R * x ^ h.t := by
        rw [hPowT]
        ring
  have hCancel :
      2 * ((x - 1) * 3 ^ k + (R - 1)) + (x ^ h.q + x ^ h.u) =
        x ^ h.q * h.cutQuotient + (x ^ h.q + x ^ h.u) := by
    calc
      2 * ((x - 1) * 3 ^ k + (R - 1)) + (x ^ h.q + x ^ h.u) =
          2 * R * x ^ h.t := by simpa [add_assoc] using hCommon
      _ = x ^ h.q * h.cutQuotient + (x ^ h.q + x ^ h.u) := by
        simpa [add_assoc] using hFactorAdd.symm
  have hCore :
      2 * ((x - 1) * 3 ^ k + (R - 1)) = x ^ h.q * h.cutQuotient :=
    Nat.add_right_cancel hCancel
  dsimp [x, R] at hCore ⊢
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hCore

/-- wrapped first cut は `nq-1`。 -/
theorem TargetTwoHoleWrappedGeometricData.firstCut_eq
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b)
    (hn : 0 < n)
    (hr : 0 < r) :
    padicValNat 2 ((2 ^ n - 1) * 3 ^ k + (2 ^ r - 1)) =
      n * h.q - 1 := by
  have hFact := h.firstCut_factorization hr
  have hOdd := h.cutQuotient_odd hn hr
  let A : ℕ := (2 ^ n - 1) * 3 ^ k + (2 ^ r - 1)
  have hAPos : 0 < A := by
    dsimp [A]
    have hx : 0 < 2 ^ n - 1 := by
      have : 1 < 2 ^ n := one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) (Nat.ne_of_gt hn)
      omega
    positivity
  have hFact' :
      2 * A = 2 ^ (n * h.q) * h.cutQuotient := by
    dsimp [A]
    simpa [pow_mul] using hFact
  have hVal := congrArg (padicValNat 2) hFact'
  have hRight :=
    targetTwo_padicValNat_twoPow_mul_odd
      (n * h.q) h.cutQuotient hOdd
  rw [targetTwo_padicValNat_two_mul A (Nat.ne_of_gt hAPos), hRight] at hVal
  have hqPos : 0 < h.q := h.q_pos
  have hnqPos : 0 < n * h.q := Nat.mul_pos hn hqPos
  calc
    padicValNat 2 A = (1 + padicValNat 2 A) - 1 := by omega
    _ = n * h.q - 1 := by rw [hVal]

/-- wrapped second cut は `n(u-q)`。 -/
theorem TargetTwoHoleWrappedGeometricData.secondCut_eq
    {k n r L a b : ℕ}
    (h : TargetTwoHoleWrappedGeometricData k n r L a b)
    (hr : 0 < r) :
    padicValNat 2 (h.cutQuotient + 1) =
      n * (h.u - h.q) := by
  have hSecond := h.cutQuotient_add_one_factorization hr
  let C : ℕ := 2 ^ (r + 1) * (2 ^ n) ^ (h.t - h.u) - 1
  have hCOdd : Odd C := by
    dsimp [C]
    exact targetTwo_odd_twoPow_mul_sub_one
      (e := r + 1) (m := (2 ^ n) ^ (h.t - h.u)) (by omega) (by positivity)
  have hSecond' :
      h.cutQuotient + 1 =
        2 ^ (n * (h.u - h.q)) * C := by
    dsimp [C]
    simpa [pow_mul] using hSecond
  rw [hSecond']
  exact targetTwo_padicValNat_twoPow_mul_odd _ _ hCOdd

/-! ## split-forward phase -/

/-- split-forward の first-cut 後 quotient。 -/
def TargetTwoHoleSplitForwardGeometricData.cutQuotient
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b) : ℕ :=
  2 ^ (r + 1) * (2 ^ n) ^ (h.t - h.q) -
    (1 + 2 ^ r * (2 ^ n) ^ (h.u - h.q))

/-- split-forward quotient に 1 を足すと第二 cut が factor 化する。 -/
theorem TargetTwoHoleSplitForwardGeometricData.cutQuotient_add_one_factorization
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b) :
    h.cutQuotient + 1 =
      2 ^ r * (2 ^ n) ^ (h.u - h.q) *
        (2 * (2 ^ n) ^ (h.t - h.u) - 1) := by
  let x : ℕ := 2 ^ n
  let R : ℕ := 2 ^ r
  let d : ℕ := h.u - h.q
  let e : ℕ := h.t - h.u
  have hqLeU : h.q ≤ h.u := h.q_le_u
  have huLeT : h.u ≤ h.t := h.u_le_t
  have hde : d + e = h.t - h.q := by
    dsimp [d, e]
    omega
  have hxPos : 0 < x := by
    dsimp [x]
    exact Nat.pow_pos (by norm_num)
  have hxPowEPos : 0 < x ^ e := Nat.pow_pos hxPos
  have hCoeffOne : 1 ≤ 2 * x ^ e := by
    have hProdPos : 0 < 2 * x ^ e :=
      Nat.mul_pos (by norm_num) hxPowEPos
    omega
  have hProdAdd :
      R * x ^ d * (2 * x ^ e - 1) + R * x ^ d =
        2 * R * x ^ (h.t - h.q) := by
    calc
      R * x ^ d * (2 * x ^ e - 1) + R * x ^ d =
          R * x ^ d * ((2 * x ^ e - 1) + 1) := by ring
      _ = R * x ^ d * (2 * x ^ e) := by
        rw [Nat.sub_add_cancel hCoeffOne]
      _ = 2 * R * x ^ (h.t - h.q) := by
        calc
          R * x ^ d * (2 * x ^ e)
              = 2 * R * (x ^ d * x ^ e) := by ring
          _ = 2 * R * x ^ (d + e) := by rw [pow_add]
          _ = 2 * R * x ^ (h.t - h.q) := by rw [hde]
  have hSubLe : 1 + R * x ^ d ≤ 2 * R * x ^ (h.t - h.q) := by
    have hTwoLe : 2 ≤ 2 * x ^ e :=
      Nat.le_mul_of_pos_right 2 hxPowEPos
    have hTailPos : 0 < 2 * x ^ e - 1 := by omega
    have hRPos : 0 < R := by
      dsimp [R]
      exact Nat.pow_pos (by norm_num)
    have hxPowDPos : 0 < x ^ d := Nat.pow_pos hxPos
    have hFrontPos : 0 < R * x ^ d :=
      Nat.mul_pos hRPos hxPowDPos
    have hExtraPos :
        0 < R * x ^ d * (2 * x ^ e - 1) :=
      Nat.mul_pos hFrontPos hTailPos
    omega
  have hCut :
      h.cutQuotient =
        2 * R * x ^ (h.t - h.q) - (1 + R * x ^ d) := by
    unfold TargetTwoHoleSplitForwardGeometricData.cutQuotient
    dsimp [x, R, d]
    rw [pow_succ]
    rw [Nat.mul_comm (2 ^ r) 2]
  have hRPos : 0 < R := by
    dsimp [R]
    exact Nat.pow_pos (by norm_num)
  have hxPowDPos : 0 < x ^ d := Nat.pow_pos hxPos
  have hFrontPos : 0 < R * x ^ d := Nat.mul_pos hRPos hxPowDPos
  have hTailPos : 0 < 2 * x ^ e - 1 := by
    have hTwoLe : 2 ≤ 2 * x ^ e :=
      Nat.le_mul_of_pos_right 2 hxPowEPos
    omega
  have hRhsPos :
      0 < R * x ^ d * (2 * x ^ e - 1) :=
    Nat.mul_pos hFrontPos hTailPos
  rw [hCut]
  calc
    2 * R * x ^ (h.t - h.q) - (1 + R * x ^ d) + 1 =
        (R * x ^ d * (2 * x ^ e - 1) + R * x ^ d) -
          (1 + R * x ^ d) + 1 := by rw [hProdAdd]
    _ = R * x ^ d * (2 * x ^ e - 1) := by omega

/-- split-forward quotient は奇数。 -/
theorem TargetTwoHoleSplitForwardGeometricData.cutQuotient_odd
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b)
    (hr : 0 < r) :
    Odd h.cutQuotient := by
  have hSecond := h.cutQuotient_add_one_factorization
  let C : ℕ := 2 * (2 ^ n) ^ (h.t - h.u) - 1
  have hCPos : 0 < C := by
    dsimp [C]
    have hPowPos : 0 < (2 ^ n) ^ (h.t - h.u) := by
      exact Nat.pow_pos (Nat.pow_pos (by norm_num))
    have hTwoLe : 2 ≤ 2 * (2 ^ n) ^ (h.t - h.u) :=
      Nat.le_mul_of_pos_right 2 hPowPos
    omega
  have hePos : 0 < r + n * (h.u - h.q) := by omega
  have hSecond' :
      h.cutQuotient + 1 =
        2 ^ (r + n * (h.u - h.q)) * C := by
    dsimp [C]
    rw [pow_add, pow_mul]
    simpa [mul_assoc] using hSecond
  exact targetTwo_odd_of_succ_eq_twoPow_mul hePos hCPos hSecond'

/-- split-forward first cut factorization。 -/
theorem TargetTwoHoleSplitForwardGeometricData.firstCut_factorization
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b) :
    (2 ^ n - 1) * 3 ^ k + (2 ^ r - 1) =
      (2 ^ n) ^ h.q * h.cutQuotient := by
  let x : ℕ := 2 ^ n
  let R : ℕ := 2 ^ r
  let d : ℕ := h.u - h.q
  have hxPos : 0 < x := by
    dsimp [x]
    exact Nat.pow_pos (by norm_num)
  have hxOne : 1 ≤ x := by omega
  have hGeomQ := targetTwo_geom_mul (x := x) (t := h.q) hxOne
  have hGeomU := targetTwo_geom_mul (x := x) (t := h.u) hxOne
  have hGeomT := targetTwo_geom_mul (x := x) (t := h.t) hxOne
  have hTwoR : 2 ^ (r + 1) = 2 * R := by
    dsimp [R]
    rw [pow_succ]
    ring
  have hEq := h.equation
  change
      3 ^ k + targetGeomSum x h.q + R * targetGeomSum x h.u =
        2 ^ (r + 1) * targetGeomSum x h.t at hEq
  rw [hTwoR] at hEq
  have hMul := congrArg (fun z : ℕ => z * (x - 1)) hEq
  rw [Nat.add_mul, Nat.add_mul, hGeomQ] at hMul
  rw [mul_assoc R (targetGeomSum x h.u) (x - 1), hGeomU] at hMul
  rw [mul_assoc (2 * R) (targetGeomSum x h.t) (x - 1), hGeomT] at hMul
  have hCommon :
      ((x - 1) * 3 ^ k + (R - 1)) + x ^ h.q + R * x ^ h.u =
        2 * R * x ^ h.t := by
    have hRPos : 0 < R := by
      dsimp [R]
      exact Nat.pow_pos (by norm_num)
    have hROne : 1 ≤ R := by omega
    have hQOne : 1 ≤ x ^ h.q := Nat.one_le_pow h.q x hxOne
    have hUOne : 1 ≤ x ^ h.u := Nat.one_le_pow h.u x hxOne
    have hTOne : 1 ≤ x ^ h.t := Nat.one_le_pow h.t x hxOne
    have hRU : R * (x ^ h.u - 1) + R = R * x ^ h.u := by
      calc
        R * (x ^ h.u - 1) + R = R * ((x ^ h.u - 1) + 1) := by ring
        _ = R * x ^ h.u := by rw [Nat.sub_add_cancel hUOne]
    have hLeft :
        ((x - 1) * 3 ^ k + (R - 1)) +
            x ^ h.q + R * x ^ h.u =
          (3 ^ k * (x - 1) + (x ^ h.q - 1) +
              R * (x ^ h.u - 1)) +
            2 * R := by
      have hRSub :
          R - 1 + 1 = R :=
        Nat.sub_add_cancel hROne
      have hQSub :
          x ^ h.q - 1 + 1 = x ^ h.q :=
        Nat.sub_add_cancel hQOne
      have hRU :
          R * (x ^ h.u - 1) + R =
            R * x ^ h.u := by
        calc
          R * (x ^ h.u - 1) + R
              = R * ((x ^ h.u - 1) + 1) := by
                  ring
          _ = R * x ^ h.u := by
                rw [Nat.sub_add_cancel hUOne]
      calc
        ((x - 1) * 3 ^ k + (R - 1)) +
              x ^ h.q + R * x ^ h.u
            =
          ((x - 1) * 3 ^ k + (R - 1)) +
              ((x ^ h.q - 1) + 1) +
              R * x ^ h.u := by
                rw [hQSub]
      _ =
          (x - 1) * 3 ^ k +
            (x ^ h.q - 1) +
            R * x ^ h.u +
            ((R - 1) + 1) := by
              ring
      _ =
          (x - 1) * 3 ^ k +
            (x ^ h.q - 1) +
            R * x ^ h.u +
            R := by
              rw [hRSub]
        _ =
          (x - 1) * 3 ^ k +
            (x ^ h.q - 1) +
            (R * (x ^ h.u - 1) + R) +
            R := by
              rw [hRU]
        _ =
          (3 ^ k * (x - 1) +
              (x ^ h.q - 1) +
              R * (x ^ h.u - 1)) +
            2 * R := by
              ring
    have hRight :
        2 * R * (x ^ h.t - 1) + 2 * R = 2 * R * x ^ h.t := by
      calc
        2 * R * (x ^ h.t - 1) + 2 * R =
            2 * R * ((x ^ h.t - 1) + 1) := by ring
        _ = 2 * R * x ^ h.t := by rw [Nat.sub_add_cancel hTOne]
    calc
      ((x - 1) * 3 ^ k + (R - 1)) + x ^ h.q + R * x ^ h.u =
          (3 ^ k * (x - 1) + (x ^ h.q - 1) + R * (x ^ h.u - 1)) + 2 * R := hLeft
      _ = 2 * R * (x ^ h.t - 1) + 2 * R := by rw [hMul]
      _ = 2 * R * x ^ h.t := hRight
  have hFsum :
      h.cutQuotient + 1 + R * x ^ d =
        2 * R * x ^ (h.t - h.q) := by
    have hSecond := h.cutQuotient_add_one_factorization
    have hqLeU : h.q ≤ h.u := h.q_le_u
    have huLeT : h.u ≤ h.t := h.u_le_t
    have hde : d + (h.t - h.u) = h.t - h.q := by
      dsimp [d]
      omega
    have hxTailPos : 0 < x ^ (h.t - h.u) :=
      Nat.pow_pos hxPos
    have hCoeffOne : 1 ≤ 2 * x ^ (h.t - h.u) := by
      have hProdPos : 0 < 2 * x ^ (h.t - h.u) :=
        Nat.mul_pos (by norm_num) hxTailPos
      omega
    change h.cutQuotient + 1 + R * x ^ d = 2 * R * x ^ (h.t - h.q)
    rw [hSecond]
    calc
      R * x ^ d * (2 * x ^ (h.t - h.u) - 1) + R * x ^ d =
          R * x ^ d * ((2 * x ^ (h.t - h.u) - 1) + 1) := by ring
      _ = R * x ^ d * (2 * x ^ (h.t - h.u)) := by
        rw [Nat.sub_add_cancel hCoeffOne]
      _ = 2 * R * x ^ (h.t - h.q) := by
        calc
          R * x ^ d * (2 * x ^ (h.t - h.u)) =
              2 * R * (x ^ d * x ^ (h.t - h.u)) := by ring
          _ = 2 * R * x ^ (d + (h.t - h.u)) := by rw [← pow_add]
          _ = 2 * R * x ^ (h.t - h.q) := by rw [hde]
  have hqd : h.q + d = h.u := by
    dsimp [d]
    exact Nat.add_sub_of_le h.q_le_u
  have hqt : h.q + (h.t - h.q) = h.t := by
    have hqLeT : h.q ≤ h.t :=
      le_trans h.q_le_u h.u_le_t
    exact Nat.add_sub_of_le hqLeT
  have hPowU : x ^ h.u = x ^ h.q * x ^ d := by
    calc
      x ^ h.u = x ^ (h.q + d) := by rw [hqd]
      _ = x ^ h.q * x ^ d := by rw [pow_add]
  have hPowT : x ^ h.t = x ^ h.q * x ^ (h.t - h.q) := by
    calc
      x ^ h.t = x ^ (h.q + (h.t - h.q)) := by rw [hqt]
      _ = x ^ h.q * x ^ (h.t - h.q) := by rw [pow_add]
  have hFactorAdd :
      x ^ h.q * h.cutQuotient + x ^ h.q + R * x ^ h.u =
        2 * R * x ^ h.t := by
    calc
      x ^ h.q * h.cutQuotient + x ^ h.q + R * x ^ h.u =
          x ^ h.q * (h.cutQuotient + 1 + R * x ^ d) := by
            rw [hPowU]
            ring
      _ = x ^ h.q * (2 * R * x ^ (h.t - h.q)) := by rw [hFsum]
      _ = 2 * R * x ^ h.t := by
        rw [hPowT]
        ring
  have hCancel :
      ((x - 1) * 3 ^ k + (R - 1)) + (x ^ h.q + R * x ^ h.u) =
        x ^ h.q * h.cutQuotient + (x ^ h.q + R * x ^ h.u) := by
    calc
      ((x - 1) * 3 ^ k + (R - 1)) + (x ^ h.q + R * x ^ h.u) =
          2 * R * x ^ h.t := by simpa [add_assoc] using hCommon
      _ = x ^ h.q * h.cutQuotient + (x ^ h.q + R * x ^ h.u) := by
        simpa [add_assoc] using hFactorAdd.symm
  have hCore :
      (x - 1) * 3 ^ k + (R - 1) = x ^ h.q * h.cutQuotient :=
    Nat.add_right_cancel hCancel
  dsimp [x, R] at hCore ⊢
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hCore

/-- split-forward first cut は `nq`。 -/
theorem TargetTwoHoleSplitForwardGeometricData.firstCut_eq
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b)
    (hr : 0 < r) :
    padicValNat 2 ((2 ^ n - 1) * 3 ^ k + (2 ^ r - 1)) =
      n * h.q := by
  have hFact := h.firstCut_factorization
  have hOdd := h.cutQuotient_odd hr
  have hFact' :
      (2 ^ n - 1) * 3 ^ k + (2 ^ r - 1) =
        2 ^ (n * h.q) * h.cutQuotient := by
    simpa [pow_mul] using hFact
  rw [hFact']
  exact targetTwo_padicValNat_twoPow_mul_odd _ _ hOdd

/-- split-forward second cut は `r+n(u-q)`。 -/
theorem TargetTwoHoleSplitForwardGeometricData.secondCut_eq
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitForwardGeometricData k n r L a b) :
    padicValNat 2 (h.cutQuotient + 1) =
      r + n * (h.u - h.q) := by
  have hSecond := h.cutQuotient_add_one_factorization
  let C : ℕ := 2 * (2 ^ n) ^ (h.t - h.u) - 1
  have hCOdd : Odd C := by
    dsimp [C]
    exact targetTwo_odd_twoPow_mul_sub_one
      (e := 1) (m := (2 ^ n) ^ (h.t - h.u)) (by omega) (by positivity)
  have hSecond' :
      h.cutQuotient + 1 =
        2 ^ (r + n * (h.u - h.q)) * C := by
    dsimp [C]
    rw [pow_add, pow_mul]
    simpa [mul_assoc] using hSecond
  rw [hSecond']
  exact targetTwo_padicValNat_twoPow_mul_odd _ _ hCOdd

/-! ## split-reverse phase -/

/-- reverse phase で `x^(q-u)/2^r` に対応する exponent。 -/
def TargetTwoHoleSplitReverseGeometricData.gapExponent
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b) : ℕ :=
  n * (h.q - h.u) - r

/-- reverse phase の first-cut 後、`2^r` まで正規化した quotient。 -/
def TargetTwoHoleSplitReverseGeometricData.cutQuotient
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b) : ℕ :=
  2 * (2 ^ n) ^ (h.t - h.u) - (1 + 2 ^ h.gapExponent)

/-- reverse gap exponent は `n>=4`, `r<=2` では正。 -/
theorem TargetTwoHoleSplitReverseGeometricData.gapExponent_pos
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b)
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    0 < h.gapExponent := by
  have huLtQ : h.u < h.q := h.u_lt_q
  have hd : 0 < h.q - h.u :=
    Nat.sub_pos_of_lt huLtQ
  have hMul : n ≤ n * (h.q - h.u) :=
    Nat.le_mul_of_pos_right n hd
  have hrLe : r ≤ 2 := by rcases hr with rfl | rfl <;> omega
  dsimp [TargetTwoHoleSplitReverseGeometricData.gapExponent]
  omega

/-- reverse quotient に 1 を足すと第二 cut が factor 化する。 -/
theorem TargetTwoHoleSplitReverseGeometricData.cutQuotient_add_one_factorization
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b)
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    h.cutQuotient + 1 =
      2 ^ h.gapExponent *
        (2 ^ (r + 1) * (2 ^ n) ^ (h.t - h.q) - 1) := by
  let x : ℕ := 2 ^ n
  let E : ℕ := h.gapExponent
  have hEPos : 0 < E := by
    dsimp [E]
    exact h.gapExponent_pos hn4 hr
  have hrPos : 0 < r := by rcases hr with rfl | rfl <;> omega
  have hExpEq : r + E = n * (h.q - h.u) := by
    dsimp [E, TargetTwoHoleSplitReverseGeometricData.gapExponent]
    have hgt : r < n * (h.q - h.u) := by
      have huLtQ : h.u < h.q := h.u_lt_q
      have hGapPos : 0 < h.q - h.u :=
        Nat.sub_pos_of_lt huLtQ
      have hMul : n ≤ n * (h.q - h.u) :=
        Nat.le_mul_of_pos_right n hGapPos
      have hrLe : r ≤ 2 := by rcases hr with rfl | rfl <;> omega
      omega
    omega
  have hPowGap :
      2 ^ r * 2 ^ E = x ^ (h.q - h.u) := by
    rw [← pow_add, hExpEq]
    dsimp [x]
    rw [pow_mul]
  have huLtQ : h.u < h.q := h.u_lt_q
  have hqLeT : h.q ≤ h.t := h.q_le_t
  have hde :
      (h.q - h.u) + (h.t - h.q) = h.t - h.u := by
    omega
  have hxPos : 0 < x := by
    dsimp [x]
    exact Nat.pow_pos (by norm_num)
  have hCoeffPos : 0 < 2 ^ (r + 1) :=
    Nat.pow_pos (by norm_num)
  have hxTailPos : 0 < x ^ (h.t - h.q) :=
    Nat.pow_pos hxPos
  have hCoeffOne : 1 ≤ 2 ^ (r + 1) * x ^ (h.t - h.q) := by
    have hProdPos :
        0 < 2 ^ (r + 1) * x ^ (h.t - h.q) :=
      Nat.mul_pos hCoeffPos hxTailPos
    omega
  have hProdAdd :
      2 ^ E * (2 ^ (r + 1) * x ^ (h.t - h.q) - 1) + 2 ^ E =
        2 * x ^ (h.t - h.u) := by
    calc
      2 ^ E * (2 ^ (r + 1) * x ^ (h.t - h.q) - 1) + 2 ^ E =
          2 ^ E * ((2 ^ (r + 1) * x ^ (h.t - h.q) - 1) + 1) := by ring
      _ = 2 ^ E * (2 ^ (r + 1) * x ^ (h.t - h.q)) := by
        rw [Nat.sub_add_cancel hCoeffOne]
      _ = 2 * x ^ (h.t - h.u) := by
        rw [pow_succ]
        calc
          2 ^ E * (2 ^ r * 2 * x ^ (h.t - h.q)) =
              2 * (2 ^ r * 2 ^ E) * x ^ (h.t - h.q) := by ring
          _ = 2 * x ^ (h.q - h.u) * x ^ (h.t - h.q) := by rw [hPowGap]
          _ = 2 * (x ^ (h.q - h.u) * x ^ (h.t - h.q)) := by ring
          _ = 2 * x ^ ((h.q - h.u) + (h.t - h.q)) := by rw [pow_add]
          _ = 2 * x ^ (h.t - h.u) := by rw [hde]
  have hSubLe : 1 + 2 ^ E ≤ 2 * x ^ (h.t - h.u) := by
    have hCoeffTwo : 2 ≤ 2 ^ (r + 1) := by
      have hrOne : 1 ≤ r := by
        rcases hr with rfl | rfl <;> omega
      have hp :=
        Nat.pow_le_pow_right
          (by norm_num : 0 < (2 : ℕ))
          (by omega : 1 ≤ r + 1)
      norm_num at hp ⊢
      exact hp
    have hInsideTwo :
        2 ≤ 2 ^ (r + 1) * x ^ (h.t - h.q) :=
      le_trans hCoeffTwo
        (Nat.le_mul_of_pos_right (2 ^ (r + 1)) hxTailPos)
    have hInside :
        0 < 2 ^ (r + 1) * x ^ (h.t - h.q) - 1 := by
      omega
    have hPowEPos : 0 < 2 ^ E := Nat.pow_pos (by norm_num)
    have hTailPos :
        0 < 2 ^ E *
          (2 ^ (r + 1) * x ^ (h.t - h.q) - 1) :=
      Nat.mul_pos hPowEPos hInside
    omega
  change
      2 * x ^ (h.t - h.u) - (1 + 2 ^ E) + 1 =
        2 ^ E * (2 ^ (r + 1) * x ^ (h.t - h.q) - 1)
  omega

/-- reverse quotient は奇数。 -/
theorem TargetTwoHoleSplitReverseGeometricData.cutQuotient_odd
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b)
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    Odd h.cutQuotient := by
  have hSecond := h.cutQuotient_add_one_factorization hn4 hr
  let C : ℕ := 2 ^ (r + 1) * (2 ^ n) ^ (h.t - h.q) - 1
  have hCPos : 0 < C := by
    dsimp [C]
    have hCoeffTwo : 2 ≤ 2 ^ (r + 1) := by
      have hp :=
        Nat.pow_le_pow_right
          (by norm_num : 0 < (2 : ℕ))
          (by rcases hr with rfl | rfl <;> omega : 1 ≤ r + 1)
      norm_num at hp ⊢
      exact hp
    have hPowPos : 0 < (2 ^ n) ^ (h.t - h.q) :=
      Nat.pow_pos (Nat.pow_pos (by norm_num))
    have hTwoLe :
        2 ≤ 2 ^ (r + 1) * (2 ^ n) ^ (h.t - h.q) :=
      le_trans hCoeffTwo
        (Nat.le_mul_of_pos_right (2 ^ (r + 1)) hPowPos)
    omega
  have hEPos := h.gapExponent_pos hn4 hr
  exact targetTwo_odd_of_succ_eq_twoPow_mul hEPos hCPos
    (by simpa [C] using hSecond)

/-- reverse phase first cut の factorization。 -/
theorem TargetTwoHoleSplitReverseGeometricData.firstCut_factorization
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b)
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    (2 ^ n - 1) * 3 ^ k + (2 ^ r - 1) =
      (2 ^ n) ^ h.u * 2 ^ r * h.cutQuotient := by
  let x : ℕ := 2 ^ n
  let R : ℕ := 2 ^ r
  let E : ℕ := h.gapExponent
  have hrPos : 0 < r := by rcases hr with rfl | rfl <;> omega
  have hxPos : 0 < x := by
    dsimp [x]
    exact Nat.pow_pos (by norm_num)
  have hxOne : 1 ≤ x := by omega
  have hGeomQ := targetTwo_geom_mul (x := x) (t := h.q) hxOne
  have hGeomU := targetTwo_geom_mul (x := x) (t := h.u) hxOne
  have hGeomT := targetTwo_geom_mul (x := x) (t := h.t) hxOne
  have hTwoR : 2 ^ (r + 1) = 2 * R := by
    dsimp [R]
    rw [pow_succ]
    ring
  have hEq := h.equation
  change
      3 ^ k + targetGeomSum x h.q + R * targetGeomSum x h.u =
        2 ^ (r + 1) * targetGeomSum x h.t at hEq
  rw [hTwoR] at hEq
  have hMul := congrArg (fun z : ℕ => z * (x - 1)) hEq
  rw [Nat.add_mul, Nat.add_mul, hGeomQ] at hMul
  rw [mul_assoc R (targetGeomSum x h.u) (x - 1), hGeomU] at hMul
  rw [mul_assoc (2 * R) (targetGeomSum x h.t) (x - 1), hGeomT] at hMul
  have hCommon :
      ((x - 1) * 3 ^ k + (R - 1)) + x ^ h.q + R * x ^ h.u =
        2 * R * x ^ h.t := by
    have hRPos : 0 < R := by
      dsimp [R]
      exact Nat.pow_pos (by norm_num)
    have hROne : 1 ≤ R := by omega
    have hQOne : 1 ≤ x ^ h.q := Nat.one_le_pow h.q x hxOne
    have hUOne : 1 ≤ x ^ h.u := Nat.one_le_pow h.u x hxOne
    have hTOne : 1 ≤ x ^ h.t := Nat.one_le_pow h.t x hxOne
    have hRU : R * (x ^ h.u - 1) + R = R * x ^ h.u := by
      calc
        R * (x ^ h.u - 1) + R = R * ((x ^ h.u - 1) + 1) := by ring
        _ = R * x ^ h.u := by rw [Nat.sub_add_cancel hUOne]
    have hLeft :
        ((x - 1) * 3 ^ k + (R - 1)) +
            x ^ h.q + R * x ^ h.u =
          (3 ^ k * (x - 1) + (x ^ h.q - 1) +
              R * (x ^ h.u - 1)) +
            2 * R := by
      have hRSub :
          R - 1 + 1 = R :=
        Nat.sub_add_cancel hROne
      have hQSub :
          x ^ h.q - 1 + 1 = x ^ h.q :=
        Nat.sub_add_cancel hQOne
      calc
        ((x - 1) * 3 ^ k + (R - 1)) +
              x ^ h.q + R * x ^ h.u
            =
          ((x - 1) * 3 ^ k + (R - 1)) +
              ((x ^ h.q - 1) + 1) +
              R * x ^ h.u := by
                rw [hQSub]
        _ =
          (x - 1) * 3 ^ k +
            (x ^ h.q - 1) +
            R * x ^ h.u +
            ((R - 1) + 1) := by
              ring
        _ =
          (x - 1) * 3 ^ k +
            (x ^ h.q - 1) +
            R * x ^ h.u +
            R := by
              rw [hRSub]
        _ =
          (x - 1) * 3 ^ k +
            (x ^ h.q - 1) +
            (R * (x ^ h.u - 1) + R) +
            R := by
              rw [hRU]
        _ =
          (3 ^ k * (x - 1) +
              (x ^ h.q - 1) +
              R * (x ^ h.u - 1)) +
            2 * R := by
              ring
    have hRight :
        2 * R * (x ^ h.t - 1) + 2 * R = 2 * R * x ^ h.t := by
      calc
        2 * R * (x ^ h.t - 1) + 2 * R =
            2 * R * ((x ^ h.t - 1) + 1) := by ring
        _ = 2 * R * x ^ h.t := by rw [Nat.sub_add_cancel hTOne]
    calc
      ((x - 1) * 3 ^ k + (R - 1)) + x ^ h.q + R * x ^ h.u =
          (3 ^ k * (x - 1) + (x ^ h.q - 1) + R * (x ^ h.u - 1)) + 2 * R := hLeft
      _ = 2 * R * (x ^ h.t - 1) + 2 * R := by rw [hMul]
      _ = 2 * R * x ^ h.t := hRight
  have hExpEq : r + E = n * (h.q - h.u) := by
    dsimp [E, TargetTwoHoleSplitReverseGeometricData.gapExponent]
    have hGapPos : 0 < h.q - h.u :=
      Nat.sub_pos_of_lt h.u_lt_q
    have hMulLe : n ≤ n * (h.q - h.u) :=
      Nat.le_mul_of_pos_right n hGapPos
    have hrLe : r ≤ 2 := by rcases hr with rfl | rfl <;> omega
    omega
  have hPowGap : R * 2 ^ E = x ^ (h.q - h.u) := by
    dsimp [R, x]
    rw [← pow_add, hExpEq, pow_mul]
  have hHsum :
      h.cutQuotient + 1 + 2 ^ E =
        2 * x ^ (h.t - h.u) := by
    have hSecond := h.cutQuotient_add_one_factorization hn4 hr
    have hCoeffPos : 0 < 2 ^ (r + 1) :=
      Nat.pow_pos (by norm_num)
    have hxTailPos : 0 < x ^ (h.t - h.q) :=
      Nat.pow_pos hxPos
    have hCoeffOne : 1 ≤ 2 ^ (r + 1) * x ^ (h.t - h.q) := by
      have hProdPos :
          0 < 2 ^ (r + 1) * x ^ (h.t - h.q) :=
        Nat.mul_pos hCoeffPos hxTailPos
      omega
    have huLtQ : h.u < h.q := h.u_lt_q
    have hqLeT : h.q ≤ h.t := h.q_le_t
    have hde : (h.q - h.u) + (h.t - h.q) = h.t - h.u := by
      omega
    change h.cutQuotient + 1 + 2 ^ E = 2 * x ^ (h.t - h.u)
    rw [hSecond]
    have hProdAdd :
        2 ^ E * (2 ^ (r + 1) * x ^ (h.t - h.q) - 1) + 2 ^ E =
          2 * x ^ (h.t - h.u) := by
      calc
        2 ^ E * (2 ^ (r + 1) * x ^ (h.t - h.q) - 1) + 2 ^ E =
            2 ^ E * ((2 ^ (r + 1) * x ^ (h.t - h.q) - 1) + 1) := by ring
        _ = 2 ^ E * (2 ^ (r + 1) * x ^ (h.t - h.q)) := by
          rw [Nat.sub_add_cancel hCoeffOne]
        _ = 2 * x ^ (h.t - h.u) := by
          calc
            2 ^ E * (2 ^ (r + 1) * x ^ (h.t - h.q)) =
                2 ^ E * ((2 * R) * x ^ (h.t - h.q)) := by rw [hTwoR]
            _ = 2 * (R * 2 ^ E) * x ^ (h.t - h.q) := by ring
            _ = 2 * x ^ (h.q - h.u) * x ^ (h.t - h.q) := by rw [hPowGap]
            _ = 2 * (x ^ (h.q - h.u) * x ^ (h.t - h.q)) := by ring
            _ = 2 * x ^ ((h.q - h.u) + (h.t - h.q)) := by rw [← pow_add]
            _ = 2 * x ^ (h.t - h.u) := by rw [hde]
    exact hProdAdd
  have huq : h.u + (h.q - h.u) = h.q := by
    exact Nat.add_sub_of_le (Nat.le_of_lt h.u_lt_q)
  have hut : h.u + (h.t - h.u) = h.t := by
    have huLeT : h.u ≤ h.t :=
      le_trans (Nat.le_of_lt h.u_lt_q) h.q_le_t
    exact Nat.add_sub_of_le huLeT
  have hPowQ : x ^ h.q = x ^ h.u * (R * 2 ^ E) := by
    calc
      x ^ h.q = x ^ (h.u + (h.q - h.u)) := by rw [huq]
      _ = x ^ h.u * x ^ (h.q - h.u) := by rw [pow_add]
      _ = x ^ h.u * (R * 2 ^ E) := by rw [← hPowGap]
  have hPowT : x ^ h.t = x ^ h.u * x ^ (h.t - h.u) := by
    calc
      x ^ h.t = x ^ (h.u + (h.t - h.u)) := by rw [hut]
      _ = x ^ h.u * x ^ (h.t - h.u) := by rw [pow_add]
  have hFactorAdd :
      x ^ h.u * R * h.cutQuotient + x ^ h.q + R * x ^ h.u =
        2 * R * x ^ h.t := by
    calc
      x ^ h.u * R * h.cutQuotient + x ^ h.q + R * x ^ h.u =
          x ^ h.u * R * (h.cutQuotient + 1 + 2 ^ E) := by
            rw [hPowQ]
            ring
      _ = x ^ h.u * R * (2 * x ^ (h.t - h.u)) := by rw [hHsum]
      _ = 2 * R * x ^ h.t := by
        rw [hPowT]
        ring
  have hCancel :
      ((x - 1) * 3 ^ k + (R - 1)) + (x ^ h.q + R * x ^ h.u) =
        x ^ h.u * R * h.cutQuotient + (x ^ h.q + R * x ^ h.u) := by
    calc
      ((x - 1) * 3 ^ k + (R - 1)) + (x ^ h.q + R * x ^ h.u) =
          2 * R * x ^ h.t := by simpa [add_assoc] using hCommon
      _ = x ^ h.u * R * h.cutQuotient + (x ^ h.q + R * x ^ h.u) := by
        simpa [add_assoc] using hFactorAdd.symm
  have hCore :
      (x - 1) * 3 ^ k + (R - 1) = x ^ h.u * R * h.cutQuotient :=
    Nat.add_right_cancel hCancel
  dsimp [x, R] at hCore ⊢
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hCore

/-- reverse phase first cut は `nu+r`。 -/
theorem TargetTwoHoleSplitReverseGeometricData.firstCut_eq
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b)
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    padicValNat 2 ((2 ^ n - 1) * 3 ^ k + (2 ^ r - 1)) =
      n * h.u + r := by
  have hFact := h.firstCut_factorization hn4 hr
  have hOdd := h.cutQuotient_odd hn4 hr
  have hFact' :
      (2 ^ n - 1) * 3 ^ k + (2 ^ r - 1) =
        2 ^ (n * h.u + r) * h.cutQuotient := by
    calc
      (2 ^ n - 1) * 3 ^ k + (2 ^ r - 1) =
          (2 ^ n) ^ h.u * 2 ^ r * h.cutQuotient := hFact
      _ = 2 ^ (n * h.u + r) * h.cutQuotient := by
        rw [← pow_mul, ← pow_add]
  rw [hFact']
  exact targetTwo_padicValNat_twoPow_mul_odd _ _ hOdd

/-- reverse phase second cut は normalized scale で `n(q-u)-r`。 -/
theorem TargetTwoHoleSplitReverseGeometricData.secondCut_eq
    {k n r L a b : ℕ}
    (h : TargetTwoHoleSplitReverseGeometricData k n r L a b)
    (hn4 : 4 ≤ n)
    (hr : r = 1 ∨ r = 2) :
    padicValNat 2 (h.cutQuotient + 1) = h.gapExponent := by
  have hSecond := h.cutQuotient_add_one_factorization hn4 hr
  let C : ℕ := 2 ^ (r + 1) * (2 ^ n) ^ (h.t - h.q) - 1
  have hCOdd : Odd C := by
    dsimp [C]
    exact targetTwo_odd_twoPow_mul_sub_one
      (e := r + 1) (m := (2 ^ n) ^ (h.t - h.q))
      (by rcases hr with rfl | rfl <;> omega) (by positivity)
  have hSecond' : h.cutQuotient + 1 = 2 ^ h.gapExponent * C := by
    simpa [C] using hSecond
  rw [hSecond']
  exact targetTwo_padicValNat_twoPow_mul_odd _ _ hCOdd

end Mersenne
end Collatz3
