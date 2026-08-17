import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.RhinLinearForm14
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalPowerFareyGeometry
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.RhinStrongSlackStartNine

set_option linter.style.nativeDecide false
set_option exponentiation.threshold 4096
/-!
# RhinLinearForm14 -> actual start-nine strong slack

外部 input は `RhinLinearForm14` のみ。
そこから得た

  q_{j+1} <= 2 q_j^14

を二回使い、`n=q_{j-1}` に対して strong-window 左辺を

  2^273 n^2954

で粗く抑える。`n>=q_11=50508` では elementary logarithm estimate により

  2^273 n^2954 < 2^(n-1)

が成立する。j=9,10,11 は native finite check で閉じる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace RhinLinearForm14

private theorem log_two_gt_half_actual :
    (1 / 2 : ℝ) < Real.log 2 := by
  have h :=
    Real.log_lt_sub_one_of_pos
      (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hlog : Real.log (1 / 2 : ℝ) = - Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    exact Real.log_inv 2
  rw [hlog] at h
  norm_num at h ⊢
  linarith

private theorem log_nat_upper_from_32768
    {n : ℕ}
    (hn : 32768 < n) :
    Real.log (n : ℝ) <
      (n : ℝ) / 32768 - 1 + 15 * Real.log 2 := by
  have hnR : (32768 : ℝ) < n := by exact_mod_cast hn
  have hxPos : 0 < (n : ℝ) / 32768 := by positivity
  have hxNe : (n : ℝ) / 32768 ≠ 1 := by
    intro h
    have : (n : ℝ) = 32768 := (div_eq_one_iff_eq (by norm_num : (32768 : ℝ) ≠ 0)).mp h
    nlinarith
  have hx := Real.log_lt_sub_one_of_pos hxPos hxNe
  have hlogDiv :
      Real.log ((n : ℝ) / 32768) =
        Real.log (n : ℝ) - Real.log 32768 := by
    rw [Real.log_div (by positivity) (by norm_num)]
  have h32768 : Real.log (32768 : ℝ) = 15 * Real.log 2 := by
    have heq : (32768 : ℝ) = (2 : ℝ) ^ 15 := by norm_num
    rw [heq, Real.log_pow]
    norm_num
  rw [hlogDiv, h32768] at hx
  linarith

private theorem polynomial_lt_dyadic_tail
    {n : ℕ}
    (hn : 50508 ≤ n) :
    2 ^ 273 * n ^ 2954 < 2 ^ (n - 1) := by
  have hnPos : 0 < n := by omega
  have hnLarge : 32768 < n := by omega
  have hlogn := log_nat_upper_from_32768 hnLarge
  have hlog2 := log_two_gt_half_actual
  have hnR : (50508 : ℝ) ≤ n := by exact_mod_cast hn
  have hlin :
      273 * Real.log 2 +
          2954 * Real.log (n : ℝ) <
        ((n : ℝ) - 1) * Real.log 2 := by
    nlinarith
  have hleftPos :
      0 < (2 : ℝ) ^ 273 * (n : ℝ) ^ 2954 := by positivity
  have hrightPos :
      0 < (2 : ℝ) ^ (n - 1) := by positivity
  have hlogLeft :
      Real.log ((2 : ℝ) ^ 273 * (n : ℝ) ^ 2954) =
        273 * Real.log 2 + 2954 * Real.log (n : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow, Real.log_pow]
    norm_num
  have hlogRight :
      Real.log ((2 : ℝ) ^ (n - 1)) =
        ((n : ℝ) - 1) * Real.log 2 := by
    rw [Real.log_pow]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hcast]
  have hreal :
      (2 : ℝ) ^ 273 * (n : ℝ) ^ 2954 <
        (2 : ℝ) ^ (n - 1) := by
    apply (Real.log_lt_log_iff hleftPos hrightPos).1
    rw [hlogLeft, hlogRight]
    exact hlin
  exact_mod_cast hreal

private theorem natPow_le_natPow_of_le
    {a b : ℕ}
    (hab : a ≤ b) :
    ∀ n : ℕ, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul (natPow_le_natPow_of_le hab n) hab

private theorem pow_mono_exponent
    {a r s : ℕ}
    (ha : 0 < a)
    (hrs : r ≤ s) :
    a ^ r ≤ a ^ s :=
  Nat.pow_le_pow_right ha hrs

/--
tail range `j ≥ 12` では、Rhin の denominator growth から

  q_j ≤ 2 * q_(j-1)^14

を得る。

後続のすべての polynomial bound の最初の入力。
-/
private theorem strong_current_q_bound_tail
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    criticalPowerQ j ≤
      2 * criticalPowerQ (j - 1) ^ 14 := by
  have hjPred : 9 ≤ j - 1 := by
    omega
  have h :=
    R.actual_q_next_le
      (j := j - 1)
      hjPred
  simpa [show (j - 1) + 1 = j by omega] using h


/--
`n = q_(j-1)` とすると、Rhin growth を二回使って

  q_(j+1) ≤ 2^15 * n^196

を得る。

指数 `196 = 14 * 14` は
`q_j ≤ 2 n^14` をさらに14乗することで現れる。
-/
private theorem strong_next_q_bound_tail
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    criticalPowerQ (j + 1) ≤
      2 ^ 15 * criticalPowerQ (j - 1) ^ 196 := by
  let n := criticalPowerQ (j - 1)
  let q := criticalPowerQ j
  let qn := criticalPowerQ (j + 1)
  have hjStart : 9 ≤ j := by
    omega
  have hq :
      q ≤ 2 * n ^ 14 := by
    simpa [q, n] using
      strong_current_q_bound_tail R hj
  have hqn :
      qn ≤ 2 * q ^ 14 := by
    have h :=
      R.actual_q_next_le
        (j := j)
        hjStart
    simpa [qn, q] using h
  have hqPow :
      q ^ 14 ≤
        (2 * n ^ 14) ^ 14 :=
    natPow_le_natPow_of_le hq 14
  have hqPowBound :
      q ^ 14 ≤
        2 ^ 14 * n ^ 196 := by
    calc
      q ^ 14
          ≤ (2 * n ^ 14) ^ 14 := hqPow
      _ = 2 ^ 14 * n ^ 196 := by
        rw [mul_pow, ← pow_mul]
  calc
    qn
        ≤ 2 * q ^ 14 := hqn
    _ ≤ 2 * (2 ^ 14 * n ^ 196) :=
      Nat.mul_le_mul_left 2 hqPowBound
    _ = 2 ^ 15 * n ^ 196 := by
      ring

/--
`n = q_(j-1)` とすると、strong denominator window は

  U + 2 ≤ 2^17 * n^196

で抑えられる。

ここでは current denominator と next denominator の
二つの growth bound だけを使う。
-/
private theorem strong_window_upper_bound_tail
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    strongDenominatorWindowUpper criticalPowerQ j + 2 ≤
      2 ^ 17 * criticalPowerQ (j - 1) ^ 196 := by
  let n := criticalPowerQ (j - 1)
  let q := criticalPowerQ j
  let qn := criticalPowerQ (j + 1)
  let U := strongDenominatorWindowUpper criticalPowerQ j
  have hnPos : 0 < n := by
    dsimp [n]
    exact criticalPowerQ_pos _
  have hq :
      q ≤ 2 * n ^ 14 := by
    simpa [q, n] using
      strong_current_q_bound_tail R hj
  have hqnBound :
      qn ≤ 2 ^ 15 * n ^ 196 := by
    simpa [qn, n] using
      strong_next_q_bound_tail R hj
  have hnPow14_196 :
      n ^ 14 ≤ n ^ 196 :=
    pow_mono_exponent
      hnPos
      (by omega)
  have hqBound196 :
      q ≤ 2 * n ^ 196 :=
    le_trans
      hq
      (Nat.mul_le_mul_left 2 hnPow14_196)
  have hraw :
      U + 2 ≤ q + qn + 2 := by
    dsimp [
      U,
      strongDenominatorWindowUpper,
      q,
      qn
    ]
    omega
  have hn196Pos :
      0 < n ^ 196 :=
    Nat.pow_pos hnPos
  have hn196 :
      1 ≤ n ^ 196 := by
    omega
  calc
    U + 2
        ≤ q + qn + 2 := hraw
    _ ≤
        2 * n ^ 196 +
          2 ^ 15 * n ^ 196 + 2 :=
      Nat.add_le_add
        (Nat.add_le_add
          hqBound196
          hqnBound)
        le_rfl
    _ ≤ 2 ^ 17 * n ^ 196 := by
      norm_num
      nlinarith

/--
strong window の bound を15乗して、

  (U + 2)^15 ≤ 2^255 * n^2940

を得る。

`255 = 17 * 15`,
`2940 = 196 * 15`。
-/
private theorem strong_window_pow_bound_tail
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    (strongDenominatorWindowUpper criticalPowerQ j + 2) ^ 15 ≤
      2 ^ 255 * criticalPowerQ (j - 1) ^ 2940 := by
  let n := criticalPowerQ (j - 1)
  let U := strongDenominatorWindowUpper criticalPowerQ j
  have hU :
      U + 2 ≤ 2 ^ 17 * n ^ 196 := by
    simpa [U, n] using
      strong_window_upper_bound_tail R hj
  have hUPow :
      (U + 2) ^ 15 ≤
        (2 ^ 17 * n ^ 196) ^ 15 :=
    natPow_le_natPow_of_le hU 15
  calc
    (U + 2) ^ 15
        ≤ (2 ^ 17 * n ^ 196) ^ 15 := hUPow
    _ = 2 ^ 255 * n ^ 2940 := by
      rw [mul_pow, ← pow_mul, ← pow_mul]

/--
strong window 上の boundary-failure residue bound は

  B(U) ≤ 2^269 * n^2940

で抑えられる。

`rhinGapK = 16384 = 2^14` なので、
window の `2^255` と合わせて `2^269` になる。

巨大な `2^269` 自体は評価せず、
冪指数の加法だけで処理する。
-/
private theorem strong_residue_bound_tail
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    boundaryFailureResidueBound
        rhinGapK
        rhinGapA
        (strongDenominatorWindowUpper criticalPowerQ j)
      ≤
    2 ^ 269 * criticalPowerQ (j - 1) ^ 2940 := by
  let n := criticalPowerQ (j - 1)
  let U := strongDenominatorWindowUpper criticalPowerQ j
  have hUPowBound :
      (U + 2) ^ 15 ≤
        2 ^ 255 * n ^ 2940 := by
    simpa [U, n] using
      strong_window_pow_bound_tail R hj
  have hTwoConst :
      16384 * 2 ^ 255 =
        2 ^ 269 := by
    calc
      16384 * 2 ^ 255
          = 2 ^ 14 * 2 ^ 255 := by
            rw [show (16384 : ℕ) = 2 ^ 14 by norm_num]
      _ = 2 ^ (14 + 255) := by
        rw [pow_add]
      _ = 2 ^ 269 := by
        congr 1
  unfold
    boundaryFailureResidueBound
    rhinGapK
    rhinGapA
  norm_num
  calc
    16384 * (U + 2) ^ 15
        ≤ 16384 * (2 ^ 255 * n ^ 2940) :=
      Nat.mul_le_mul_left
        16384
        hUPowBound
    _ =
        (16384 * 2 ^ 255) * n ^ 2940 := by
      ac_rfl
    _ =
        2 ^ 269 * n ^ 2940 := by
      rw [hTwoConst]

/--
positive residue bound に 1 を加えても、

  B(U) + 1 ≤ 2^270 * n^2940

で抑えられる。

まず `B+1 ≤ 2B` とし、
`2 * 2^269 = 2^270` を記号的に処理する。
-/
private theorem strong_residue_succ_bound_tail
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    boundaryFailureResidueBound
        rhinGapK
        rhinGapA
        (strongDenominatorWindowUpper criticalPowerQ j) + 1
      ≤
    2 ^ 270 * criticalPowerQ (j - 1) ^ 2940 := by
  let n := criticalPowerQ (j - 1)
  let U := strongDenominatorWindowUpper criticalPowerQ j
  have hB :
      boundaryFailureResidueBound
          rhinGapK rhinGapA U
        ≤ 2 ^ 269 * n ^ 2940 := by
    simpa [U, n] using
      strong_residue_bound_tail R hj
  have hBPos :
      0 <
        boundaryFailureResidueBound
          rhinGapK rhinGapA U := by
    unfold
      boundaryFailureResidueBound
      rhinGapK
      rhinGapA
    positivity
  have hdouble :
      boundaryFailureResidueBound
          rhinGapK rhinGapA U + 1
        ≤
      2 *
        boundaryFailureResidueBound
          rhinGapK rhinGapA U := by
    omega
  have hTwoConst :
      2 * 2 ^ 269 =
        2 ^ 270 := by
    calc
      2 * 2 ^ 269
          = 2 ^ 1 * 2 ^ 269 := by
            norm_num
      _ = 2 ^ (1 + 269) := by
        rw [pow_add]
      _ = 2 ^ 270 := by
        congr 1
  calc
    boundaryFailureResidueBound
        rhinGapK rhinGapA U + 1
        ≤
      2 *
        boundaryFailureResidueBound
          rhinGapK rhinGapA U := hdouble
    _ ≤
        2 * (2 ^ 269 * n ^ 2940) :=
      Nat.mul_le_mul_left 2 hB
    _ =
        (2 * 2 ^ 269) * n ^ 2940 := by
      ac_rfl
    _ =
        2 ^ 270 * n ^ 2940 := by
      rw [hTwoConst]

/--
tail range `j ≥ 12` の strong-window 左辺全体は、

  4 * q_j * (B(U) + 1)
    ≤ 2^273 * q_(j-1)^2954

で抑えられる。

`q_j ≤ 2 n^14` と
`B(U)+1 ≤ 2^270 n^2940`
を掛け合わせるだけであり、
定数・指数整理は別の exact identity として処理する。
-/
private theorem strong_left_bound_tail
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    4 * criticalPowerQ j *
        (boundaryFailureResidueBound
            rhinGapK rhinGapA
            (strongDenominatorWindowUpper criticalPowerQ j) + 1)
      ≤
    2 ^ 273 * criticalPowerQ (j - 1) ^ 2954 := by
  let n := criticalPowerQ (j - 1)
  let q := criticalPowerQ j
  let U := strongDenominatorWindowUpper criticalPowerQ j
  have hq :
      q ≤ 2 * n ^ 14 := by
    simpa [q, n] using
      strong_current_q_bound_tail R hj
  have hB1 :
      boundaryFailureResidueBound
          rhinGapK rhinGapA U + 1
        ≤
      2 ^ 270 * n ^ 2940 := by
    simpa [U, n] using
      strong_residue_succ_bound_tail R hj
  have hTwoConst :
      4 * 2 * 2 ^ 270 =
        2 ^ 273 := by
    calc
      4 * 2 * 2 ^ 270
          =
        2 ^ 2 * 2 ^ 1 * 2 ^ 270 := by
          norm_num
      _ =
        2 ^ (2 + 1) * 2 ^ 270 := by
          rw [pow_add]
      _ =
        2 ^ ((2 + 1) + 270) := by
          rw [pow_add]
          decide
      _ =
        2 ^ 273 := by
          congr 1
  have hnConst :
      n ^ 14 * n ^ 2940 =
        n ^ 2954 := by
    calc
      n ^ 14 * n ^ 2940
          = n ^ (14 + 2940) := by
            rw [pow_add]
      _ = n ^ 2954 := by
        congr 1
  calc
    4 * criticalPowerQ j *
        (boundaryFailureResidueBound
          rhinGapK rhinGapA
          (strongDenominatorWindowUpper criticalPowerQ j) + 1)
        =
      4 * q *
        (boundaryFailureResidueBound
          rhinGapK rhinGapA U + 1) := by
      rfl
    _ ≤
        4 * (2 * n ^ 14) *
          (2 ^ 270 * n ^ 2940) := by
      exact
        Nat.mul_le_mul
          (Nat.mul_le_mul_left 4 hq)
          hB1
    _ =
        (4 * 2 * 2 ^ 270) *
          (n ^ 14 * n ^ 2940) := by
      ac_rfl
    _ =
        2 ^ 273 * n ^ 2954 := by
      rw [hTwoConst, hnConst]

private theorem strong_domination_tail
    (R : RhinLinearForm14)
    {j : ℕ}
    (hj : 12 ≤ j) :
    4 * criticalPowerQ j *
        (boundaryFailureResidueBound
            rhinGapK rhinGapA
            (strongDenominatorWindowUpper criticalPowerQ j) + 1)
      <
    2 ^ (criticalPowerQ (j - 1) - 1) := by
  have hleft := strong_left_bound_tail R hj
  have hnLower : 50508 ≤ criticalPowerQ (j - 1) := by
    have hindex : 11 ≤ j - 1 := by omega
    have hm := criticalPowerQ_mono_of_le hindex
    rw [criticalPowerQ_eleven] at hm
    exact hm
  have htail := polynomial_lt_dyadic_tail hnLower
  exact lt_of_le_of_lt hleft htail

/-- actual Step-8 certificate from the single Rhin theorem. -/
theorem toActualStrongSlackStartNine
    (R : RhinLinearForm14) :
    RhinStrongSlackStartNineCertificate
      actualOrientedCriticalContinuedFractionData := by
  refine {
    start_eq_nine := rfl
    q_eight := criticalPowerQ_eight
    q_nine := criticalPowerQ_nine
    dominates := ?_
  }
  intro j hj
  by_cases htail : 12 ≤ j
  · exact strong_domination_tail R htail
  · have hjTop : j ≤ 11 := by omega
    interval_cases j <;>
      simp only [boundaryFailureResidueBound, rhinGapK, strongDenominatorWindowUpper,
          Nat.reduceAdd, rhinGapA,
    Nat.add_one_sub_one, gt_iff_lt] <;>
      native_decide

end RhinLinearForm14

end ExternalArithmetic
end CSTMicro
end Collatz2
