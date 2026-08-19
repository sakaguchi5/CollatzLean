import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBTerminalState
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.RhinRecordPublic
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelHeightSqueeze

/-!
# Terminal critical suffix polylog bound

改良後の route:

  terminal B
    -> small positive tail state Z
    -> record start is BoundaryXiCandidate
    -> strong Xi / Christoffel H=4
    -> height lower bound と Rhin denominator growth 1回だけで
       every record length L = O((log m)^14)
    -> each carry record has Rhin phase drop >= (2L)^(-14)
    -> number of records O(L^14)
    -> terminal suffix length O(L^15)
    -> O((log m)^210).

既存 repo の private theorem / def は外から使用しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-! ## 1. elementary dyadic-vs-polynomial estimate -/

/-- `log 2 > 1/2`。 -/
theorem record_log_two_gt_half :
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

/-- `log 2 < 1`。 -/
theorem record_log_two_lt_one : Real.log 2 < 1 := by
  have h :=
    Real.log_lt_sub_one_of_pos
      (x := (2 : ℝ)) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

/-- `n>32768` で使う粗い logarithm upper bound。 -/
theorem record_log_nat_upper_from_32768
    {n : ℕ}
    (hn : 32768 < n) :
    Real.log (n : ℝ) <
      (n : ℝ) / 32768 - 1 + 15 * Real.log 2 := by
  have hnR : (32768 : ℝ) < n := by exact_mod_cast hn
  have hxPos : 0 < (n : ℝ) / 32768 := by positivity
  have hxNe : (n : ℝ) / 32768 ≠ 1 := by
    intro h
    have hEq : (n : ℝ) = 32768 :=
      (div_eq_one_iff_eq (by norm_num : (32768 : ℝ) ≠ 0)).mp h
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

/--
`2^(n-1) <= 8 n^14 2^ell` なら `n` は ell に線形。
定数は最適化せず 65536 に固定する。
-/
theorem dyadic_poly14_forces_linear
    {n ell : ℕ}
    (hMain :
      2 ^ (n - 1) ≤ 8 * n ^ 14 * 2 ^ ell) :
    n ≤ 65536 * (ell + 1) := by
  by_cases hnSmall : n ≤ 32768
  · have hOne : 1 ≤ ell + 1 := by omega
    nlinarith
  · have hnLarge : 32768 < n := by omega
    have hnPos : 0 < n := by omega
    have hReal :
        (2 : ℝ) ^ (n - 1) ≤
          8 * (n : ℝ) ^ 14 * (2 : ℝ) ^ ell := by
      exact_mod_cast hMain
    have hLog :=
      Real.log_le_log
        (by positivity : (0 : ℝ) < (2 : ℝ) ^ (n - 1))
        hReal
    have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      have heq : (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      rw [heq, Real.log_pow]
      norm_num
    have hcastPred : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [Real.log_pow] at hLog
    rw [Real.log_mul (by positivity) (by positivity)] at hLog
    rw [Real.log_mul (by positivity) (by positivity)] at hLog
    rw [Real.log_pow, Real.log_pow, hlog8, hcastPred] at hLog
    norm_num at hLog
    have hlogn := record_log_nat_upper_from_32768 hnLarge
    have hlog2Low := record_log_two_gt_half
    have hlog2High := record_log_two_lt_one
    have hEllNonneg : (0 : ℝ) ≤ ell := by positivity
    have hEllLog : (ell : ℝ) * Real.log 2 ≤ ell := by
      have := mul_le_mul_of_nonneg_left (le_of_lt hlog2High) hEllNonneg
      norm_num at this ⊢
      exact this
    have hnRealOne : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    have hPredPos : (0 : ℝ) < (n : ℝ) - 1 := by
      linarith
    have hLower :
        ((n : ℝ) - 1) / 2 <
          ((n : ℝ) - 1) * Real.log 2 := by
      have := mul_lt_mul_of_pos_left hlog2Low hPredPos
      norm_num at this ⊢
      nlinarith
    have hCoarse :
        ((n : ℝ) - 1) / 2 <
          (ell : ℝ) + 199 + 14 * (n : ℝ) / 32768 := by
      nlinarith
    by_contra hnot
    have hBigNat : 65536 * (ell + 1) < n := by omega
    have hBig :
        (65536 : ℝ) * ((ell : ℝ) + 1) < n := by
      exact_mod_cast hBigNat
    nlinarith

/-! ## 2. small Xi candidate -> degree-14 precision bound -/

/-- strong windows用 sequence monotonicity helper。 -/
theorem natSeq_mono_of_succ
    (q : ℕ → ℕ)
    (hSucc : ∀ n : ℕ, q n ≤ q (n + 1))
    {a b : ℕ}
    (hab : a ≤ b) :
    q a ≤ q b := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact le_rfl
  | succ b ih =>
      by_cases hEq : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a ≤ b := by omega
        exact le_trans (ih hab') (hSucc b)

/-- start-nearby strong windows を吸収する absolute exceptional precision。 -/
def terminalRecordExceptionalPrecision : ℕ :=
  strongDenominatorWindowUpper criticalPowerQ 11

/--
large-window 側の degree-14 coefficient。
height inequality から precision を直接読むための coefficient。
-/
def smallXiTailConstant : ℕ :=
  4 * 65536 ^ 14 + 2

/-- generic small-Xi precision bound。 -/
def smallXiPrecisionBound (ell : ℕ) : ℕ :=
  max 1538
    (max terminalRecordExceptionalPrecision
      (smallXiTailConstant * (ell + 1) ^ 14))

/--
large precision の Xi candidate から、
actual record strong window と height lower bound を同時に取り出す。

ここに López--Stoll / Christoffel packet 側の実装詳細を閉じ込める。
後段では `criticalPowerQ` だけを扱えばよい。
-/
theorem exists_actualRecord_window_with_heightLower
    (R : RhinLinearForm14)
    {e x : ℕ}
    (hLarge : 1538 ≤ e)
    (hCandidate : BoundaryXiCandidate e x) :
    ∃ j : ℕ,
      strongDenominatorWindowLower criticalPowerQ j ≤ e ∧
      e ≤ strongDenominatorWindowUpper criticalPowerQ j ∧
      2 ^ e ≤
        (4 * criticalPowerQ j * 2 ^ criticalPowerQ j) *
          (x + 1) := by
  let L := actualRecordLopezStollInstantiation
  let C := actualRecordHeightFour R
  have hLq : L.q = criticalPowerQ := by
    funext k
    rfl
  have hFirst :
      strongFirstPrecision L = 1538 := by
    simpa [L] using
      actualRecord_firstPrecision_eq_1538 R
  have hFirstLow :
      strongDenominatorWindowLower L.q L.start = 1538 := by
    simpa [strongFirstPrecision] using hFirst
  have hLow :
      strongDenominatorWindowLower L.q L.start ≤ e := by
    calc
      strongDenominatorWindowLower L.q L.start
          = 1538 := hFirstLow
      _ ≤ e := hLarge
  have hStartOne :
      1 ≤ L.start :=
    le_trans (by decide : 1 ≤ 3) L.start_ge_three
  have hCofinal :
      ∀ N : ℕ, ∃ j : ℕ,
        L.start ≤ j ∧
        N ≤ strongDenominatorWindowUpper L.q j :=
    strongDenominatorWindowUpper_cofinal_of_q_cofinal
      L.q L.q_cofinal
  rcases exists_strongDenominatorWindow_cofinal
      L.q hStartOne hLow hCofinal with
    ⟨j, hjStart, hWindowLow, hWindowUpper⟩
  have hWindowLowCritical :
      strongDenominatorWindowLower criticalPowerQ j ≤ e := by
    simpa only [hLq] using hWindowLow
  have hWindowUpperCritical :
      e ≤ strongDenominatorWindowUpper criticalPowerQ j := by
    simpa only [hLq] using hWindowUpper
  have hMatch :
      (L.packet j).Matches e x := by
    change MatchesAtTwoPower e (L.P j) (L.Q j) x
    exact
      actualRecordStrongBoundaryMatch.xiTargetAgreement
        j e x
        (by simpa [L] using hjStart)
        (by simpa [L] using hWindowUpper)
        hCandidate
  have hHeight :
      HasChristoffelHeightBound
        4
        (L.packet j).q
        (L.packet j).P
        (L.packet j).Q := by
    have h0 := C.height j
    simpa [C, L, LopezStollInstantiation.packet] using h0
  have hHeightLower :
      2 ^ e ≤
        (4 * (L.packet j).q *
            2 ^ (L.packet j).q) *
          (x + 1) := by
    by_contra hnot
    have hlt :
        (4 * (L.packet j).q *
            2 ^ (L.packet j).q) *
            (x + 1) <
          2 ^ e := by
      omega
    exact
      noSmallResidue_of_height_squeeze
        (L.packet j)
        hMatch
        hHeight
        (le_rfl : x ≤ x)
        hlt
  have hHeightLowerCritical :
      2 ^ e ≤
        (4 * criticalPowerQ j *
            2 ^ criticalPowerQ j) *
          (x + 1) := by
    simpa [L, LopezStollInstantiation.packet] using
      hHeightLower
  exact
    ⟨j,
      hWindowLowCritical,
      hWindowUpperCritical,
      hHeightLowerCritical⟩

/--
tail range `12 ≤ j` では、
Xi candidate の dyadic size と height squeeze から

  q_(j-1) ≤ 65536 * (ell+1)

を得る。
-/
theorem actualRecord_tail_prevQ_le_linear
    (R : RhinLinearForm14)
    {e x ell j : ℕ}
    (hxSize : x + 1 ≤ 2 ^ ell)
    (hWindowLow :
      strongDenominatorWindowLower criticalPowerQ j ≤ e)
    (hHeightLower :
      2 ^ e ≤
        (4 * criticalPowerQ j *
            2 ^ criticalPowerQ j) *
          (x + 1))
    (hjTail : 12 ≤ j) :
    criticalPowerQ (j - 1) ≤
      65536 * (ell + 1) := by
  let n := criticalPowerQ (j - 1)
  let q := criticalPowerQ j
  have hnPos : 0 < n := by
    dsimp [n]
    exact criticalPowerQ_pos _
  have hqPos : 0 < q := by
    dsimp [q]
    exact criticalPowerQ_pos _
  have hLowNQ :
      n + q - 1 ≤ e := by
    simpa [n, q, strongDenominatorWindowLower] using
      hWindowLow
  have hHeightLower' :
      2 ^ e ≤
        (4 * q * 2 ^ q) * (x + 1) := by
    simpa [q] using hHeightLower
  have hSizeScaled :
      (4 * q * 2 ^ q) * (x + 1) ≤
        (4 * q * 2 ^ q) * 2 ^ ell :=
    Nat.mul_le_mul_left
      (4 * q * 2 ^ q)
      hxSize
  have hPowNQ :
      2 ^ (n + q - 1) ≤
        (4 * q * 2 ^ q) * 2 ^ ell := by
    calc
      2 ^ (n + q - 1)
          ≤ 2 ^ e :=
        Nat.pow_le_pow_right
          (by omega : 0 < (2 : ℕ))
          hLowNQ
      _ ≤ (4 * q * 2 ^ q) * (x + 1) :=
        hHeightLower'
      _ ≤ (4 * q * 2 ^ q) * 2 ^ ell :=
        hSizeScaled
  have hExp :
      n + q - 1 = (n - 1) + q := by
    omega
  rw [hExp, pow_add] at hPowNQ
  have hMul :
      2 ^ (n - 1) * 2 ^ q ≤
        (4 * q * 2 ^ ell) * 2 ^ q := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      hPowNQ
  have hCancel :
      2 ^ (n - 1) ≤
        4 * q * 2 ^ ell := by
    by_contra hnot
    have hgt :
        4 * q * 2 ^ ell <
          2 ^ (n - 1) := by
      omega
    have hgtMul :=
      Nat.mul_lt_mul_of_pos_right
        hgt
        (by positivity : 0 < 2 ^ q)
    omega
  have hqBound :
      q ≤ 2 * n ^ 14 := by
    simpa [q, n] using
      R.actual_record_current_q_le_prev_pow14
        hjTail
  have hMain :
      2 ^ (n - 1) ≤
        8 * n ^ 14 * 2 ^ ell := by
    calc
      2 ^ (n - 1)
          ≤ 4 * q * 2 ^ ell :=
        hCancel
      _ ≤ 4 * (2 * n ^ 14) * 2 ^ ell :=
        Nat.mul_le_mul_right
          (2 ^ ell)
          (Nat.mul_le_mul_left 4 hqBound)
      _ = 8 * n ^ 14 * 2 ^ ell := by
        ring
  exact dyadic_poly14_forces_linear hMain

/--
height lower bound から、指数部分だけを取り出して
`e ≤ q + q + ell + 2` を得る。
-/
private theorem precision_le_two_q_add_ell_add_two
    {e x ell q : ℕ}
    (hxSize : x + 1 ≤ 2 ^ ell)
    (hHeightLower :
      2 ^ e ≤
        (4 * q * 2 ^ q) * (x + 1)) :
    e ≤ q + q + ell + 2 := by
  have hSizeScaled :
      (4 * q * 2 ^ q) * (x + 1) ≤
        (4 * q * 2 ^ q) * 2 ^ ell :=
    Nat.mul_le_mul_left (4 * q * 2 ^ q) hxSize
  have hqPow : q ≤ 2 ^ q := by
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have hCoeff :
      4 * q * 2 ^ q ≤
        4 * (2 ^ q) * 2 ^ q := by
    exact
      Nat.mul_le_mul_right (2 ^ q)
        (Nat.mul_le_mul_left 4 hqPow)
  have hCoeffScaled :
      (4 * q * 2 ^ q) * 2 ^ ell ≤
        (4 * (2 ^ q) * 2 ^ q) * 2 ^ ell :=
    Nat.mul_le_mul_right (2 ^ ell) hCoeff
  have hPowEq :
      (4 * (2 ^ q) * 2 ^ q) * 2 ^ ell =
        2 ^ (q + q + ell + 2) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    simp only [pow_add]
    ring
  have hPowBound :
      2 ^ e ≤ 2 ^ (q + q + ell + 2) := by
    calc
      2 ^ e ≤ (4 * q * 2 ^ q) * (x + 1) := hHeightLower
      _ ≤ (4 * q * 2 ^ q) * 2 ^ ell := hSizeScaled
      _ ≤ (4 * (2 ^ q) * 2 ^ q) * 2 ^ ell := hCoeffScaled
      _ = 2 ^ (q + q + ell + 2) := hPowEq
  exact
    (Nat.pow_le_pow_iff_right
      (by decide : 1 < (2 : ℕ))).mp hPowBound


/--
previous q の linear bound と Rhin の degree-14 bound から、
current q を `ell` の degree 14 多項式で抑える。
-/
private theorem actualRecord_tail_current_q_le_explicit
    (R : RhinLinearForm14)
    {ell j : ℕ}
    (hjTail : 12 ≤ j)
    (hPrevLinear :
      criticalPowerQ (j - 1) ≤
        65536 * (ell + 1)) :
    criticalPowerQ j ≤
      2 * (65536 ^ 14) * (ell + 1) ^ 14 := by
  let n := criticalPowerQ (j - 1)
  let q := criticalPowerQ j
  have hqBound : q ≤ 2 * n ^ 14 := by
    simpa [q, n] using
      R.actual_record_current_q_le_prev_pow14 hjTail
  have hnLinear :
      n ≤ 65536 * (ell + 1) := by
    simpa [n] using hPrevLinear
  have hnPow :
      n ^ 14 ≤
        (65536 * (ell + 1)) ^ 14 :=
    Nat.pow_le_pow_left hnLinear 14
  have hqSub :
      q ≤ 2 * (65536 * (ell + 1)) ^ 14 :=
    le_trans hqBound
      (Nat.mul_le_mul_left 2 hnPow)
  calc
    q ≤ 2 * (65536 * (ell + 1)) ^ 14 := hqSub
    _ = 2 * (65536 ^ 14) * (ell + 1) ^ 14 := by
      rw [mul_pow]
      ring


/--
`ell + 1` はその 14 乗以下。
この小補題を独立させて power normalization を隔離する。
-/
private theorem ell_add_one_le_pow14
    (ell : ℕ) :
    ell + 1 ≤ (ell + 1) ^ 14 := by
  have h :=
    Nat.pow_le_pow_right
      (by omega : 0 < ell + 1)
      (by norm_num : 1 ≤ 14)
  simpa using h


/--
`q ≤ 2 A M` と `ell + 1 ≤ M` から、
`q + q + ell + 2` 全体を一つの `M` に吸収する。

巨大定数を入れず、純粋な symbolic arithmetic として処理する。
-/
private theorem two_q_add_ell_add_two_le_tail
    {q ell A M : ℕ}
    (hq : q ≤ 2 * A * M)
    (hM : ell + 1 ≤ M) :
    q + q + ell + 2 ≤
      (4 * A + 2) * M := by
  have hEll :
      ell + 2 ≤ 2 * M := by
    have h0 :
        ell + 2 ≤ 2 * (ell + 1) := by
      omega
    exact
      le_trans h0
        (Nat.mul_le_mul_left 2 hM)
  calc
    q + q + ell + 2
        ≤
      (2 * A * M) +
        (2 * A * M) +
        2 * M := by
          omega
    _ = (4 * A + 2) * M := by
      ring


/--
tail 部分について precision を
`smallXiTailConstant * (ell+1)^14` まで抑える。
-/
private theorem actualRecord_tail_precision_le_explicit
    (R : RhinLinearForm14)
    {e x ell j : ℕ}
    (hxSize : x + 1 ≤ 2 ^ ell)
    (hHeightLower :
      2 ^ e ≤
        (4 * criticalPowerQ j *
          2 ^ criticalPowerQ j) *
          (x + 1))
    (hjTail : 12 ≤ j)
    (hPrevLinear :
      criticalPowerQ (j - 1) ≤
        65536 * (ell + 1)) :
    e ≤
      smallXiTailConstant * (ell + 1) ^ 14 := by
  let q := criticalPowerQ j
  have hHeightLower' :
      2 ^ e ≤
        (4 * q * 2 ^ q) * (x + 1) := by
    simpa [q] using hHeightLower
  have heCore :
      e ≤ q + q + ell + 2 :=
    precision_le_two_q_add_ell_add_two
      hxSize hHeightLower'
  have hq :
      q ≤
        2 * (65536 ^ 14) *
          (ell + 1) ^ 14 := by
    simpa [q] using
      actualRecord_tail_current_q_le_explicit
        R hjTail hPrevLinear
  have hM :
      ell + 1 ≤ (ell + 1) ^ 14 :=
    ell_add_one_le_pow14 ell
  have hTail :
      q + q + ell + 2 ≤
        (4 * (65536 ^ 14) + 2) *
          (ell + 1) ^ 14 := by
    exact
      two_q_add_ell_add_two_le_tail
        hq hM
  have he :
      e ≤
        (4 * (65536 ^ 14) + 2) *
          (ell + 1) ^ 14 :=
    le_trans heCore hTail
  simpa [smallXiTailConstant] using he


/--
height lower bound をもう一度直接使い、precision を degree 14 で抑える。

ここでは q_(j+1) へ進まず、height lower bound から precision を直接読む。
-/
theorem actualRecord_tail_precision_le_smallXiPrecisionBound
    (R : RhinLinearForm14)
    {e x ell j : ℕ}
    (hxSize : x + 1 ≤ 2 ^ ell)
    (hHeightLower :
      2 ^ e ≤
        (4 * criticalPowerQ j *
          2 ^ criticalPowerQ j) *
          (x + 1))
    (hjTail : 12 ≤ j)
    (hPrevLinear :
      criticalPowerQ (j - 1) ≤
        65536 * (ell + 1)) :
    e ≤ smallXiPrecisionBound ell := by
  have heExplicit :
      e ≤
        smallXiTailConstant *
          (ell + 1) ^ 14 :=
    actualRecord_tail_precision_le_explicit
      R
      hxSize
      hHeightLower
      hjTail
      hPrevLinear
  unfold smallXiPrecisionBound
  exact
    le_trans heExplicit
      (le_trans
        (le_max_right _ _)
        (le_max_right _ _))

/--
`j < 12` の有限 exceptional range では、
strong window upper endpoint は固定 exceptional precision 以下。
-/
theorem actualRecord_exceptional_precision_le_smallXiPrecisionBound
    {e ell j : ℕ}
    (hWindowUpper :
      e ≤ strongDenominatorWindowUpper criticalPowerQ j)
    (hjLt : j < 12) :
    e ≤ smallXiPrecisionBound ell := by
  have hqj :
      criticalPowerQ j ≤
        criticalPowerQ 11 :=
    criticalPowerQ_mono_of_le
      (by omega)
  have hqj1 :
      criticalPowerQ (j + 1) ≤
        criticalPowerQ 12 :=
    criticalPowerQ_mono_of_le
      (by omega)
  have hExceptional :
      strongDenominatorWindowUpper criticalPowerQ j ≤
        terminalRecordExceptionalPrecision := by
    unfold terminalRecordExceptionalPrecision
      strongDenominatorWindowUpper
    exact
      Nat.sub_le_sub_right
        (Nat.add_le_add hqj hqj1)
        1
  have heExceptional :
      e ≤ terminalRecordExceptionalPrecision := by
    exact le_trans hWindowUpper hExceptional
  unfold smallXiPrecisionBound
  exact
    le_trans heExceptional
      (le_trans (le_max_left _ _) (le_max_right _ _))

/--
Xi candidate `x` が `x+1 <= 2^ell` なら、
その precision は explicit degree-14 bound 以下。
-/
theorem smallXiCandidate_precision_le
    (R : RhinLinearForm14)
    {e x ell : ℕ}
    (hxSize : x + 1 ≤ 2 ^ ell)
    (hCandidate : BoundaryXiCandidate e x) :
    e ≤ smallXiPrecisionBound ell := by
  by_cases hSmall : e < 1538
  · unfold smallXiPrecisionBound
    exact le_trans (Nat.le_of_lt hSmall) (le_max_left _ _)
  · have hLarge : 1538 ≤ e := by omega
    rcases exists_actualRecord_window_with_heightLower
        R hLarge hCandidate with
      ⟨j, hWindowLow, hWindowUpper, hHeightLower⟩
    by_cases hjTail : 12 ≤ j
    · have hPrevLinear :
          criticalPowerQ (j - 1) ≤
            65536 * (ell + 1) :=
        actualRecord_tail_prevQ_le_linear
          R hxSize hWindowLow hHeightLower hjTail
      exact
        actualRecord_tail_precision_le_smallXiPrecisionBound
          R hxSize hHeightLower hjTail hPrevLinear
    · have hjLt : j < 12 := by omega
      exact
        actualRecord_exceptional_precision_le_smallXiPrecisionBound
          hWindowUpper hjLt

/-! ## 3. specialize the candidate bound to terminal B states -/

/-- one record length の `(ell+1)^14` coefficient。 -/
def terminalRecordLengthConstant : ℕ :=
  max 1538
    (max terminalRecordExceptionalPrecision
      (smallXiTailConstant * 21 ^ 14))

/-- one record / final fragment length bound。 -/
def terminalRecordLengthBound (ell : ℕ) : ℕ :=
  terminalRecordLengthConstant * (ell + 1) ^ 14

/-- terminal record length bound は正。 -/
theorem terminalRecordLengthBound_pos (ell : ℕ) :
    0 < terminalRecordLengthBound ell := by
  unfold terminalRecordLengthBound terminalRecordLengthConstant
  positivity

/--
terminal-state 用 size parameter `20+15*ell` を代入した
small-Xi degree-14 bound を一様 record bound へ吸収する。
-/
theorem smallXiPrecisionBound_terminalSize_le_recordLengthBound
    (ell : ℕ) :
    smallXiPrecisionBound (20 + 15 * ell) ≤
      terminalRecordLengthBound ell := by
  let M := (ell + 1) ^ 14
  have hM : 1 ≤ M := by
    have hMpos : 0 < M := by
      dsimp [M]
      positivity
    omega
  have hSizeLinear :
      (20 + 15 * ell) + 1 ≤ 21 * (ell + 1) := by
    omega
  have hPowLinear :
      ((20 + 15 * ell) + 1) ^ 14 ≤
        (21 * (ell + 1)) ^ 14 :=
    Nat.pow_le_pow_left hSizeLinear 14
  have hTailCoeff :
      smallXiTailConstant * ((20 + 15 * ell) + 1) ^ 14 ≤
        (smallXiTailConstant * 21 ^ 14) * M := by
    calc
      smallXiTailConstant * ((20 + 15 * ell) + 1) ^ 14
          ≤ smallXiTailConstant * (21 * (ell + 1)) ^ 14 :=
        Nat.mul_le_mul_left smallXiTailConstant hPowLinear
      _ = (smallXiTailConstant * 21 ^ 14) * M := by
        dsimp [M]
        rw [mul_pow]
        ring
  let C := terminalRecordLengthConstant
  have h1538C : 1538 ≤ C := by
    dsimp [C]
    unfold terminalRecordLengthConstant
    exact le_max_left _ _
  have hExcC : terminalRecordExceptionalPrecision ≤ C := by
    dsimp [C]
    unfold terminalRecordLengthConstant
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCoeffC : smallXiTailConstant * 21 ^ 14 ≤ C := by
    dsimp [C]
    unfold terminalRecordLengthConstant
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have h1538Scaled : 1538 ≤ C * M := by
    calc
      1538 ≤ C := h1538C
      _ = C * 1 := by simp
      _ ≤ C * M := Nat.mul_le_mul_left C hM
  have hExcScaled : terminalRecordExceptionalPrecision ≤ C * M := by
    calc
      terminalRecordExceptionalPrecision ≤ C := hExcC
      _ = C * 1 := by simp
      _ ≤ C * M := Nat.mul_le_mul_left C hM
  have hTailScaled :
      smallXiTailConstant * ((20 + 15 * ell) + 1) ^ 14 ≤ C * M := by
    exact le_trans hTailCoeff (Nat.mul_le_mul_right M hCoeffC)
  unfold smallXiPrecisionBound terminalRecordLengthBound
  change
    max 1538
        (max terminalRecordExceptionalPrecision
          (smallXiTailConstant * ((20 + 15 * ell) + 1) ^ 14)) ≤
      C * M
  exact max_le h1538Scaled (max_le hExcScaled hTailScaled)

/-- `m+1<=2^ell` なら全 tail state の `x+1` は `2^(20+15ell)` 以下。 -/
theorem terminalTailStateNat_succ_le_dyadic
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {a s ell : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hsm : s ≤ P.m)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    P.terminalTailStateNat S hy s has hsm + 1 ≤
      2 ^ (20 + 15 * ell) := by
  have hState := P.terminalTailStateNat_le_four_yNat S hy has hsm
  have hyBound := P.yNat_le_rhinPolynomial R hy
  have hPow : (P.m + 1) ^ 15 ≤ (2 ^ ell) ^ 15 :=
    Nat.pow_le_pow_left hmSize 15
  have hCore :
      P.terminalTailStateNat S hy s has hsm ≤
        4 * rhinGapK * (2 ^ ell) ^ 15 := by
    calc
      P.terminalTailStateNat S hy s has hsm
          ≤ 4 * P.yNat := hState
      _ ≤ 4 * (rhinGapK * (P.m + 1) ^ 15) :=
        Nat.mul_le_mul_left 4 hyBound
      _ ≤ 4 * rhinGapK * (2 ^ ell) ^ 15 := by
        nlinarith
  have hPowerEq :
      4 * rhinGapK * (2 ^ ell) ^ 15 =
        2 ^ (16 + 15 * ell) := by
    unfold rhinGapK
    norm_num
    rw [← pow_mul]
    have hMul : ell * 15 = 15 * ell := by omega
    rw [hMul, pow_add]
    ring
  rw [hPowerEq] at hCore
  have hPos : 0 < 2 ^ (16 + 15 * ell) := by positivity
  have hSucc :
      P.terminalTailStateNat S hy s has hsm + 1 ≤
        2 * 2 ^ (16 + 15 * ell) := by
    omega
  calc
    P.terminalTailStateNat S hy s has hsm + 1
        ≤ 2 * 2 ^ (16 + 15 * ell) := hSucc
    _ = 2 ^ (17 + 15 * ell) := by
      have hExp : 17 + 15 * ell = (16 + 15 * ell) + 1 := by omega
      rw [hExp, pow_succ]
      ring
    _ ≤ 2 ^ (20 + 15 * ell) :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)

/-- positive record length is below its Beatty precision。 -/
theorem length_le_beattyIndex
    {r : ℕ}
    (hr : 0 < r) :
    r ≤ beattyIndex r := by
  have hPow : 2 ^ r < 3 ^ r :=
    Nat.pow_lt_pow_left (by norm_num : 2 < 3) (Nat.ne_of_gt hr)
  have hCrit := Collatz2.Word.le_criticalHeight_of_twoPow_lt_threePow hPow
  simpa [beattyIndex_eq_wordCriticalHeight_all] using hCrit

/-- one first-carry record の degree-14 length bound。 -/
theorem terminalRecordPiece_length_le
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {a s r ell : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hend : s + r ≤ P.m)
    (B : CriticalRecordPiece s r)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    r ≤ terminalRecordLengthBound ell := by
  let x := P.terminalTailStateNat S hy s has (by omega : s ≤ P.m)
  have hxSize : x + 1 ≤ 2 ^ (20 + 15 * ell) := by
    simpa [x] using
      terminalTailStateNat_succ_le_dyadic R P S hy has (by omega) hmSize
  have hCandidate := P.terminalRecordStart_isBoundaryXiCandidate S hy has hend B
  have hPrec := smallXiCandidate_precision_le R hxSize hCandidate
  have hre : r ≤ beattyIndex r := length_le_beattyIndex B.length_pos
  exact le_trans hre
    (le_trans hPrec (smallXiPrecisionBound_terminalSize_le_recordLengthBound ell))

/-- final no-carry fragment も同じ degree-14 length bound。 -/
theorem terminalNoCarryFragment_length_le
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {a s r ell : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (has : a ≤ s)
    (hend : s + r ≤ P.m)
    (F : CriticalNoCarryFragment s r)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    r ≤ terminalRecordLengthBound ell := by
  by_cases hr0 : r = 0
  · subst r
    omega
  · have hrPos : 0 < r := Nat.pos_of_ne_zero hr0
    let x := P.terminalTailStateNat S hy s has (by omega : s ≤ P.m)
    have hxSize : x + 1 ≤ 2 ^ (20 + 15 * ell) := by
      simpa [x] using
        terminalTailStateNat_succ_le_dyadic R P S hy has (by omega) hmSize
    have hCandidate := P.terminalNoCarryStart_isBoundaryXiCandidate S hy has hend F
    have hPrec := smallXiCandidate_precision_le R hxSize hCandidate
    have hre : r ≤ beattyIndex r := length_le_beattyIndex hrPos
    exact le_trans hre
      (le_trans hPrec (smallXiPrecisionBound_terminalSize_le_recordLengthBound ell))

/-! ## 4. Rhin phase packing -/

/-- record carry の phase drop は upper errorそのもの。 -/
theorem CriticalRecordPiece.phase_drop_eq_upperError
    {s r : ℕ}
    (B : CriticalRecordPiece s r) :
    criticalRealPhase s - criticalRealPhase (s + r) =
      criticalUpperError r := by
  have hAdd := criticalRealPhase_add s r
  rw [B.terminal_carry] at hAdd
  norm_num at hAdd
  rw [criticalUpperError_eq_log_two_sub_phase]
  linarith

/-- critical upper exponent `beta_r+1` は `2r` 以下。 -/
theorem beattyIndex_succ_le_two_mul
    {r : ℕ}
    (hr : 0 < r) :
    beattyIndex r + 1 ≤ 2 * r := by
  have hBase : 3 ^ r ≤ 4 ^ r :=
    Nat.pow_le_pow_left (by norm_num : 3 ≤ 4) r
  have hFour : 4 ^ r = 2 ^ (2 * r) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  rw [hFour] at hBase
  have hIdx : beattyIndex r ≤ 2 * r - 1 := by
    apply beattyIndex_le_of_upper
    simpa [show (2 * r - 1) + 1 = 2 * r by omega] using hBase
  omega

/-- one record の Rhin phase drop lower bound。 -/
theorem RhinLinearForm14.record_phase_drop_lower
    (R : RhinLinearForm14)
    {s r L : ℕ}
    (B : CriticalRecordPiece s r)
    (hrL : r ≤ L) :
    1 / (((2 * L : ℕ) : ℝ) ^ 14) ≤
      criticalRealPhase s - criticalRealPhase (s + r) := by
  have hqPos : 0 < beattyIndex r + 1 := by omega
  have hqTwo : 2 ≤ beattyIndex r + 1 := by
    have hBetaPos : 0 < beattyIndex r := by
      have h := beattyIndex_strictMono (a := 0) (b := r) B.length_pos
      simpa using h
    omega
  have hMaxTwo : 2 ≤ max r (beattyIndex r + 1) :=
    le_max_of_le_right hqTwo
  have hRhin :=
    R.lower r (beattyIndex r + 1)
      B.length_pos hqPos hMaxTwo
  have hErrPos := criticalUpperError_pos r
  have hErrEq :
      ((beattyIndex r + 1 : ℕ) : ℝ) * Real.log 2 -
          (r : ℝ) * Real.log 3 = criticalUpperError r := by
    unfold criticalUpperError
    push_cast
    rfl
  rw [hErrEq, abs_of_pos hErrPos] at hRhin
  have hqLe : beattyIndex r + 1 ≤ 2 * r := beattyIndex_succ_le_two_mul B.length_pos
  have hMaxLeR : max r (beattyIndex r + 1) ≤ 2 * r := by
    apply max_le
    · omega
    · exact hqLe
  have hRL : 2 * r ≤ 2 * L := Nat.mul_le_mul_left 2 hrL
  have hMaxLe : max r (beattyIndex r + 1) ≤ 2 * L :=
    le_trans hMaxLeR hRL
  have hMaxPos :
      0 < (((max r (beattyIndex r + 1) : ℕ) : ℝ) ^ 14) := by positivity
  have hLPosNat : 0 < 2 * L := by
    have hL : 0 < L := lt_of_lt_of_le B.length_pos hrL
    omega
  have hLPos : 0 < (((2 * L : ℕ) : ℝ) ^ 14) := by positivity
  have hPowLe :
      (((max r (beattyIndex r + 1) : ℕ) : ℝ) ^ 14) ≤
        (((2 * L : ℕ) : ℝ) ^ 14) := by
    have hCast :
        ((max r (beattyIndex r + 1) : ℕ) : ℝ) ≤ (2 * L : ℕ) := by
      exact_mod_cast hMaxLe
    gcongr
  have hInv :
      1 / (((2 * L : ℕ) : ℝ) ^ 14) ≤
        1 / (((max r (beattyIndex r + 1) : ℕ) : ℝ) ^ 14) := by
    exact (div_le_div_iff₀ hLPos hMaxPos).2 (by nlinarith [hPowLe])
  have hRhin' :
      1 / (((max r (beattyIndex r + 1) : ℕ) : ℝ) ^ 14) ≤
        criticalUpperError r := by
    simpa only [one_div] using hRhin
  have hLower :
      1 / (((2 * L : ℕ) : ℝ) ^ 14) ≤
        criticalUpperError r := by
    exact le_trans hInv hRhin'
  rw [B.phase_drop_eq_upperError]
  exact hLower

/-- chain 内の全 record が L 以下なら count/L^14 は start phase 以下。 -/
theorem CriticalRecordChain.recordCount_div_le_phase
    (R : RhinLinearForm14)
    {start remaining L : ℕ}
    (C : CriticalRecordChain start remaining)
    (hLengths : ∀ r : ℕ, r ∈ C.recordLengths → r ≤ L) :
    (C.recordCount : ℝ) / (((2 * L : ℕ) : ℝ) ^ 14) ≤
      criticalRealPhase start := by
  induction C with
  | final fragment =>
      simp only [recordCount, CharP.cast_eq_zero, Nat.cast_mul, Nat.cast_ofNat, zero_div]
      exact criticalRealPhase_nonneg _
  | @step start remaining r hrPos hrLe piece tail ih =>
      have hrL : r ≤ L := by
        apply hLengths r
        simp [CriticalRecordChain.recordLengths]
      have hTailLengths :
          ∀ u : ℕ, u ∈ tail.recordLengths → u ≤ L := by
        intro u hu
        exact hLengths u (by simp [CriticalRecordChain.recordLengths, hu])
      have hIH := ih hTailLengths
      have hDrop := R.record_phase_drop_lower piece hrL
      have hCount :
          (CriticalRecordChain.step hrPos hrLe piece tail).recordCount =
            tail.recordCount + 1 := by simp
      have hPhaseAdd :
          criticalRealPhase start =
            criticalRealPhase (start + r) +
              (criticalRealPhase start - criticalRealPhase (start + r)) := by
        ring
      rw [hCount, hPhaseAdd]
      push_cast at hIH hDrop ⊢
      calc
        ((tail.recordCount : ℝ) + 1) / (2 * (L : ℝ)) ^ 14
            =
          (tail.recordCount : ℝ) / (2 * (L : ℝ)) ^ 14 +
            1 / (2 * (L : ℝ)) ^ 14 := by
              ring
        _ ≤
            criticalRealPhase (start + r) +
              (criticalRealPhase start - criticalRealPhase (start + r)) :=
          add_le_add hIH hDrop

/-- phase packing gives `recordCount <= (2L)^14`。 -/
theorem CriticalRecordChain.recordCount_le_twoMulPow14
    (R : RhinLinearForm14)
    {start remaining L : ℕ}
    (C : CriticalRecordChain start remaining)
    (hLPos : 0 < L)
    (hLengths : ∀ r : ℕ, r ∈ C.recordLengths → r ≤ L) :
    C.recordCount ≤ (2 * L) ^ 14 := by
  have hDiv := C.recordCount_div_le_phase R hLengths
  have hPhaseLt := criticalRealPhase_lt_log_two start
  have hLogLt : Real.log 2 < 1 := record_log_two_lt_one
  have hFracLt :
      (C.recordCount : ℝ) / (((2 * L : ℕ) : ℝ) ^ 14) < 1 :=
    lt_of_le_of_lt hDiv (lt_trans hPhaseLt hLogLt)
  have hDenPos : 0 < (((2 * L : ℕ) : ℝ) ^ 14) := by positivity
  have hCountReal :
      (C.recordCount : ℝ) < (((2 * L : ℕ) : ℝ) ^ 14) := by
    have := (div_lt_one hDenPos).mp hFracLt
    exact this
  have hCountNat : C.recordCount < (2 * L) ^ 14 := by
    exact_mod_cast hCountReal
  exact Nat.le_of_lt hCountNat

/-! ## 5. whole chain bound -/

/-- list sum の elementary bound。 -/
theorem list_sum_le_length_mul_of_mem_le
    (xs : List ℕ)
    (L : ℕ)
    (h : ∀ x : ℕ, x ∈ xs → x ≤ L) :
    xs.sum ≤ xs.length * L := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx : x ≤ L := h x (by simp)
      have htail : ∀ y : ℕ, y ∈ xs → y ≤ L := by
        intro y hy
        exact h y (by simp [hy])
      have hih := ih htail
      simp only [List.sum_cons, List.length_cons]
      calc
        x + xs.sum ≤ L + xs.length * L :=
          Nat.add_le_add hx hih
        _ = (xs.length + 1) * L := by ring

/-- chain 内の各 record と final fragment を一様 bound。 -/
theorem PureBProfileObstruction.recordChain_piece_bounds
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {a start remaining ell : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (C : CriticalRecordChain start remaining)
    (has : a ≤ start)
    (hend : start + remaining = P.m)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    (∀ r : ℕ, r ∈ C.recordLengths → r ≤ terminalRecordLengthBound ell) ∧
      C.finalLength ≤ terminalRecordLengthBound ell := by
  induction C with
  | @final start remaining fragment =>
      constructor
      · intro r hr
        simp [CriticalRecordChain.recordLengths] at hr
      · change remaining ≤ terminalRecordLengthBound ell
        have hEnd : start + remaining ≤ P.m := by omega
        exact
          terminalNoCarryFragment_length_le
            R P S hy has hEnd fragment hmSize
  | @step start remaining r hrPos hrLe piece tail ih =>
      have hPieceEnd : start + r ≤ P.m := by omega
      have hPiece :=
        terminalRecordPiece_length_le
          R P S hy has hPieceEnd piece hmSize
      have hTailStart : a ≤ start + r := by omega
      have hTailEnd : (start + r) + (remaining - r) = P.m := by omega
      have hTail := ih hTailStart hTailEnd
      constructor
      · intro u hu
        simp only [CriticalRecordChain.recordLengths, List.mem_cons] at hu
        rcases hu with hEq | hMem
        · subst u
          exact hPiece
        · exact hTail.1 u hMem
      · exact hTail.2

/-- final absolute coefficient。 -/
def terminalCriticalSuffixPolylogConstant : ℕ :=
  (2 ^ 14 + 1) * terminalRecordLengthConstant ^ 15

/--
chain 内の各 record と final fragment が `L` 以下なら、
全 remaining length は `(recordCount + 1) * L` 以下。
-/
theorem CriticalRecordChain.remaining_le_recordCount_succ_mul
    {start remaining L : ℕ}
    (C : CriticalRecordChain start remaining)
    (hLengths :
      ∀ r : ℕ, r ∈ C.recordLengths → r ≤ L)
    (hFinal :
      C.finalLength ≤ L) :
    remaining ≤ (C.recordCount + 1) * L := by
  have hSum :
      C.recordLengths.sum ≤
        C.recordLengths.length * L :=
    list_sum_le_length_mul_of_mem_le
      C.recordLengths L hLengths
  have hParts :
      C.recordLengths.sum + C.finalLength ≤
        C.recordLengths.length * L + L :=
    Nat.add_le_add hSum hFinal
  calc
    remaining
        = C.recordLengths.sum + C.finalLength :=
      C.recordLengths_sum_add_finalLength_eq.symm
    _ ≤ C.recordLengths.length * L + L :=
      hParts
    _ = (C.recordCount + 1) * L := by
      unfold CriticalRecordChain.recordCount
      ring

/-- pure arithmetic: `((2L)^14 + 1)L <= (2^14 + 1)L^15`。 -/
theorem twoMulPow14_add_one_mul_le_pow15
    {L : ℕ}
    (hLPos : 0 < L) :
    ((2 * L) ^ 14 + 1) * L ≤
      (2 ^ 14 + 1) * L ^ 15 := by
  have hLpow :
      L ≤ L ^ 15 := by
    have h :
        L ^ 1 ≤ L ^ 15 :=
      Nat.pow_le_pow_right hLPos (by norm_num)
    simpa using h
  have hL14mul :
      L ^ 14 * L = L ^ 15 := by
    rw [← pow_succ]
  calc
    ((2 * L) ^ 14 + 1) * L
        = (2 ^ 14 * L ^ 14 + 1) * L := by
          rw [mul_pow]
    _ = 2 ^ 14 * (L ^ 14 * L) + L := by
          ring
    _ = 2 ^ 14 * L ^ 15 + L := by
          rw [hL14mul]
    _ ≤ 2 ^ 14 * L ^ 15 + L ^ 15 :=
      Nat.add_le_add_left hLpow _
    _ = (2 ^ 14 + 1) * L ^ 15 := by
          ring

/--
record count bound `count <= (2L)^14` を
whole-chain packing bound へ変換する。
-/
theorem recordCount_succ_mul_le_pow15
    {count L : ℕ}
    (hLPos : 0 < L)
    (hCount :
      count ≤ (2 * L) ^ 14) :
    (count + 1) * L ≤
      (2 ^ 14 + 1) * L ^ 15 := by
  have hCountSucc :
      count + 1 ≤ (2 * L) ^ 14 + 1 :=
    Nat.add_le_add_right hCount 1
  have hFirst :
      (count + 1) * L ≤
        ((2 * L) ^ 14 + 1) * L :=
    Nat.mul_le_mul_right L hCountSucc
  exact
    le_trans hFirst
      (twoMulPow14_add_one_mul_le_pow15 hLPos)

/--
phase packing と各 piece の長さ上界から、
chain 全体を直接 `(2^14+1)L^15` で bound する。
-/
theorem CriticalRecordChain.remaining_le_pow15_of_record_bounds
    (R : RhinLinearForm14)
    {start remaining L : ℕ}
    (C : CriticalRecordChain start remaining)
    (hLPos : 0 < L)
    (hLengths :
      ∀ r : ℕ, r ∈ C.recordLengths → r ≤ L)
    (hFinal :
      C.finalLength ≤ L) :
    remaining ≤ (2 ^ 14 + 1) * L ^ 15 := by
  have hTotal :
      remaining ≤
        (C.recordCount + 1) * L :=
    C.remaining_le_recordCount_succ_mul
      hLengths hFinal
  have hCount :
      C.recordCount ≤ (2 * L) ^ 14 :=
    C.recordCount_le_twoMulPow14
      R hLPos hLengths
  have hPacked :
      (C.recordCount + 1) * L ≤
        (2 ^ 14 + 1) * L ^ 15 :=
    recordCount_succ_mul_le_pow15
      hLPos hCount
  exact le_trans hTotal hPacked

/--
`terminalRecordLengthBound` の 15 乗だけを展開する。

ここで
  14 * 15 = 210
を処理する。
-/
theorem terminalRecordLengthBound_pow15_expansion
    (ell : ℕ) :
    terminalRecordLengthBound ell ^ 15 =
      terminalRecordLengthConstant ^ 15 *
        (ell + 1) ^ 210 := by
  unfold terminalRecordLengthBound
  rw [mul_pow]
  have hPower :
      ((ell + 1) ^ 14) ^ 15 =
        (ell + 1) ^ 210 := by
    rw [← pow_mul]
  rw [hPower]

/-- `L^15` packing を最終 degree-210 polylog constant の形へ変換する。 -/
theorem terminalRecordLengthBound_pack_eq_polylog
    (ell : ℕ) :
    (2 ^ 14 + 1) *
        terminalRecordLengthBound ell ^ 15 =
      terminalCriticalSuffixPolylogConstant *
        (ell + 1) ^ 210 := by
  rw [terminalRecordLengthBound_pow15_expansion]
  unfold terminalCriticalSuffixPolylogConstant
  exact
    (Nat.mul_assoc
      (2 ^ 14 + 1)
      (terminalRecordLengthConstant ^ 15)
      ((ell + 1) ^ 210)).symm

/--
main pure theorem, dyadic-size form。

`m+1 <= 2^ell` なら terminal critical suffix length は degree 210。
-/
theorem PureBProfileObstruction.terminalCriticalSuffix_le_dyadicPolylog
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {a ell : ℕ}
    (S : IsTerminalCriticalSuffix P a)
    (hy : 0 ≤ P.y)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    P.m - a ≤
      terminalCriticalSuffixPolylogConstant *
        (ell + 1) ^ 210 := by
  obtain ⟨C⟩ :=
    exists_criticalRecordChain a (P.m - a)
  have ha :
      a ≤ P.m :=
    S.1
  have hEnd :
      a + (P.m - a) = P.m := by
    omega
  have hBounds :
      (∀ r : ℕ,
          r ∈ C.recordLengths →
            r ≤ terminalRecordLengthBound ell) ∧
        C.finalLength ≤ terminalRecordLengthBound ell :=
    P.recordChain_piece_bounds
      R S hy C le_rfl hEnd hmSize
  have hChain :
      P.m - a ≤
        (2 ^ 14 + 1) *
          terminalRecordLengthBound ell ^ 15 :=
    C.remaining_le_pow15_of_record_bounds
      R
      (terminalRecordLengthBound_pos ell)
      hBounds.1
      hBounds.2
  calc
    P.m - a
        ≤ (2 ^ 14 + 1) *
            terminalRecordLengthBound ell ^ 15 :=
      hChain
    _ =
        terminalCriticalSuffixPolylogConstant *
          (ell + 1) ^ 210 :=
      terminalRecordLengthBound_pack_eq_polylog ell

/-- canonical longest terminal critical suffix `t` の dyadic-size degree-210 bound。 -/
theorem PureBProfileObstruction.terminalCriticalLength_le_dyadicPolylog
    (R : RhinLinearForm14)
    (P : PureBProfileObstruction)
    {ell : ℕ}
    (hy : 0 ≤ P.y)
    (hmSize : P.m + 1 ≤ 2 ^ ell) :
    P.terminalCriticalLength ≤
      terminalCriticalSuffixPolylogConstant * (ell + 1) ^ 210 := by
  unfold PureBProfileObstruction.terminalCriticalLength
  exact
    P.terminalCriticalSuffix_le_dyadicPolylog
      R P.terminalCriticalStart_spec hy hmSize

/-- actual minimal B wrapper。 -/
theorem MinimalActualABObstructionPacket.terminalCriticalSuffix_le_dyadicPolylog
    (R : RhinLinearForm14)
    {Len : ℕ}
    (M : MinimalActualABObstructionPacket Len)
    (hLen : 2 < Len)
    {a ell : ℕ}
    (S : IsTerminalCriticalSuffix (M.toPureBProfileObstruction hLen) a)
    (hmSize : (M.toPureBProfileObstruction hLen).m + 1 ≤ 2 ^ ell) :
    (M.toPureBProfileObstruction hLen).m - a ≤
      terminalCriticalSuffixPolylogConstant * (ell + 1) ^ 210 := by
  exact
    (M.toPureBProfileObstruction hLen).terminalCriticalSuffix_le_dyadicPolylog
      R S (M.toPureBProfileObstruction_y_nonneg hLen) hmSize

/-- actual minimal B の canonical terminal critical length の dyadic-size bound。 -/
theorem MinimalActualABObstructionPacket.terminalCriticalLength_le_dyadicPolylog
    (R : RhinLinearForm14)
    {Len : ℕ}
    (M : MinimalActualABObstructionPacket Len)
    (hLen : 2 < Len)
    {ell : ℕ}
    (hmSize : (M.toPureBProfileObstruction hLen).m + 1 ≤ 2 ^ ell) :
    (M.toPureBProfileObstruction hLen).terminalCriticalLength ≤
      terminalCriticalSuffixPolylogConstant * (ell + 1) ^ 210 := by
  exact
    (M.toPureBProfileObstruction hLen).terminalCriticalLength_le_dyadicPolylog
      R (M.toPureBProfileObstruction_y_nonneg hLen) hmSize

/--
Nat logarithm form。数学的には `t = O((log m)^210)`。
`+2` は zero / finite initial rangeを一つの式に吸収するため。
-/
theorem MinimalActualABObstructionPacket.terminalCriticalSuffix_le_log210
    (R : RhinLinearForm14)
    {Len : ℕ}
    (M : MinimalActualABObstructionPacket Len)
    (hLen : 2 < Len)
    {a : ℕ}
    (S : IsTerminalCriticalSuffix (M.toPureBProfileObstruction hLen) a) :
    (M.toPureBProfileObstruction hLen).m - a ≤
      terminalCriticalSuffixPolylogConstant *
        (Nat.log 2 ((M.toPureBProfileObstruction hLen).m + 1) + 2) ^ 210 := by
  let m := (M.toPureBProfileObstruction hLen).m
  let ell := Nat.log 2 (m + 1) + 1
  have hmPos : 0 < m + 1 := by omega
  have hmLt :
      m + 1 < 2 ^ (Nat.log 2 (m + 1) + 1) := by
    simpa using
      Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (m + 1)
  have hmSize : m + 1 ≤ 2 ^ ell := by
    dsimp [ell]
    exact Nat.le_of_lt hmLt
  have hMain :=
    M.terminalCriticalSuffix_le_dyadicPolylog R hLen S
      (by simpa [m] using hmSize)
  simpa [ell, m, Nat.add_assoc] using hMain

/-- actual minimal B の canonical terminal critical length `t` を直接 bound する最終 theorem。 -/
theorem MinimalActualABObstructionPacket.terminalCriticalLength_le_log210
    (R : RhinLinearForm14)
    {Len : ℕ}
    (M : MinimalActualABObstructionPacket Len)
    (hLen : 2 < Len) :
    (M.toPureBProfileObstruction hLen).terminalCriticalLength ≤
      terminalCriticalSuffixPolylogConstant *
        (Nat.log 2 ((M.toPureBProfileObstruction hLen).m + 1) + 2) ^ 210 := by
  unfold PureBProfileObstruction.terminalCriticalLength
  exact
    M.terminalCriticalSuffix_le_log210
      R hLen (M.toPureBProfileObstruction hLen).terminalCriticalStart_spec

end ExternalArithmetic
end CSTMicro
end Collatz2
