import CollatzLean.Collatz3.Mersenne.TargetOneHoleQOneArithmetic
import CollatzLean.Collatz3.Mersenne.TargetOneHoleLocks
import CollatzLean.Collatz3.Mersenne.TargetOneHoleValuation
import Mathlib.NumberTheory.Height.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Collatz3 Mersenne: target-one `q≥2` の内部 three-log depth bound

A1 の残り B/D

* B: even, `r=1`, `q≥2`
* D: odd,  `r=2`, `q≥2`

について、従来の generic periodic-run external bound を使わず、
`baseBlock_normalForm` / `twoAdicCut_factorization` / `beattyIndex_eq` から
二本の exact three-log identity を作る。

`M = floor(log₂(3^k))`, `Q=nq`,
`U=r+n(t-q-1)` とすると `M=Q+U` であり、`G=2^n-1`, `e=2^r-1` に対して

* top:    `G·3^k + 2^Q + e = 2^(M+n)`
* bottom: `G·3^k + e = 2^Q (2^(U+n)-1)`

が exact に成り立つ。

上側は `(2,G,3)`、下側は
`(2,(2^(U+n)-1)/G,3)` の三対数一次形式として Baker--Wüstholz を適用する。
`q≥2` の valuation lock `n≤floor(log₂ k)+2` と合わせ、
`z=floor(log₂ k)` に対して三次多項式 bound を作り、`z≥101` で
その多項式が `2^z` より小さいことを離散的に示す。

結論は B/D 共通で `k < 2^101`。この解析部分では `gcd(q,t)=1` を使わない。
-/

namespace Collatz3
namespace Mersenne

open External.BakerWustholzQ

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- B/D (`q≥2`) の内部 three-log estimate で使う共通 cut。 -/
def targetOneQGeTwoInternalDepthBound : ℕ := 2 ^ 101

private def qGeTwoMainExponent (k : ℕ) : ℕ :=
  Nat.log 2 (3 ^ k)

private def qGeTwoLogDepth (k : ℕ) : ℕ :=
  Nat.log 2 k

private def qGeTwoGap (n : ℕ) : ℕ :=
  2 ^ n - 1

/-- `Q=nq`。lower block の総 bit 長。 -/
private def qGeTwoCutExponent (n q : ℕ) : ℕ :=
  n * q

/-- upper block の先頭から `3^k` の最上位 bit までの距離。 -/
private def qGeTwoUpperRun (n r q t : ℕ) : ℕ :=
  r + n * (t - q - 1)

private def qGeTwoTopError (n r q : ℕ) : ℕ :=
  2 ^ qGeTwoCutExponent n q + (2 ^ r - 1)

private def qGeTwoBottomFactor (n U : ℕ) : ℕ :=
  2 ^ (U + n) - 1

private def qGeTwoAlpha (n U : ℕ) : ℚ :=
  (qGeTwoBottomFactor n U : ℚ) / (qGeTwoGap n : ℚ)

/-! ## 基本的な指数・高さ評価 -/

private theorem qGeTwoMainExponent_le_two_mul (k : ℕ) :
    qGeTwoMainExponent k ≤ 2 * k := by
  unfold qGeTwoMainExponent
  have hPow : (3 : ℕ) ^ k ≤ 2 ^ (2 * k) := by
    calc
      (3 : ℕ) ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  calc
    Nat.log 2 (3 ^ k) ≤ Nat.log 2 (2 ^ (2 * k)) := Nat.log_mono_right hPow
    _ = 2 * k := Nat.log_pow (by norm_num) _

private theorem twoPow_qGeTwoMainExponent_le_threePow (k : ℕ) :
    2 ^ qGeTwoMainExponent k ≤ 3 ^ k := by
  unfold qGeTwoMainExponent
  exact Nat.pow_log_le_self 2 (by positivity : 3 ^ k ≠ 0)

private theorem qGeTwoGap_pos {n : ℕ} (hn : 0 < n) :
    0 < qGeTwoGap n := by
  unfold qGeTwoGap
  have hp : 1 < 2 ^ n := one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) hn.ne'
  omega

private theorem qGeTwoGap_lower {n : ℕ} (hn : 0 < n) :
    2 ^ (n - 1) ≤ qGeTwoGap n := by
  unfold qGeTwoGap
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring_nf
    simp
  rw [hpow]
  have hp : 0 < 2 ^ (n - 1) := by positivity
  omega

private theorem qGeTwoBottomFactor_pos
    {n U : ℕ} (hn : 0 < n) :
    0 < qGeTwoBottomFactor n U := by
  unfold qGeTwoBottomFactor
  have hp : 1 < 2 ^ (U + n) :=
    one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) (by omega : U + n ≠ 0)
  omega

/-- `U≥0` なので bottom factor は gap 以上。 -/
private theorem qGeTwoGap_le_bottomFactor
    {n U : ℕ} :
    qGeTwoGap n ≤ qGeTwoBottomFactor n U := by
  unfold qGeTwoGap qGeTwoBottomFactor
  have hp : 2 ^ n ≤ 2 ^ (U + n) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
  omega

private theorem qGeTwoAlpha_pos
    {n U : ℕ} (hn : 0 < n) :
    (0 : ℚ) < qGeTwoAlpha n U := by
  unfold qGeTwoAlpha
  exact div_pos
    (by exact_mod_cast qGeTwoBottomFactor_pos (U := U) hn)
    (by exact_mod_cast qGeTwoGap_pos hn)

private theorem one_le_qGeTwoAlpha
    {n U : ℕ} (hn : 0 < n) :
    (1 : ℚ) ≤ qGeTwoAlpha n U := by
  unfold qGeTwoAlpha
  rw [le_div_iff₀ (by exact_mod_cast qGeTwoGap_pos hn : (0 : ℚ) < qGeTwoGap n)]
  simpa using (show qGeTwoGap n ≤ qGeTwoBottomFactor n U from qGeTwoGap_le_bottomFactor)

private theorem qGeTwoAlpha_le_bottomFactor
    {n U : ℕ} (hn : 0 < n) :
    qGeTwoAlpha n U ≤ (qGeTwoBottomFactor n U : ℚ) := by
  unfold qGeTwoAlpha
  have hGOneNat : 1 ≤ qGeTwoGap n := by
    have hGPos := qGeTwoGap_pos hn
    omega
  have hGOne : (1 : ℚ) ≤ qGeTwoGap n := by
    exact_mod_cast hGOneNat
  exact div_le_self (by positivity) hGOne

private theorem log_two_le_seven_tenths :
    Real.log 2 ≤ (7 : ℝ) / 10 := by
  linarith [Real.log_two_lt_d9]

private theorem log_three_le_eleven_tenths :
    Real.log 3 ≤ (11 : ℝ) / 10 := by
  linarith [Real.log_three_lt_d9]

/-- `C(3,1)·log 3` の sharpened safe bound。 -/
private theorem C_three_mul_log_three_le_sharp :
    BakerWustholz.C 3 1 * Real.log 3 ≤ (2400000000000 : ℝ) := by
  have h6 : Real.log 6 ≤ (9 : ℝ) / 5 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    linarith [log_two_le_seven_tenths, log_three_le_eleven_tenths]
  have h3nonneg : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h6nonneg : (0 : ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hprod :
      Real.log 6 * Real.log 3 ≤ ((9 : ℝ) / 5) * ((11 : ℝ) / 10) :=
    mul_le_mul h6 log_three_le_eleven_tenths h3nonneg (by norm_num)
  have hC :
      BakerWustholz.C 3 1 = (1174136684544 : ℝ) * Real.log 6 := by
    norm_num [BakerWustholz.C]
  rw [hC]
  nlinarith

/-- `C(3,1)·log 2` の sharpened safe bound。 -/
private theorem C_three_mul_log_two_le_sharp :
    BakerWustholz.C 3 1 * Real.log 2 ≤ (1500000000000 : ℝ) := by
  have h6 : Real.log 6 ≤ (9 : ℝ) / 5 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    linarith [log_two_le_seven_tenths, log_three_le_eleven_tenths]
  have h2nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h6nonneg : (0 : ℝ) ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  have hprod :
      Real.log 6 * Real.log 2 ≤ ((9 : ℝ) / 5) * ((7 : ℝ) / 10) :=
    mul_le_mul h6 log_two_le_seven_tenths h2nonneg (by norm_num)
  have hC :
      BakerWustholz.C 3 1 = (1174136684544 : ℝ) * Real.log 6 := by
    norm_num [BakerWustholz.C]
  rw [hC]
  nlinarith

/-! ## exact top / bottom identities -/

private theorem qGeTwo_exponent_split
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn : 0 < n)
    (hr : 0 < r)
    (hqt : h.q < h.t) :
    qGeTwoMainExponent k =
      qGeTwoCutExponent n h.q + qGeTwoUpperRun n r h.q h.t := by
  have hBeatty := h.beattyIndex_eq hn hr hqt
  rw [beattyIndex_eq_natLog_threePow] at hBeatty
  have hSplitMul :
      n * (h.t - 1) =
        n * h.q + n * (h.t - h.q - 1) := by
    have ht1 : h.t - 1 = h.q + (h.t - h.q - 1) := by
      omega
    rw [ht1, Nat.mul_add]
  dsimp [qGeTwoMainExponent, qGeTwoCutExponent, qGeTwoUpperRun]
  omega

/-- lower block cut そのものを three-log 用の factorization に書き直す。 -/
private theorem qGeTwo_bottom_identity
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hqt : h.q < h.t) :
    qGeTwoGap n * 3 ^ k + (2 ^ r - 1) =
      2 ^ qGeTwoCutExponent n h.q *
        qGeTwoBottomFactor n (qGeTwoUpperRun n r h.q h.t) := by
  have hFact := h.twoAdicCut_factorization hqt
  have hExp :
      r + n * (h.t - h.q) =
        (r + n * (h.t - h.q - 1)) + n := by
    have hdPos : 0 < h.t - h.q := Nat.sub_pos_of_lt hqt
    have hdOne : 1 ≤ h.t - h.q := by omega
    have htq :
        h.t - h.q = (h.t - h.q - 1) + 1 := by
      omega
    calc
      r + n * (h.t - h.q)
          = r + n * ((h.t - h.q - 1) + 1) := by
              rw [htq]
              simp
      _ = r + (n * (h.t - h.q - 1) + n) := by
              simp [Nat.mul_add]
      _ = (r + n * (h.t - h.q - 1)) + n := by
              omega
  have hTail :
      2 ^ r * (2 ^ n) ^ (h.t - h.q) =
        2 ^ ((r + n * (h.t - h.q - 1)) + n) := by
    rw [← pow_mul, ← pow_add, hExp]
  unfold qGeTwoGap qGeTwoCutExponent qGeTwoBottomFactor qGeTwoUpperRun
  calc
    (2 ^ n - 1) * 3 ^ k + (2 ^ r - 1)
        = (2 ^ n) ^ h.q *
            (2 ^ r * (2 ^ n) ^ (h.t - h.q) - 1) := hFact
    _ = 2 ^ (n * h.q) *
          (2 ^ r * (2 ^ n) ^ (h.t - h.q) - 1) := by
            rw [← pow_mul]
    _ = 2 ^ (n * h.q) *
          (2 ^ ((r + n * (h.t - h.q - 1)) + n) - 1) := by
            rw [hTail]

/-- top identity。`Q=nq` の lower block を error として右端へ移す。 -/
private theorem qGeTwo_top_identity
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn : 0 < n)
    (hr : 0 < r)
    (hqt : h.q < h.t) :
    qGeTwoGap n * 3 ^ k + qGeTwoTopError n r h.q =
      2 ^ (qGeTwoMainExponent k + n) := by
  have hBottom := qGeTwo_bottom_identity h hqt
  have hSplit := qGeTwo_exponent_split h hn hr hqt
  let Q := qGeTwoCutExponent n h.q
  let U := qGeTwoUpperRun n r h.q h.t
  have hFactorSucc : qGeTwoBottomFactor n U + 1 = 2 ^ (U + n) := by
    unfold qGeTwoBottomFactor
    have hp : 0 < (2 : ℕ) ^ (U + n) := by positivity
    omega
  have hPow : 2 ^ Q * 2 ^ (U + n) = 2 ^ (qGeTwoMainExponent k + n) := by
    rw [← pow_add]
    congr 1
    dsimp [Q, U] at hSplit ⊢
    omega
  dsimp [qGeTwoTopError, Q, U]
  calc
    qGeTwoGap n * 3 ^ k +
        (2 ^ qGeTwoCutExponent n h.q + (2 ^ r - 1))
        = (qGeTwoGap n * 3 ^ k + (2 ^ r - 1)) +
            2 ^ qGeTwoCutExponent n h.q := by ring
    _ = 2 ^ qGeTwoCutExponent n h.q *
          qGeTwoBottomFactor n (qGeTwoUpperRun n r h.q h.t) +
            2 ^ qGeTwoCutExponent n h.q := by rw [hBottom]
    _ = 2 ^ qGeTwoCutExponent n h.q *
          (qGeTwoBottomFactor n (qGeTwoUpperRun n r h.q h.t) + 1) := by ring
    _ = 2 ^ qGeTwoCutExponent n h.q *
          2 ^ (qGeTwoUpperRun n r h.q h.t + n) := by
            rw [hFactorSucc]
    _ = 2 ^ (qGeTwoMainExponent k + n) := hPow

/-! ## top three-log -/

private noncomputable def qGeTwoTopLinearForm (k n : ℕ) : ℝ :=
  ((qGeTwoMainExponent k + n : ℕ) : ℝ) * Real.log 2 -
    Real.log (qGeTwoGap n : ℝ) - (k : ℝ) * Real.log 3

private def qGeTwoTopAlpha (n : ℕ) : Fin 3 → ℚ :=
  ![2, (((qGeTwoGap n : ℕ) : ℤ) : ℚ), 3]

private def qGeTwoTopCoeff (k n : ℕ) : Fin 3 → ℤ :=
  ![((qGeTwoMainExponent k + n : ℕ) : ℤ), -1, -((k : ℕ) : ℤ)]

private theorem qGeTwoTopLinearForm_eq_log_one_add_ratio
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn : 0 < n)
    (hr : 0 < r)
    (hqt : h.q < h.t) :
    qGeTwoTopLinearForm k n =
      Real.log
        (1 + (qGeTwoTopError n r h.q : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k)) := by
  have hIdentity := qGeTwo_top_identity h hn hr hqt
  have hGPos : 0 < qGeTwoGap n := qGeTwoGap_pos hn
  have hDenPos : (0 : ℝ) < (qGeTwoGap n : ℝ) * (3 : ℝ) ^ k := by positivity
  have hIdentityR :
      (qGeTwoGap n : ℝ) * (3 : ℝ) ^ k + (qGeTwoTopError n r h.q : ℝ) =
        (2 : ℝ) ^ (qGeTwoMainExponent k + n) := by
    exact_mod_cast hIdentity
  have hRatio :
      qGeTwoTopLinearForm k n =
        Real.log
          ((2 : ℝ) ^ (qGeTwoMainExponent k + n) /
            ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k)) := by
    unfold qGeTwoTopLinearForm
    rw [Real.log_div (by positivity) hDenPos.ne', Real.log_pow,
      Real.log_mul (by exact_mod_cast hGPos.ne') (by positivity), Real.log_pow]
    ring
  have hRatioEq :
      (2 : ℝ) ^ (qGeTwoMainExponent k + n) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) =
        1 + (qGeTwoTopError n r h.q : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := by
    rw [← hIdentityR]
    field_simp [hDenPos.ne']
  rw [hRatio, hRatioEq]

private theorem qGeTwoTopLinearForm_pos
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn : 0 < n)
    (hr : 0 < r)
    (hqt : h.q < h.t) :
    0 < qGeTwoTopLinearForm k n := by
  rw [qGeTwoTopLinearForm_eq_log_one_add_ratio h hn hr hqt]
  have hDenPos : (0 : ℝ) < (qGeTwoGap n : ℝ) * (3 : ℝ) ^ k := by
    have hGPos := qGeTwoGap_pos hn
    positivity
  have hEPos : (0 : ℝ) < (qGeTwoTopError n r h.q : ℝ) := by
    unfold qGeTwoTopError
    positivity
  have hFracPos :
      0 < (qGeTwoTopError n r h.q : ℝ) /
        ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := div_pos hEPos hDenPos
  exact Real.log_pos (by linarith)

private theorem qGeTwoTopError_le_two_mul_cut
    {n r q : ℕ}
    (hn3 : 3 ≤ n)
    (hqTwo : 2 ≤ q)
    (hr12 : r = 1 ∨ r = 2) :
    qGeTwoTopError n r q ≤ 2 * 2 ^ qGeTwoCutExponent n q := by
  have hQ6 : 6 ≤ qGeTwoCutExponent n q := by
    unfold qGeTwoCutExponent
    have hmul := Nat.mul_le_mul hn3 hqTwo
    norm_num at hmul ⊢
    exact hmul
  have hThreeLe : 3 ≤ 2 ^ qGeTwoCutExponent n q := by
    have h64 : 64 ≤ 2 ^ qGeTwoCutExponent n q := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hQ6
      norm_num at this ⊢
      exact this
    omega
  have he : 2 ^ r - 1 ≤ 3 := by
    rcases hr12 with rfl | rfl <;> norm_num
  unfold qGeTwoTopError
  omega

private theorem qGeTwoTop_error_ratio_le_four_div_twoPow
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn3 : 3 ≤ n)
    (hr12 : r = 1 ∨ r = 2)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q) :
    (qGeTwoTopError n r h.q : ℝ) /
        ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) ≤
      4 / (2 : ℝ) ^ (qGeTwoUpperRun n r h.q h.t + n) := by
  have hn : 0 < n := by omega
  have hr : 0 < r := by rcases hr12 with rfl | rfl <;> norm_num
  have hE := qGeTwoTopError_le_two_mul_cut hn3 hqTwo hr12
  have hG := qGeTwoGap_lower hn
  have hM := twoPow_qGeTwoMainExponent_le_threePow k
  have hSplit := qGeTwo_exponent_split h hn hr hqt
  let Q := qGeTwoCutExponent n h.q
  let U := qGeTwoUpperRun n r h.q h.t
  have hEReal :
      (qGeTwoTopError n r h.q : ℝ) ≤ 2 * (2 : ℝ) ^ Q := by
    exact_mod_cast hE
  have hGReal :
      (2 : ℝ) ^ (n - 1) ≤ (qGeTwoGap n : ℝ) := by
    exact_mod_cast hG
  have hMReal :
      (2 : ℝ) ^ (Q + U) ≤ (3 : ℝ) ^ k := by
    have hEq : qGeTwoMainExponent k = Q + U := by simpa [Q, U] using hSplit
    rw [← hEq]
    exact_mod_cast hM
  have hDen :
      (2 : ℝ) ^ (n - 1) * (2 : ℝ) ^ (Q + U) ≤
        (qGeTwoGap n : ℝ) * (3 : ℝ) ^ k := by
    exact mul_le_mul hGReal hMReal (by positivity) (by positivity)
  calc
    (qGeTwoTopError n r h.q : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k)
        ≤ (2 * (2 : ℝ) ^ Q) /
            ((2 : ℝ) ^ (n - 1) * (2 : ℝ) ^ (Q + U)) := by
          exact div_le_div₀ (by positivity) hEReal (by positivity) hDen
    _ = 4 / (2 : ℝ) ^ (U + n) := by
          have hnPow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
            rw [show n = (n - 1) + 1 by omega, pow_succ]
            ring_nf
            simp
          simp only [pow_add]
          rw [hnPow]
          field_simp
          ring
    _ = 4 / (2 : ℝ) ^ (qGeTwoUpperRun n r h.q h.t + n) := rfl

private theorem qGeTwoTopLinearForm_log_upper
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn3 : 3 ≤ n)
    (hr12 : r = 1 ∨ r = 2)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q) :
    Real.log (qGeTwoTopLinearForm k n) ≤
      (2 - ((qGeTwoUpperRun n r h.q h.t + n : ℕ) : ℝ)) * Real.log 2 := by
  have hn : 0 < n := by omega
  have hr : 0 < r := by rcases hr12 with rfl | rfl <;> norm_num
  have hΛPos := qGeTwoTopLinearForm_pos h hn hr hqt
  have hEq := qGeTwoTopLinearForm_eq_log_one_add_ratio h hn hr hqt
  have hDenPos : (0 : ℝ) < (qGeTwoGap n : ℝ) * (3 : ℝ) ^ k := by
    have hGPos := qGeTwoGap_pos hn
    positivity
  have hEPos : (0 : ℝ) < (qGeTwoTopError n r h.q : ℝ) := by
    unfold qGeTwoTopError
    positivity
  have hLogLe :
      qGeTwoTopLinearForm k n ≤
        (qGeTwoTopError n r h.q : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := by
    rw [hEq]
    simpa using Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 1 + (qGeTwoTopError n r h.q : ℝ) /
        ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) by
          have := div_pos hEPos hDenPos
          linarith)
  have hRatio := qGeTwoTop_error_ratio_le_four_div_twoPow h hn3 hr12 hqt hqTwo
  have hΛUpper := le_trans hLogLe hRatio
  calc
    Real.log (qGeTwoTopLinearForm k n)
        ≤ Real.log (4 / (2 : ℝ) ^ (qGeTwoUpperRun n r h.q h.t + n)) :=
      Real.log_le_log hΛPos hΛUpper
    _ = (2 - ((qGeTwoUpperRun n r h.q h.t + n : ℕ) : ℝ)) * Real.log 2 := by
      rw [Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by positivity),
        show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Real.log_pow]
      ring

private theorem qGeTwoTopAlpha_pos
    {n : ℕ} (hn3 : 3 ≤ n) :
    ∀ i, 0 < qGeTwoTopAlpha n i := by
  intro i
  fin_cases i
  · norm_num [qGeTwoTopAlpha]
  · dsimp [qGeTwoTopAlpha]
    exact_mod_cast qGeTwoGap_pos (by omega : 0 < n)
  · norm_num [qGeTwoTopAlpha]

private theorem qGeTwoTopCoeff_natAbs_le
    {k n : ℕ}
    (hk4 : 4 ≤ k)
    (hnLog : n ≤ qGeTwoLogDepth k + 2) :
    ∀ i, (qGeTwoTopCoeff k n i).natAbs ≤ 4 * k := by
  have hM := qGeTwoMainExponent_le_two_mul k
  have hz : qGeTwoLogDepth k ≤ k := by
    unfold qGeTwoLogDepth
    exact Nat.log_le_self 2 k
  have hnK : n ≤ k + 2 := by omega
  have hMn : qGeTwoMainExponent k + n ≤ 4 * k := by omega
  intro i
  fin_cases i
  · change qGeTwoMainExponent k + n ≤ 4 * k
    exact hMn
  · simp [qGeTwoTopCoeff]
    omega
  · simp [qGeTwoTopCoeff]
    omega

private theorem qGeTwoTopLinearForm_eq_sum
    (k n : ℕ) :
    qGeTwoTopLinearForm k n =
      ∑ i, (qGeTwoTopCoeff k n i : ℝ) * Real.log (qGeTwoTopAlpha n i : ℝ) := by
  rw [Fin.sum_univ_three]
  dsimp [qGeTwoTopAlpha, qGeTwoTopCoeff, qGeTwoTopLinearForm, qGeTwoGap]
  push_cast
  ring

private theorem qGeTwoGap_modifiedHeight_le
    {n : ℕ} (hn3 : 3 ≤ n) :
    BakerWustholz.modifiedHeight (Rat.castHom ℂ)
        (((qGeTwoGap n : ℕ) : ℤ) : ℚ) ≤
      (n : ℝ) * Real.log 2 := by
  have hGPos : 0 < qGeTwoGap n := qGeTwoGap_pos (by omega)
  have hGOne : 1 ≤ qGeTwoGap n := by omega
  have hGLe : qGeTwoGap n ≤ 2 ^ n := by
    unfold qGeTwoGap
    exact Nat.sub_le _ _
  have hLogG : Real.log (qGeTwoGap n : ℝ) ≤ (n : ℝ) * Real.log 2 := by
    calc
      Real.log (qGeTwoGap n : ℝ) ≤ Real.log ((2 : ℝ) ^ n) :=
        Real.log_le_log (by exact_mod_cast hGPos) (by exact_mod_cast hGLe)
      _ = (n : ℝ) * Real.log 2 := by rw [Real.log_pow]
  have hOneLe : (1 : ℝ) ≤ (n : ℝ) * Real.log 2 := by
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    nlinarith [Real.log_two_gt_d9]
  have hBase := mh_intCast (u := (qGeTwoGap n : ℤ)) (by exact_mod_cast hGOne)
  exact le_trans hBase (max_le hLogG hOneLe)

private theorem qGeTwoTopHeightProduct_le
    {n : ℕ} (hn3 : 3 ≤ n) :
    (∏ i, BakerWustholz.modifiedHeight (Rat.castHom ℂ) (qGeTwoTopAlpha n i)) ≤
      (n : ℝ) * Real.log 2 * Real.log 3 := by
  rw [Fin.prod_univ_three]
  dsimp [qGeTwoTopAlpha]
  have hG := qGeTwoGap_modifiedHeight_le hn3
  have h12 := mul_le_mul mh_two hG (modifiedHeight_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h3nonneg := modifiedHeight_nonneg (3 : ℚ)
  have hRightNonneg : 0 ≤ (1 : ℝ) * ((n : ℝ) * Real.log 2) := by positivity
  have h := mul_le_mul h12 mh_three h3nonneg hRightNonneg
  simpa [mul_assoc] using h

/--
上側 exact identity に対する Baker--Wüstholz 下界。

外部定理へ渡す基数は
`(2, 2^n - 1, 3)`、係数は `(M+n, -1, -k)`。
-/
private theorem qGeTwoTopBW_log_lower
    {k n : ℕ}
    (hk4 : 4 ≤ k)
    (hn3 : 3 ≤ n)
    (hnLog : n ≤ qGeTwoLogDepth k + 2)
    (hΛPos : 0 < qGeTwoTopLinearForm k n) :
    -(BakerWustholz.C 3 1 * max (Real.log (4 * k)) 1 *
        ((n : ℝ) * Real.log 2 * Real.log 3)) ≤
      Real.log (qGeTwoTopLinearForm k n) := by
  have hAlphaPos :
      (0 : ℚ) < (((qGeTwoGap n : ℕ) : ℤ) : ℚ) := by
    exact_mod_cast qGeTwoGap_pos (by omega : 0 < n)
  have hz :
      qGeTwoLogDepth k ≤ k := by
    unfold qGeTwoLogDepth
    exact Nat.log_le_self 2 k
  have hnK : n ≤ k + 2 := by
    omega
  have haB :
      qGeTwoMainExponent k + n ≤ 4 * k := by
    have hM := qGeTwoMainExponent_le_two_mul k
    omega
  have hkB : k ≤ 4 * k := by
    omega
  have hForm :
      qGeTwoTopLinearForm k n =
        BakerWustholz.threeLogRatForm
          (qGeTwoMainExponent k + n) k (-1)
          (((qGeTwoGap n : ℕ) : ℤ) : ℚ) := by
    unfold qGeTwoTopLinearForm BakerWustholz.threeLogRatForm
    norm_num
    ring
  have hBW :=
    log_threeForm_rat_ge
      (a := qGeTwoMainExponent k + n)
      (k := k)
      (B := 4 * k)
      (α := (((qGeTwoGap n : ℕ) : ℤ) : ℚ))
      hAlphaPos
      (ε := -1)
      (Or.inr rfl)
      (by omega)
      haB
      hkB
      hForm
      hΛPos
  have hProd := qGeTwoTopHeightProduct_le hn3
  rw [Fin.prod_univ_three] at hProd
  dsimp [qGeTwoTopAlpha] at hProd
  have hScaleNonneg :
      0 ≤ BakerWustholz.C 3 1 * max (Real.log (4 * k)) 1 :=
    mul_nonneg
      (C_one_nonneg 3)
      (le_trans zero_le_one (le_max_right _ _))
  have hMul :=
    mul_le_mul_of_nonneg_left hProd hScaleNonneg
  have hNeg := neg_le_neg hMul
  exact le_trans (by simpa [mul_assoc] using hNeg) hBW

/-- top 3-log から upper run `U` の実数 bound を得る。 -/
private theorem qGeTwoUpperRun_real_bound
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hk4 : 4 ≤ k)
    (hn3 : 3 ≤ n)
    (hr12 : r = 1 ∨ r = 2)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hnLog : n ≤ qGeTwoLogDepth k + 2) :
    ((qGeTwoUpperRun n r h.q h.t + n : ℕ) : ℝ) - 2 ≤
      BakerWustholz.C 3 1 * Real.log 3 *
        max (Real.log (4 * k)) 1 * (n : ℝ) := by
  have hr : 0 < r := by rcases hr12 with rfl | rfl <;> norm_num
  have hΛPos := qGeTwoTopLinearForm_pos h (by omega) hr hqt
  have hLow := qGeTwoTopBW_log_lower hk4 hn3 hnLog hΛPos
  have hUp := qGeTwoTopLinearForm_log_upper h hn3 hr12 hqt hqTwo
  have hCombined := le_trans hLow hUp
  have h2pos := log_two_pos
  have hFactored :
      ((((qGeTwoUpperRun n r h.q h.t + n : ℕ) : ℝ) - 2) * Real.log 2) ≤
        (BakerWustholz.C 3 1 * Real.log 3 *
          max (Real.log (4 * k)) 1 * (n : ℝ)) * Real.log 2 := by
    nlinarith
  nlinarith

/-! ## bottom three-log -/

private noncomputable def qGeTwoBottomLinearForm
    (k n q U : ℕ) : ℝ :=
  (qGeTwoCutExponent n q : ℝ) * Real.log 2 +
    Real.log (qGeTwoAlpha n U : ℝ) -
    (k : ℝ) * Real.log 3

private def qGeTwoBottomAlpha (n U : ℕ) : Fin 3 → ℚ :=
  ![2, qGeTwoAlpha n U, 3]

private def qGeTwoBottomCoeff (k n q : ℕ) : Fin 3 → ℤ :=
  ![((qGeTwoCutExponent n q : ℕ) : ℤ), 1, -((k : ℕ) : ℤ)]

private theorem qGeTwoBottomLinearForm_eq_log_one_add_ratio
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn : 0 < n)
    (hqt : h.q < h.t) :
    qGeTwoBottomLinearForm k n h.q (qGeTwoUpperRun n r h.q h.t) =
      Real.log
        (1 + ((2 ^ r - 1 : ℕ) : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k)) := by
  let U := qGeTwoUpperRun n r h.q h.t
  have hIdentity := qGeTwo_bottom_identity h hqt
  have hGPos : 0 < qGeTwoGap n := qGeTwoGap_pos hn
  have hFPos : 0 < qGeTwoBottomFactor n U := qGeTwoBottomFactor_pos hn
  have hAlphaPosQ : (0 : ℚ) < qGeTwoAlpha n U := qGeTwoAlpha_pos hn
  have hAlphaPosR : (0 : ℝ) < (qGeTwoAlpha n U : ℝ) := by exact_mod_cast hAlphaPosQ
  have hDenPos : (0 : ℝ) < (qGeTwoGap n : ℝ) * (3 : ℝ) ^ k := by positivity
  have hIdentityR :
      (qGeTwoGap n : ℝ) * (3 : ℝ) ^ k + ((2 ^ r - 1 : ℕ) : ℝ) =
        (2 : ℝ) ^ qGeTwoCutExponent n h.q * (qGeTwoBottomFactor n U : ℝ) := by
    exact_mod_cast hIdentity
  have hRatio :
      qGeTwoBottomLinearForm k n h.q U =
        Real.log
          (((2 : ℝ) ^ qGeTwoCutExponent n h.q * (qGeTwoAlpha n U : ℝ)) /
            (3 : ℝ) ^ k) := by
    unfold qGeTwoBottomLinearForm
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_mul (by positivity) hAlphaPosR.ne', Real.log_pow, Real.log_pow]
  have hAlphaCast :
      (qGeTwoAlpha n U : ℝ) =
        (qGeTwoBottomFactor n U : ℝ) / (qGeTwoGap n : ℝ) := by
    norm_num [qGeTwoAlpha]
  have hRatioEq :
      ((2 : ℝ) ^ qGeTwoCutExponent n h.q * (qGeTwoAlpha n U : ℝ)) /
          (3 : ℝ) ^ k =
        1 + ((2 ^ r - 1 : ℕ) : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := by
    rw [hAlphaCast]
    have hGNe : (qGeTwoGap n : ℝ) ≠ 0 := by positivity
    have hThreeNe : (3 : ℝ) ^ k ≠ 0 := by positivity
    calc
      ((2 : ℝ) ^ qGeTwoCutExponent n h.q *
            ((qGeTwoBottomFactor n U : ℝ) / (qGeTwoGap n : ℝ))) /
          (3 : ℝ) ^ k
          =
        ((2 : ℝ) ^ qGeTwoCutExponent n h.q *
            (qGeTwoBottomFactor n U : ℝ)) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := by
            field_simp [hGNe, hThreeNe]
      _ =
        ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k + ((2 ^ r - 1 : ℕ) : ℝ)) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := by
            rw [← hIdentityR]
      _ =
        1 + ((2 ^ r - 1 : ℕ) : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := by
            field_simp [hDenPos.ne']
  rw [hRatio, hRatioEq]

private theorem qGeTwoBottomLinearForm_pos
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn : 0 < n)
    (hr : 0 < r)
    (hqt : h.q < h.t) :
    0 < qGeTwoBottomLinearForm k n h.q (qGeTwoUpperRun n r h.q h.t) := by
  rw [qGeTwoBottomLinearForm_eq_log_one_add_ratio h hn hqt]
  have he : 0 < 2 ^ r - 1 := by
    have hp : 1 < 2 ^ r := one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) hr.ne'
    omega
  have hDen : (0 : ℝ) < (qGeTwoGap n : ℝ) * (3 : ℝ) ^ k := by
    have hG := qGeTwoGap_pos hn
    positivity
  have hFrac :
      (0 : ℝ) < ((2 ^ r - 1 : ℕ) : ℝ) /
        ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := by
    exact div_pos (by exact_mod_cast he) hDen
  exact Real.log_pos (by linarith)

private theorem qGeTwoBottom_error_ratio_le_three_div_threePow
    {k n r : ℕ}
    (hn : 0 < n)
    (hr12 : r = 1 ∨ r = 2) :
    ((2 ^ r - 1 : ℕ) : ℝ) /
        ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) ≤
      3 / (3 : ℝ) ^ k := by
  have hGOneNat : 1 ≤ qGeTwoGap n := by
    have hGPos := qGeTwoGap_pos hn
    omega
  have hGOne : (1 : ℝ) ≤ (qGeTwoGap n : ℝ) := by
    exact_mod_cast hGOneNat
  have he : ((2 ^ r - 1 : ℕ) : ℝ) ≤ 3 := by
    rcases hr12 with rfl | rfl <;> norm_num
  have hDen : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  calc
    ((2 ^ r - 1 : ℕ) : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k)
        ≤ 3 / ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := by
          exact div_le_div_of_nonneg_right he (by positivity)
    _ ≤ 3 / (3 : ℝ) ^ k := by
          have hDenLe : (3 : ℝ) ^ k ≤ (qGeTwoGap n : ℝ) * (3 : ℝ) ^ k := by
            nlinarith [mul_le_mul_of_nonneg_right hGOne
              (show 0 ≤ (3 : ℝ) ^ k by positivity)]
          exact div_le_div₀ (by norm_num) le_rfl hDen hDenLe

private theorem qGeTwoBottomLinearForm_log_upper
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn3 : 3 ≤ n)
    (hr12 : r = 1 ∨ r = 2)
    (hqt : h.q < h.t) :
    Real.log (qGeTwoBottomLinearForm k n h.q (qGeTwoUpperRun n r h.q h.t)) ≤
      (1 - (k : ℝ)) * Real.log 3 := by
  have hn : 0 < n := by omega
  have hr : 0 < r := by rcases hr12 with rfl | rfl <;> norm_num
  have hΛPos := qGeTwoBottomLinearForm_pos h hn hr hqt
  have hEq := qGeTwoBottomLinearForm_eq_log_one_add_ratio h hn hqt
  have he : 0 < 2 ^ r - 1 := by
    have hp : 1 < 2 ^ r := one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) hr.ne'
    omega
  have hDenPos : (0 : ℝ) < (qGeTwoGap n : ℝ) * (3 : ℝ) ^ k := by
    have hG := qGeTwoGap_pos hn
    positivity
  have hLogLe :
      qGeTwoBottomLinearForm k n h.q (qGeTwoUpperRun n r h.q h.t) ≤
        ((2 ^ r - 1 : ℕ) : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := by
    rw [hEq]
    have heR : (0 : ℝ) < ((2 ^ r - 1 : ℕ) : ℝ) := by
      exact_mod_cast he
    have hFrac :
        (0 : ℝ) < ((2 ^ r - 1 : ℕ) : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) :=
      div_pos heR hDenPos
    have hArgPos :
        (0 : ℝ) < 1 + ((2 ^ r - 1 : ℕ) : ℝ) /
          ((qGeTwoGap n : ℝ) * (3 : ℝ) ^ k) := by
      linarith
    simpa using Real.log_le_sub_one_of_pos hArgPos
  have hRatio := qGeTwoBottom_error_ratio_le_three_div_threePow (k := k) hn hr12
  have hΛUpper := le_trans hLogLe hRatio
  calc
    Real.log (qGeTwoBottomLinearForm k n h.q (qGeTwoUpperRun n r h.q h.t))
        ≤ Real.log (3 / (3 : ℝ) ^ k) := Real.log_le_log hΛPos hΛUpper
    _ = (1 - (k : ℝ)) * Real.log 3 := by
      rw [Real.log_div (by norm_num : (3 : ℝ) ≠ 0) (by positivity), Real.log_pow]
      ring

private theorem qGeTwoAlpha_logHeight_le
    {n U : ℕ}
    (hn3 : 3 ≤ n) :
    Height.logHeight₁ (qGeTwoAlpha n U) ≤
      ((U + 2 * n : ℕ) : ℝ) * Real.log 2 := by
  have hn : 0 < n := by omega
  have hFPos : 0 < qGeTwoBottomFactor n U := qGeTwoBottomFactor_pos hn
  have hGPos : 0 < qGeTwoGap n := qGeTwoGap_pos hn
  let : NeZero (qGeTwoBottomFactor n U) := ⟨hFPos.ne'⟩
  let : NeZero (qGeTwoGap n) := ⟨hGPos.ne'⟩
  have hMul := Height.logHeight₁_mul_le
    ((qGeTwoBottomFactor n U : ℚ)) ((qGeTwoGap n : ℚ)⁻¹)
  have hFLe : Real.log (qGeTwoBottomFactor n U : ℝ) ≤ ((U + n : ℕ) : ℝ) * Real.log 2 := by
    have hFLt : qGeTwoBottomFactor n U < 2 ^ (U + n) := by
      unfold qGeTwoBottomFactor
      have hp : 0 < (2 : ℕ) ^ (U + n) := by positivity
      omega
    calc
      Real.log (qGeTwoBottomFactor n U : ℝ) ≤ Real.log ((2 : ℝ) ^ (U + n)) :=
        Real.log_le_log (by exact_mod_cast hFPos) (by exact_mod_cast (Nat.le_of_lt hFLt))
      _ = ((U + n : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
  have hGLe : Real.log (qGeTwoGap n : ℝ) ≤ (n : ℝ) * Real.log 2 := by
    have hGN : qGeTwoGap n ≤ 2 ^ n := by
      unfold qGeTwoGap
      exact Nat.sub_le _ _
    calc
      Real.log (qGeTwoGap n : ℝ) ≤ Real.log ((2 : ℝ) ^ n) :=
        Real.log_le_log (by exact_mod_cast hGPos) (by exact_mod_cast hGN)
      _ = (n : ℝ) * Real.log 2 := by rw [Real.log_pow]
  rw [show qGeTwoAlpha n U = (qGeTwoBottomFactor n U : ℚ) * (qGeTwoGap n : ℚ)⁻¹ by
    simp [qGeTwoAlpha, div_eq_mul_inv]]
  calc
    Height.logHeight₁ ((qGeTwoBottomFactor n U : ℚ) * (qGeTwoGap n : ℚ)⁻¹)
        ≤ Height.logHeight₁ (qGeTwoBottomFactor n U : ℚ) +
            Height.logHeight₁ ((qGeTwoGap n : ℚ)⁻¹) := hMul
    _ = Real.log (qGeTwoBottomFactor n U : ℝ) +
          Real.log (qGeTwoGap n : ℝ) := by
          rw [Height.logHeight₁_inv, Rat.logHeight₁_natCast, Rat.logHeight₁_natCast]
    _ ≤ ((U + n : ℕ) : ℝ) * Real.log 2 + (n : ℝ) * Real.log 2 :=
      add_le_add hFLe hGLe
    _ = ((U + 2 * n : ℕ) : ℝ) * Real.log 2 := by
      push_cast
      ring

private theorem qGeTwoAlpha_realLog_le
    {n U : ℕ}
    (hn3 : 3 ≤ n) :
    Real.log (qGeTwoAlpha n U : ℝ) ≤
      ((U + 2 * n : ℕ) : ℝ) * Real.log 2 := by
  have hn : 0 < n := by omega
  have hAlphaPosQ := qGeTwoAlpha_pos (U := U) hn
  have hAlphaOneQ := one_le_qGeTwoAlpha (U := U) hn
  have hAlphaLeFQ := qGeTwoAlpha_le_bottomFactor (U := U) hn
  have hAlphaPosR : (0 : ℝ) < (qGeTwoAlpha n U : ℝ) := by exact_mod_cast hAlphaPosQ
  have hAlphaLeFR : (qGeTwoAlpha n U : ℝ) ≤ (qGeTwoBottomFactor n U : ℝ) := by
    exact_mod_cast hAlphaLeFQ
  have hFPos : 0 < qGeTwoBottomFactor n U := qGeTwoBottomFactor_pos hn
  have hLogF : Real.log (qGeTwoBottomFactor n U : ℝ) ≤ ((U + n : ℕ) : ℝ) * Real.log 2 := by
    have hFLt : qGeTwoBottomFactor n U < 2 ^ (U + n) := by
      unfold qGeTwoBottomFactor
      have hp : 0 < (2 : ℕ) ^ (U + n) := by positivity
      omega
    calc
      Real.log (qGeTwoBottomFactor n U : ℝ) ≤ Real.log ((2 : ℝ) ^ (U + n)) :=
        Real.log_le_log (by exact_mod_cast hFPos) (by exact_mod_cast (Nat.le_of_lt hFLt))
      _ = ((U + n : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
  have hLogAlphaF :
      Real.log (qGeTwoAlpha n U : ℝ) ≤ Real.log (qGeTwoBottomFactor n U : ℝ) :=
    Real.log_le_log hAlphaPosR hAlphaLeFR
  have hnNonneg : 0 ≤ (n : ℝ) * Real.log 2 := by positivity
  calc
    Real.log (qGeTwoAlpha n U : ℝ) ≤ ((U + n : ℕ) : ℝ) * Real.log 2 :=
      le_trans hLogAlphaF hLogF
    _ ≤ ((U + 2 * n : ℕ) : ℝ) * Real.log 2 := by
      push_cast
      nlinarith

private theorem qGeTwoAlpha_modifiedHeight_le
    {n U : ℕ}
    (hn3 : 3 ≤ n) :
    BakerWustholz.modifiedHeight (Rat.castHom ℂ) (qGeTwoAlpha n U) ≤
      ((U + 2 * n : ℕ) : ℝ) * Real.log 2 := by
  have hn : 0 < n := by omega
  rw [modifiedHeight_rat, norm_log_ratCast (qGeTwoAlpha_pos (U := U) hn)]
  have hLogNonneg : 0 ≤ Real.log (qGeTwoAlpha n U : ℝ) :=
    Real.log_nonneg (by exact_mod_cast one_le_qGeTwoAlpha (U := U) hn)
  rw [abs_of_nonneg hLogNonneg]
  apply max_le
  · exact qGeTwoAlpha_logHeight_le hn3
  · apply max_le
    · exact qGeTwoAlpha_realLog_le hn3
    · have hOneN : (1 : ℝ) ≤ (n : ℝ) * Real.log 2 := by
        have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
        nlinarith [Real.log_two_gt_d9]
      have hnLe : n ≤ U + 2 * n := by omega
      have hnLeR : (n : ℝ) ≤ ((U + 2 * n : ℕ) : ℝ) := by
        exact_mod_cast hnLe
      have hLogTwoNonneg : (0 : ℝ) ≤ Real.log 2 :=
        Real.log_nonneg (by norm_num)
      have hScaled :=
        mul_le_mul_of_nonneg_right hnLeR hLogTwoNonneg
      exact le_trans hOneN hScaled

private theorem qGeTwoBottomAlpha_pos
    {n U : ℕ} (hn3 : 3 ≤ n) :
    ∀ i, 0 < qGeTwoBottomAlpha n U i := by
  intro i
  fin_cases i
  · norm_num [qGeTwoBottomAlpha]
  · dsimp [qGeTwoBottomAlpha]
    exact qGeTwoAlpha_pos (U := U) (by omega)
  · norm_num [qGeTwoBottomAlpha]

private theorem qGeTwoCutExponent_le_main
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hn : 0 < n)
    (hr : 0 < r)
    (hqt : h.q < h.t) :
    qGeTwoCutExponent n h.q ≤ qGeTwoMainExponent k := by
  rw [qGeTwo_exponent_split h hn hr hqt]
  omega

private theorem qGeTwoBottomCoeff_natAbs_le
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hk4 : 4 ≤ k)
    (hn : 0 < n)
    (hr : 0 < r)
    (hqt : h.q < h.t) :
    ∀ i, (qGeTwoBottomCoeff k n h.q i).natAbs ≤ 4 * k := by
  have hQ := qGeTwoCutExponent_le_main h hn hr hqt
  have hM := qGeTwoMainExponent_le_two_mul k
  intro i
  fin_cases i
  · change qGeTwoCutExponent n h.q ≤ 4 * k
    omega
  · simp [qGeTwoBottomCoeff]
    omega
  · simp [qGeTwoBottomCoeff]
    omega

private theorem qGeTwoBottomLinearForm_eq_sum
    (k n q U : ℕ) :
    qGeTwoBottomLinearForm k n q U =
      ∑ i, (qGeTwoBottomCoeff k n q i : ℝ) *
        Real.log (qGeTwoBottomAlpha n U i : ℝ) := by
  rw [Fin.sum_univ_three]
  dsimp [qGeTwoBottomAlpha, qGeTwoBottomCoeff, qGeTwoBottomLinearForm]
  push_cast
  ring

private theorem qGeTwoBottomHeightProduct_le
    {n U : ℕ}
    (hn3 : 3 ≤ n) :
    (∏ i, BakerWustholz.modifiedHeight (Rat.castHom ℂ) (qGeTwoBottomAlpha n U i)) ≤
      (((U + 2 * n : ℕ) : ℝ) * Real.log 2) * Real.log 3 := by
  rw [Fin.prod_univ_three]
  dsimp [qGeTwoBottomAlpha]
  have hAlpha := qGeTwoAlpha_modifiedHeight_le (U := U) hn3
  have h12 := mul_le_mul mh_two hAlpha (modifiedHeight_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h3nonneg := modifiedHeight_nonneg (3 : ℚ)
  have hRightNonneg : 0 ≤ (1 : ℝ) * (((U + 2 * n : ℕ) : ℝ) * Real.log 2) := by positivity
  have h := mul_le_mul h12 mh_three h3nonneg hRightNonneg
  simpa [mul_assoc] using h

/--
下側 exact identity に対する Baker--Wüstholz 下界。

ここでは中央の基数
`α = qGeTwoAlpha n U`
が一般には整数ではなく正の有理数になる。

外部定理へ渡す基数は `(2, α, 3)`、
係数は `(Q, 1, -k)`。
-/
private theorem qGeTwoBottomBW_log_lower
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hk4 : 4 ≤ k)
    (hn3 : 3 ≤ n)
    (hr12 : r = 1 ∨ r = 2)
    (hqt : h.q < h.t)
    (hΛPos :
      0 < qGeTwoBottomLinearForm
        k n h.q (qGeTwoUpperRun n r h.q h.t)) :
    -(BakerWustholz.C 3 1 * max (Real.log (4 * k)) 1 *
        ((((qGeTwoUpperRun n r h.q h.t + 2 * n : ℕ) : ℝ) *
            Real.log 2) *
          Real.log 3)) ≤
      Real.log
        (qGeTwoBottomLinearForm
          k n h.q (qGeTwoUpperRun n r h.q h.t)) := by
  have hr : 0 < r := by
    rcases hr12 with rfl | rfl <;> norm_num
  let U := qGeTwoUpperRun n r h.q h.t
  have hAlphaPos :
      (0 : ℚ) < qGeTwoAlpha n U :=
    qGeTwoAlpha_pos (U := U) (by omega)
  have hQleM :=
    qGeTwoCutExponent_le_main
      h (by omega : 0 < n) hr hqt
  have hM :=
    qGeTwoMainExponent_le_two_mul k
  have haB :
      qGeTwoCutExponent n h.q ≤ 4 * k := by
    omega
  have hkB : k ≤ 4 * k := by
    omega
  have hForm :
      qGeTwoBottomLinearForm k n h.q U =
        BakerWustholz.threeLogRatForm
          (qGeTwoCutExponent n h.q)
          k
          1
          (qGeTwoAlpha n U) := by
    unfold qGeTwoBottomLinearForm BakerWustholz.threeLogRatForm
    norm_num
  have hBW :=
    log_threeForm_rat_ge
      (a := qGeTwoCutExponent n h.q)
      (k := k)
      (B := 4 * k)
      (α := qGeTwoAlpha n U)
      hAlphaPos
      (ε := 1)
      (Or.inl rfl)
      (by omega)
      haB
      hkB
      hForm
      hΛPos
  have hProd :=
    qGeTwoBottomHeightProduct_le (U := U) hn3
  rw [Fin.prod_univ_three] at hProd
  dsimp [qGeTwoBottomAlpha] at hProd
  have hScaleNonneg :
      0 ≤ BakerWustholz.C 3 1 * max (Real.log (4 * k)) 1 :=
    mul_nonneg
      (C_one_nonneg 3)
      (le_trans zero_le_one (le_max_right _ _))
  have hMul :=
    mul_le_mul_of_nonneg_left hProd hScaleNonneg
  have hNeg := neg_le_neg hMul
  exact le_trans
    (by simpa [U, mul_assoc] using hNeg)
    hBW

/-- bottom 3-log から `k` の実数 bound を得る。 -/
private theorem qGeTwoDepth_real_bound
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hk4 : 4 ≤ k)
    (hn3 : 3 ≤ n)
    (hr12 : r = 1 ∨ r = 2)
    (hqt : h.q < h.t) :
    (k : ℝ) - 1 ≤
      BakerWustholz.C 3 1 * Real.log 2 *
        max (Real.log (4 * k)) 1 *
        ((qGeTwoUpperRun n r h.q h.t + 2 * n : ℕ) : ℝ) := by
  have hr : 0 < r := by rcases hr12 with rfl | rfl <;> norm_num
  have hΛPos := qGeTwoBottomLinearForm_pos h (by omega) hr hqt
  have hLow := qGeTwoBottomBW_log_lower h hk4 hn3 hr12 hqt hΛPos
  have hUp := qGeTwoBottomLinearForm_log_upper h hn3 hr12 hqt
  have hCombined := le_trans hLow hUp
  have h3pos := log_three_pos
  have hFactored :
      (((k : ℝ) - 1) * Real.log 3) ≤
        (BakerWustholz.C 3 1 * Real.log 2 *
          max (Real.log (4 * k)) 1 *
          ((qGeTwoUpperRun n r h.q h.t + 2 * n : ℕ) : ℝ)) * Real.log 3 := by
    nlinarith
  nlinarith

/-! ## `z=floor(log₂k)` への粗視化 -/

private theorem qGeTwoHeightParameter_le
    {k : ℕ} (hk4 : 4 ≤ k) :
    max (Real.log ((4 : ℝ) * (k : ℝ))) 1 ≤
      ((7 : ℝ) / 10) * ((qGeTwoLogDepth k + 3 : ℕ) : ℝ) := by
  have hkPowUpper : k < 2 ^ (qGeTwoLogDepth k + 1) := by
    unfold qGeTwoLogDepth
    exact Nat.lt_pow_succ_log_self (by norm_num) k
  have hFourK : 4 * k < 2 ^ (qGeTwoLogDepth k + 3) := by
    calc
      4 * k < 4 * 2 ^ (qGeTwoLogDepth k + 1) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < (4 : ℕ))).2 hkPowUpper
      _ = 2 ^ (qGeTwoLogDepth k + 3) := by
        rw [show qGeTwoLogDepth k + 3 = (qGeTwoLogDepth k + 1) + 2 by omega,
          pow_add]
        norm_num
        ring
  have hLogLt :
      Real.log ((4 : ℝ) * (k : ℝ)) <
        ((qGeTwoLogDepth k + 3 : ℕ) : ℝ) * Real.log 2 := by
    have hCast :
        (4 : ℝ) * (k : ℝ) < (2 : ℝ) ^ (qGeTwoLogDepth k + 3) := by
      exact_mod_cast hFourK
    have h := Real.log_lt_log (by positivity) hCast
    rw [Real.log_pow] at h
    exact h
  have hLogBound :
      Real.log ((4 : ℝ) * (k : ℝ)) ≤
        ((7 : ℝ) / 10) * ((qGeTwoLogDepth k + 3 : ℕ) : ℝ) := by
    have h2 := log_two_le_seven_tenths
    have hzNonneg : (0 : ℝ) ≤ ((qGeTwoLogDepth k + 3 : ℕ) : ℝ) := by positivity
    have hMul := mul_le_mul_of_nonneg_left h2 hzNonneg
    nlinarith
  have hz2 : 2 ≤ qGeTwoLogDepth k := by
    unfold qGeTwoLogDepth
    apply Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ))
    norm_num
    exact hk4
  have hzFive : (5 : ℝ) ≤ ((qGeTwoLogDepth k + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 5 ≤ qGeTwoLogDepth k + 3 by omega)
  have hOne :
      (1 : ℝ) ≤ ((7 : ℝ) / 10) * ((qGeTwoLogDepth k + 3 : ℕ) : ℝ) := by
    nlinarith
  exact max_le hLogBound hOne

private theorem qGeTwoWidth_le_log_even
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk4 : 4 ≤ k)
    (hkEven : k % 2 = 0)
    (hn : 0 < n)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q) :
    n ≤ qGeTwoLogDepth k + 2 := by
  have hWidth := h.even_q_ge_two_width_eq (by omega) ((Nat.even_iff).2 hkEven)
    hn hqt hqTwo
  have hv := padicValNat_le_nat_log (p := 2) k
  rw [hWidth]
  simpa [qGeTwoLogDepth, Nat.add_comm] using Nat.add_le_add_left hv 2

private theorem qGeTwoWidth_le_log_odd
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk4 : 4 ≤ k)
    (hkOdd : k % 2 = 1)
    (hn : 0 < n)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q) :
    n ≤ qGeTwoLogDepth k + 2 := by
  have hWidth := h.odd_q_ge_two_width_eq (by omega) hkOdd hn hqt hqTwo
  have hv := padicValNat_le_nat_log (p := 2) (k - 1)
  have hLogMono : Nat.log 2 (k - 1) ≤ Nat.log 2 k := Nat.log_mono_right (by omega)
  rw [hWidth]
  dsimp [qGeTwoLogDepth]
  omega

private def qGeTwoUPoly (z : ℕ) : ℕ :=
  1680000000000 * (z + 3) * (z + 2) + 2

private def qGeTwoPoly (z : ℕ) : ℕ :=
  1050000000000 * (z + 3) * (qGeTwoUPoly z + 2 * (z + 2)) + 1

private theorem qGeTwoUpperRun_le_poly
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hk4 : 4 ≤ k)
    (hn3 : 3 ≤ n)
    (hr12 : r = 1 ∨ r = 2)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hnLog : n ≤ qGeTwoLogDepth k + 2) :
    qGeTwoUpperRun n r h.q h.t ≤ qGeTwoUPoly (qGeTwoLogDepth k) := by
  have hReal := qGeTwoUpperRun_real_bound h hk4 hn3 hr12 hqt hqTwo hnLog
  have hH := qGeTwoHeightParameter_le hk4
  have hC := C_three_mul_log_three_le_sharp
  have hnR : (n : ℝ) ≤ ((qGeTwoLogDepth k + 2 : ℕ) : ℝ) := by exact_mod_cast hnLog
  have hHNonneg : 0 ≤ max (Real.log (4 * k)) 1 := le_trans zero_le_one (le_max_right _ _)
  have hnNonneg : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hCoarse :
      ((qGeTwoUpperRun n r h.q h.t + n : ℕ) : ℝ) - 2 ≤
        (1680000000000 : ℝ) *
          ((qGeTwoLogDepth k + 3 : ℕ) : ℝ) *
          ((qGeTwoLogDepth k + 2 : ℕ) : ℝ) := by
    calc
      ((qGeTwoUpperRun n r h.q h.t + n : ℕ) : ℝ) - 2
          ≤ (BakerWustholz.C 3 1 * Real.log 3) *
              max (Real.log (4 * k)) 1 * (n : ℝ) := by
                simpa [mul_assoc] using hReal
      _ ≤ (2400000000000 : ℝ) * max (Real.log (4 * k)) 1 * (n : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC hHNonneg) hnNonneg
      _ ≤ (2400000000000 : ℝ) *
            (((7 : ℝ) / 10) * ((qGeTwoLogDepth k + 3 : ℕ) : ℝ)) * (n : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hH (by norm_num)) hnNonneg
      _ ≤ (2400000000000 : ℝ) *
            (((7 : ℝ) / 10) * ((qGeTwoLogDepth k + 3 : ℕ) : ℝ)) *
            ((qGeTwoLogDepth k + 2 : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_left hnR (by positivity)
      _ = (1680000000000 : ℝ) *
            ((qGeTwoLogDepth k + 3 : ℕ) : ℝ) *
            ((qGeTwoLogDepth k + 2 : ℕ) : ℝ) := by ring
  have hUReal :
      (qGeTwoUpperRun n r h.q h.t : ℝ) ≤
        (qGeTwoUPoly (qGeTwoLogDepth k) : ℝ) := by
    push_cast at hCoarse
    dsimp [qGeTwoUPoly]
    push_cast
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith
  exact_mod_cast hUReal

private theorem qGeTwoDepth_le_poly
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hk4 : 4 ≤ k)
    (hn3 : 3 ≤ n)
    (hr12 : r = 1 ∨ r = 2)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hnLog : n ≤ qGeTwoLogDepth k + 2) :
    k ≤ qGeTwoPoly (qGeTwoLogDepth k) := by
  have hU := qGeTwoUpperRun_le_poly h hk4 hn3 hr12 hqt hqTwo hnLog
  have hReal := qGeTwoDepth_real_bound h hk4 hn3 hr12 hqt
  have hH := qGeTwoHeightParameter_le hk4
  have hC := C_three_mul_log_two_le_sharp
  have hnR : (n : ℝ) ≤ ((qGeTwoLogDepth k + 2 : ℕ) : ℝ) := by exact_mod_cast hnLog
  have hUR :
      (qGeTwoUpperRun n r h.q h.t : ℝ) ≤
        (qGeTwoUPoly (qGeTwoLogDepth k) : ℝ) := by exact_mod_cast hU
  have hHNonneg : 0 ≤ max (Real.log (4 * k)) 1 := le_trans zero_le_one (le_max_right _ _)
  have hUNonneg : (0 : ℝ) ≤ ((qGeTwoUpperRun n r h.q h.t + 2 * n : ℕ) : ℝ) := by positivity
  have hUN :
      ((qGeTwoUpperRun n r h.q h.t + 2 * n : ℕ) : ℝ) ≤
        (qGeTwoUPoly (qGeTwoLogDepth k) : ℝ) +
          2 * ((qGeTwoLogDepth k + 2 : ℕ) : ℝ) := by
    have hnR' := hnR
    have hUR' := hUR
    push_cast at hnR' hUR' ⊢
    linarith
  have hCoarse :
      (k : ℝ) - 1 ≤
        (1050000000000 : ℝ) *
          ((qGeTwoLogDepth k + 3 : ℕ) : ℝ) *
          ((qGeTwoUPoly (qGeTwoLogDepth k) : ℝ) +
            2 * ((qGeTwoLogDepth k + 2 : ℕ) : ℝ)) := by
    calc
      (k : ℝ) - 1
          ≤ (BakerWustholz.C 3 1 * Real.log 2) *
              max (Real.log (4 * k)) 1 *
              ((qGeTwoUpperRun n r h.q h.t + 2 * n : ℕ) : ℝ) := by
                simpa [mul_assoc] using hReal
      _ ≤ (1500000000000 : ℝ) * max (Real.log (4 * k)) 1 *
              ((qGeTwoUpperRun n r h.q h.t + 2 * n : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC hHNonneg) hUNonneg
      _ ≤ (1500000000000 : ℝ) *
            (((7 : ℝ) / 10) * ((qGeTwoLogDepth k + 3 : ℕ) : ℝ)) *
              ((qGeTwoUpperRun n r h.q h.t + 2 * n : ℕ) : ℝ) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hH (by norm_num)) hUNonneg
      _ ≤ (1500000000000 : ℝ) *
            (((7 : ℝ) / 10) * ((qGeTwoLogDepth k + 3 : ℕ) : ℝ)) *
              ((qGeTwoUPoly (qGeTwoLogDepth k) : ℝ) +
                2 * ((qGeTwoLogDepth k + 2 : ℕ) : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hUN (by positivity)
      _ = (1050000000000 : ℝ) *
            ((qGeTwoLogDepth k + 3 : ℕ) : ℝ) *
              ((qGeTwoUPoly (qGeTwoLogDepth k) : ℝ) +
                2 * ((qGeTwoLogDepth k + 2 : ℕ) : ℝ)) := by ring
  have hkReal : (k : ℝ) ≤ (qGeTwoPoly (qGeTwoLogDepth k) : ℝ) := by
    have hCoarse' := hCoarse
    push_cast at hCoarse'
    dsimp [qGeTwoPoly]
    push_cast
    linarith
  exact_mod_cast hkReal

/-- `z≥101` では q≥2 用三次多項式は `2^z` より小さい。 -/
private theorem qGeTwoPoly_lt_twoPow
    {z : ℕ} (hz : 101 ≤ z) :
    qGeTwoPoly z < 2 ^ z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hz
  induction d with
  | zero =>
      norm_num [qGeTwoPoly, qGeTwoUPoly]
  | succ d ih =>
      have hStep :
          qGeTwoPoly (101 + (d + 1)) < 2 * qGeTwoPoly (101 + d) := by
        let gap : ℕ :=
          1764000000000000000000000 * d ^ 3 +
          543312000000002100000000000 * d ^ 2 +
          55768860000000432600000000000 * d +
          1907758944000022274700000000001
        have hEq :
            2 * qGeTwoPoly (101 + d) =
              qGeTwoPoly (101 + (d + 1)) + gap := by
          dsimp [qGeTwoPoly, qGeTwoUPoly, gap]
          ring
        have hGap : 0 < gap := by
          dsimp [gap]
          positivity
        omega
      calc
        qGeTwoPoly (101 + (d + 1)) < 2 * qGeTwoPoly (101 + d) := hStep
        _ < 2 * 2 ^ (101 + d) :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < (2 : ℕ))).2 (ih (by omega))
        _ = 2 ^ (101 + (d + 1)) := by
          rw [show 101 + (d + 1) = (101 + d) + 1 by omega, pow_succ]
          ring

private theorem qGeTwo_depth_lt_of_data
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hk4 : 4 ≤ k)
    (hn3 : 3 ≤ n)
    (hr12 : r = 1 ∨ r = 2)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q)
    (hnLog : n ≤ qGeTwoLogDepth k + 2) :
    k < targetOneQGeTwoInternalDepthBound := by
  have hkPoly := qGeTwoDepth_le_poly h hk4 hn3 hr12 hqt hqTwo hnLog
  by_contra hNot
  have hkBig : targetOneQGeTwoInternalDepthBound ≤ k := by omega
  have hz101 : 101 ≤ qGeTwoLogDepth k := by
    unfold targetOneQGeTwoInternalDepthBound at hkBig
    unfold qGeTwoLogDepth
    apply Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ))
    exact hkBig
  have hPolyExp := qGeTwoPoly_lt_twoPow hz101
  have hPowLeK : 2 ^ qGeTwoLogDepth k ≤ k := by
    unfold qGeTwoLogDepth
    exact Nat.pow_log_le_self 2 (by omega : k ≠ 0)
  omega

/-! ## public B/D bound: gcd 仮定なし -/

/-- B (`even,q≥2`) は external periodic-run bound なしで `k<2^101`。 -/
theorem TargetOneHoleGeometricData.even_q_ge_two_internal_depth_bound
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q) :
    k < targetOneQGeTwoInternalDepthBound := by
  have hnLog := qGeTwoWidth_le_log_even h hk hkEven (by omega) hqt hqTwo
  exact qGeTwo_depth_lt_of_data h hk hn (Or.inl rfl) hqt hqTwo hnLog

/-- D (`odd,q≥2`) も external periodic-run bound なしで `k<2^101`。 -/
theorem TargetOneHoleGeometricData.odd_q_ge_two_internal_depth_bound
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hqTwo : 2 ≤ h.q) :
    k < targetOneQGeTwoInternalDepthBound := by
  have hnLog := qGeTwoWidth_le_log_odd h hk hkOdd (by omega) hqt hqTwo
  exact qGeTwo_depth_lt_of_data h hk hn (Or.inr rfl) hqt hqTwo hnLog

end Mersenne
end Collatz3
