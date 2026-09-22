import CollatzLean.Collatz3.External.BakerWustholz
import CollatzLean.Collatz3.Mersenne.TargetOneHoleLocks
import CollatzLean.Collatz3.Mersenne.TargetOneHoleValuation
import CollatzLean.Collatz3.Mersenne.OneHoleThreeTailLargeDepth
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option linter.style.nativeDecide false

/-!
# Collatz3 Mersenne: target-one `q=1` の無条件 A/C closure

A1 の四枝のうち

* A: even, `q=1`, `r=1`
* C: odd,  `q=1`, `r=2`

を外部 package から完全に外す。

q=1 では汎用 periodic-window theorem より強い exact identity が得られる。
`M = floor(log₂(3^k))` とすると

* A: `(2^n-1) 3^k + 2^n + 1 = 2^(M+n)`
* C: `(2^n-1) 3^k + 2^n + 3 = 2^(M+n)`

である。これは 3-log linear form

`(M+n) log 2 - log(2^n-1) - k log 3`

を直接 Baker--Wüstholz に入れられる形で、Stephan の一般 4-log periodic-run
estimate より q=1 に特化した分だけ単純である。

解析部分で `k < 10^23` を得た後は、既存 M₄
`561847684041` (`2`: period 486, `3`: tail 6 / period 972) を使う。
valuation lock から `n < 78` となり、`L mod 486` を自由に許した
over-approximation ですら survivor は 0。従って bounded residual も repo 内の
`native_decide` certificate で閉じる。

外部数学として引用するのは `External/BakerWustholz.lean` の [BW93] 主定理だけで、
A/C 固有の `... → False` や explicit depth bound は仮定しない。
-/

namespace Collatz3
namespace Mersenne

open External.BakerWustholzQ

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- A/C の three-log estimate に使う安全側の finite cut。 -/
def targetOneQOneInternalDepthBound : ℕ := 10 ^ 23

/-! ## q=1 geometric data から元の target-one equation を回収 -/

/--
`q=1` geometric equation は元の target-one exact equation と同値な方向へ戻せる。

この補題により解析 identity と M₄ finite sieve の両方を同じ geometric data から
開始できる。
-/
theorem TargetOneHoleGeometricData.toTargetOneHoleEquation_of_q_one
    {k n r L b : ℕ}
    (h : TargetOneHoleGeometricData k n r L b)
    (hq : h.q = 1) :
    TargetOneHoleEquation k n r L b := by
  have hb : b + r = n := by
    have := h.b_add_r_eq
    rw [hq] at this
    simpa using this
  have hEqNat := h.equation
  rw [hq] at hEqNat
  have hG1 : targetGeomSum (2 ^ n) 1 = 1 := by
    simp [targetGeomSum]
  rw [hG1] at hEqNat
  have hEqZ :
      (3 : ℤ) ^ k + 1 =
        (2 : ℤ) ^ r * (targetGeomSum (2 ^ n) h.t : ℤ) := by
    exact_mod_cast hEqNat
  have hxOne : 1 ≤ 2 ^ n := by
    have hxPos : 0 < 2 ^ n := pow_pos (by norm_num : 0 < (2 : ℕ)) n
    omega
  have hGeomNat :
      targetGeomSum (2 ^ n) h.t * (2 ^ n - 1) =
        (2 ^ n) ^ h.t - 1 := by
    unfold targetGeomSum
    exact geom_sum_mul_of_one_le hxOne h.t
  have hPowOne : 1 ≤ (2 ^ n) ^ h.t := by
    have hp : 0 < (2 ^ n) ^ h.t := pow_pos (by positivity : 0 < (2 ^ n)) h.t
    omega
  have hGeomNat' :
      targetGeomSum (2 ^ n) h.t * (2 ^ n - 1) + 1 =
        (2 ^ n) ^ h.t := by
    rw [hGeomNat]
    exact Nat.sub_add_cancel hPowOne
  have hSubCast :
      (((2 ^ n - 1 : ℕ) : ℤ)) = (2 : ℤ) ^ n - 1 := by
    rw [Nat.cast_sub hxOne]
    norm_num
  have hPowCast :
      ((((2 ^ n) ^ h.t : ℕ) : ℤ)) = ((2 : ℤ) ^ n) ^ h.t := by
    norm_num
  have hGeomNatCast := congrArg (fun x : ℕ => (x : ℤ)) hGeomNat'
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hGeomNatCast
  rw [hSubCast, hPowCast] at hGeomNatCast
  have hGeomZ :
      (targetGeomSum (2 ^ n) h.t : ℤ) * ((2 : ℤ) ^ n - 1) =
        ((2 : ℤ) ^ n) ^ h.t - 1 := by
    linarith
  have hbPow :
      (2 : ℤ) ^ n = (2 : ℤ) ^ r * (2 : ℤ) ^ b := by
    calc
      (2 : ℤ) ^ n = (2 : ℤ) ^ (b + r) := by rw [hb]
      _ = (2 : ℤ) ^ b * (2 : ℤ) ^ r := by rw [pow_add]
      _ = (2 : ℤ) ^ r * (2 : ℤ) ^ b := by ring
  have hLPow :
      (2 : ℤ) ^ L = ((2 : ℤ) ^ n) ^ h.t := by
    calc
      (2 : ℤ) ^ L = (2 : ℤ) ^ (n * h.t) :=
        congrArg (fun e : ℕ => (2 : ℤ) ^ e) h.length_eq
      _ = ((2 : ℤ) ^ n) ^ h.t := by rw [pow_mul]
  unfold TargetOneHoleEquation
  calc
    (3 : ℤ) ^ k * ((2 : ℤ) ^ n - 1)
        = (((2 : ℤ) ^ r * (targetGeomSum (2 ^ n) h.t : ℤ)) - 1) *
            ((2 : ℤ) ^ n - 1) := by
              rw [← hEqZ]
              ring
    _ = (2 : ℤ) ^ r *
          ((targetGeomSum (2 ^ n) h.t : ℤ) * ((2 : ℤ) ^ n - 1)) -
          (2 : ℤ) ^ n + 1 := by ring
    _ = (2 : ℤ) ^ r * (((2 : ℤ) ^ n) ^ h.t - 1) -
          (2 : ℤ) ^ n + 1 := by rw [hGeomZ]
    _ = (2 : ℤ) ^ r * ((2 : ℤ) ^ L - 1) -
          (2 : ℤ) ^ r * (2 : ℤ) ^ b + 1 := by rw [hLPow, hbPow]
    _ = (2 : ℤ) ^ r *
          ((2 : ℤ) ^ L - 1 - (2 : ℤ) ^ b) + 1 := by ring

/-! ## Beatty index と通常の Nat.log -/

/-- project の power-form Beatty index は通常の `Nat.log 2 (3^k)` に一致する。 -/
theorem beattyIndex_eq_natLog_threePow
    {k : ℕ} :
    Critical.beattyIndex k = Nat.log 2 (3 ^ k) := by
  have hLower : 2 ^ Critical.beattyIndex k ≤ 3 ^ k :=
    Critical.beattyIndex_lower k
  have hUpper : 3 ^ k ≤ 2 ^ (Critical.beattyIndex k + 1) :=
    Critical.beattyIndex_upper k
  have hUpperStrict : 3 ^ k < 2 ^ (Critical.beattyIndex k + 1) := by
    refine lt_of_le_of_ne hUpper ?_
    intro hEq
    have hOdd : Odd (3 ^ k) := (by decide : Odd (3 : ℕ)).pow
    have hEven : Even (2 ^ (Critical.beattyIndex k + 1)) := by
      apply even_iff_two_dvd.mpr
      exact dvd_pow_self 2 (by omega : Critical.beattyIndex k + 1 ≠ 0)
    rcases hOdd with ⟨u, hu⟩
    rcases hEven with ⟨v, hv⟩
    rw [hEq] at hu
    omega
  exact (Nat.log_eq_of_pow_le_of_lt_pow hLower hUpperStrict).symm

/-! ## q=1 exact three-log identities -/

/-- A (`r=1,q=1`) の exact three-log identity。 -/
theorem TargetOneHoleGeometricData.even_q_one_threeLogIdentity
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hn : 0 < n)
    (hqt : h.q < h.t)
    (hq : h.q = 1) :
    (2 ^ n - 1) * 3 ^ k + 2 ^ n + 1 =
      2 ^ (Nat.log 2 (3 ^ k) + n) := by
  have hTarget := h.toTargetOneHoleEquation_of_q_one hq
  have hb : b + 1 = n := by
    have hb0 := h.b_add_r_eq
    rw [hq] at hb0
    norm_num at hb0
    exact hb0
  have hBeatty := h.beattyIndex_eq hn (by norm_num) hqt
  have hBeattyLog := beattyIndex_eq_natLog_threePow (k:=k)
  have htPos : 0 < h.t := by omega
  have hMul : n * h.t = n * (h.t - 1) + n := by
    rw [show h.t = (h.t - 1) + 1 by omega, Nat.mul_add]
    simp
  have hTopExp : 1 + L = Nat.log 2 (3 ^ k) + n := by
    rw [h.length_eq]
    rw [hBeattyLog] at hBeatty
    omega
  have hHolePow :
      (2 : ℤ) * (2 : ℤ) ^ b = (2 : ℤ) ^ n := by
    calc
      (2 : ℤ) * (2 : ℤ) ^ b = (2 : ℤ) ^ b * 2 := by ring
      _ = (2 : ℤ) ^ (b + 1) := by rw [pow_succ]
      _ = (2 : ℤ) ^ n := by congr 1
  have hTopPow :
      (2 : ℤ) * (2 : ℤ) ^ L = (2 : ℤ) ^ (Nat.log 2 (3 ^ k) + n) := by
    calc
      (2 : ℤ) * (2 : ℤ) ^ L = (2 : ℤ) ^ L * 2 := by ring
      _ = (2 : ℤ) ^ (L + 1) := by rw [pow_succ]
      _ = (2 : ℤ) ^ (Nat.log 2 (3 ^ k) + n) := by congr 1; omega
  have hTargetZ := hTarget
  unfold TargetOneHoleEquation at hTargetZ
  norm_num at hTargetZ
  have hIdentityZ :
      ((2 : ℤ) ^ n - 1) * (3 : ℤ) ^ k + (2 : ℤ) ^ n + 1 =
        (2 : ℤ) ^ (Nat.log 2 (3 ^ k) + n) := by
    calc
      ((2 : ℤ) ^ n - 1) * (3 : ℤ) ^ k + (2 : ℤ) ^ n + 1
          = (3 : ℤ) ^ k * ((2 : ℤ) ^ n - 1) + (2 : ℤ) ^ n + 1 := by ring
      _ = 2 * ((2 : ℤ) ^ L - 1 - (2 : ℤ) ^ b) + 1 +
            (2 : ℤ) ^ n + 1 := by rw [hTargetZ]
      _ = 2 * (2 : ℤ) ^ L := by
            rw [← hHolePow]
            ring
      _ = (2 : ℤ) ^ (Nat.log 2 (3 ^ k) + n) := hTopPow
  have hPowOne : 1 ≤ 2 ^ n := by
    have hp : 0 < 2 ^ n := pow_pos (by norm_num : 0 < (2 : ℕ)) n
    omega
  have hCastGoal :
      (((2 ^ n - 1) * 3 ^ k + 2 ^ n + 1 : ℕ) : ℤ) =
        ((2 ^ (Nat.log 2 (3 ^ k) + n) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hPowOne]
    simpa using hIdentityZ
  exact Int.ofNat_injective hCastGoal

/-- C (`r=2,q=1`) の exact three-log identity。 -/
theorem TargetOneHoleGeometricData.odd_q_one_threeLogIdentity
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hn : 0 < n)
    (hqt : h.q < h.t)
    (hq : h.q = 1) :
    (2 ^ n - 1) * 3 ^ k + 2 ^ n + 3 =
      2 ^ (Nat.log 2 (3 ^ k) + n) := by
  have hTarget := h.toTargetOneHoleEquation_of_q_one hq
  have hb : b + 2 = n := by
    have hb0 := h.b_add_r_eq
    rw [hq] at hb0
    norm_num at hb0
    exact hb0
  have hBeatty := h.beattyIndex_eq hn (by norm_num) hqt
  have hBeattyLog := beattyIndex_eq_natLog_threePow (k:=k)
  have htPos : 0 < h.t := by omega
  have hMul : n * h.t = n * (h.t - 1) + n := by
    rw [show h.t = (h.t - 1) + 1 by omega, Nat.mul_add]
    simp
  have hTopExp : 2 + L = Nat.log 2 (3 ^ k) + n := by
    rw [h.length_eq]
    rw [hBeattyLog] at hBeatty
    omega
  have hHolePow :
      (4 : ℤ) * (2 : ℤ) ^ b = (2 : ℤ) ^ n := by
    have h4 : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_add]
    congr 1
    omega
  have hTopPow :
      (4 : ℤ) * (2 : ℤ) ^ L = (2 : ℤ) ^ (Nat.log 2 (3 ^ k) + n) := by
    have h4 : (4 : ℤ) = 2 ^ 2 := by norm_num
    rw [h4, ← pow_add]
    congr 1
  have hTargetZ := hTarget
  unfold TargetOneHoleEquation at hTargetZ
  norm_num at hTargetZ
  have hIdentityZ :
      ((2 : ℤ) ^ n - 1) * (3 : ℤ) ^ k + (2 : ℤ) ^ n + 3 =
        (2 : ℤ) ^ (Nat.log 2 (3 ^ k) + n) := by
    calc
      ((2 : ℤ) ^ n - 1) * (3 : ℤ) ^ k + (2 : ℤ) ^ n + 3
          = (3 : ℤ) ^ k * ((2 : ℤ) ^ n - 1) + (2 : ℤ) ^ n + 3 := by ring
      _ = 4 * ((2 : ℤ) ^ L - 1 - (2 : ℤ) ^ b) + 1 +
            (2 : ℤ) ^ n + 3 := by rw [hTargetZ]
      _ = 4 * (2 : ℤ) ^ L := by
            rw [← hHolePow]
            ring
      _ = (2 : ℤ) ^ (Nat.log 2 (3 ^ k) + n) := hTopPow
  have hPowOne : 1 ≤ 2 ^ n := by
    have hp : 0 < 2 ^ n := pow_pos (by norm_num : 0 < (2 : ℕ)) n
    omega
  have hCastGoal :
      (((2 ^ n - 1) * 3 ^ k + 2 ^ n + 3 : ℕ) : ℤ) =
        ((2 ^ (Nat.log 2 (3 ^ k) + n) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hPowOne]
    simpa using hIdentityZ
  exact Int.ofNat_injective hCastGoal

/-! ## 離散 exponential dominance -/

private def qOnePoly (z : ℕ) : ℕ :=
  8000000000000 * (z + 3) * (z + 1) + 3

/-- `z≥76` では three-log 側の二次式は `2^z` より小さい。 -/
private theorem qOnePoly_lt_twoPow
    {z : ℕ}
    (hz : 76 ≤ z) :
    qOnePoly z < 2 ^ z := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hz
  induction d with
  | zero =>
      norm_num [qOnePoly]
  | succ d ih =>
      have hStep :
          qOnePoly (76 + (d + 1)) < 2 * qOnePoly (76 + d) := by
        dsimp [qOnePoly]
        nlinarith [sq_nonneg d]
      calc
        qOnePoly (76 + (d + 1)) < 2 * qOnePoly (76 + d) := hStep
        _ < 2 * 2 ^ (76 + d) :=
          (Nat.mul_lt_mul_left (by norm_num : 0 < (2 : ℕ))).2 (ih (by omega))
        _ = 2 ^ (76 + (d + 1)) := by
          rw [show 76 + (d + 1) = (76 + d) + 1 by omega, pow_succ]
          ring

/-! ## 共通 three-log Baker--Wüstholz bound -/

/-- three-log identity に現れる主指数 `M = floor(log₂(3^k))`。 -/
private def qOneMainExponent (k : ℕ) : ℕ :=
  Nat.log 2 (3 ^ k)

/-- 深さ `k` の二進 logarithmic scale `z = floor(log₂ k)`。 -/
private def qOneLogDepth (k : ℕ) : ℕ :=
  Nat.log 2 k

/-- three-log identity の中央因子 `G = 2^n - 1`。 -/
private def qOneGap (n : ℕ) : ℕ :=
  2 ^ n - 1

/-- A/C を統一して扱うための誤差項 `E = 2^n + e`。 -/
private def qOneError (n e : ℕ) : ℕ :=
  2 ^ n + e

/--
three-log identity に対応する実 linear form
`Λ = (M+n)log 2 - log G - k log 3`。
-/
private noncomputable def qOneLinearForm (k n : ℕ) : ℝ :=
  ((qOneMainExponent k + n : ℕ) : ℝ) * Real.log 2 -
    Real.log (qOneGap n : ℝ) - (k : ℝ) * Real.log 3

/-- Baker--Wüstholz に渡す三つの有理数 `(2,G,3)`。 -/
private def qOneAlpha (n : ℕ) : Fin 3 → ℚ :=
  ![2, (((qOneGap n : ℕ) : ℤ) : ℚ), 3]

/-- Baker--Wüstholz に渡す係数 `(M+n,-1,-k)`。 -/
private def qOneCoeff (k n : ℕ) : Fin 3 → ℤ :=
  ![((qOneMainExponent k + n : ℕ) : ℤ), -1, -((k : ℕ) : ℤ)]

/-- `M = floor(log₂(3^k))` は粗く `2k` 以下である。 -/
private theorem qOneMainExponent_le_two_mul
    (k : ℕ) :
    qOneMainExponent k ≤ 2 * k := by
  unfold qOneMainExponent
  have hPow : (3 : ℕ) ^ k ≤ 2 ^ (2 * k) := by
    calc
      (3 : ℕ) ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
      _ = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  calc
    Nat.log 2 (3 ^ k) ≤ Nat.log 2 (2 ^ (2 * k)) := Nat.log_mono_right hPow
    _ = 2 * k := Nat.log_pow (by norm_num) _

/-- `n>0` なら `G=2^n-1` は正である。 -/
private theorem qOneGap_pos
    {n : ℕ}
    (hn : 0 < n) :
    0 < qOneGap n := by
  unfold qOneGap
  have hp : 1 < 2 ^ n :=
    one_lt_pow₀ (by norm_num : (1 : ℕ) < 2) hn.ne'
  omega

/-- `n>0` なら `G=2^n-1` は `2^(n-1)` 以上である。 -/
private theorem qOneGap_lower
    {n : ℕ}
    (hn : 0 < n) :
    2 ^ (n - 1) ≤ qOneGap n := by
  unfold qOneGap
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring_nf
    simp
  rw [hpow]
  have hp : 0 < 2 ^ (n - 1) := by positivity
  omega

/-- `e≤3` なら誤差項 `E=2^n+e` は `4·2^n` 以下である。 -/
private theorem qOneError_le_four_mul_twoPow
    {n e : ℕ}
    (he : e ≤ 3) :
    qOneError n e ≤ 4 * 2 ^ n := by
  unfold qOneError
  have hp : 1 ≤ 2 ^ n := by
    have hp' : 0 < 2 ^ n := pow_pos (by norm_num : 0 < (2 : ℕ)) n
    omega
  omega

/-- `M=floor(log₂(3^k))` の定義から `2^M ≤ 3^k`。 -/
private theorem twoPow_qOneMainExponent_le_threePow
    (k : ℕ) :
    2 ^ qOneMainExponent k ≤ 3 ^ k := by
  unfold qOneMainExponent
  exact Nat.pow_log_le_self 2 (by positivity : 3 ^ k ≠ 0)

/--
exact identity を `G·3^k + E = 2^(M+n)` という共通形へ正規化する。
A では `e=1`、C では `e=3` を代入する。
-/
private theorem qOneIdentity_normalized
    {k n e : ℕ}
    (hIdentity :
      (2 ^ n - 1) * 3 ^ k + 2 ^ n + e =
        2 ^ (Nat.log 2 (3 ^ k) + n)) :
    qOneGap n * 3 ^ k + qOneError n e =
      2 ^ (qOneMainExponent k + n) := by
  simpa [qOneMainExponent, qOneGap, qOneError, Nat.add_assoc] using hIdentity

/--
exact identity を割り算して、three-log linear form を
`log(1 + E/(G·3^k))` として表す。
-/
private theorem qOneLinearForm_eq_log_one_add_ratio
    {k n e : ℕ}
    (hn : 0 < n)
    (hIdentity :
      (2 ^ n - 1) * 3 ^ k + 2 ^ n + e =
        2 ^ (Nat.log 2 (3 ^ k) + n)) :
    qOneLinearForm k n =
      Real.log
        (1 + (qOneError n e : ℝ) /
          ((qOneGap n : ℝ) * (3 : ℝ) ^ k)) := by
  have hGPos : 0 < qOneGap n := qOneGap_pos hn
  have hIdentity' := qOneIdentity_normalized hIdentity
  have hDenPos :
      (0 : ℝ) < (qOneGap n : ℝ) * (3 : ℝ) ^ k := by
    positivity
  have hTopPos :
      (0 : ℝ) < (2 : ℝ) ^ (qOneMainExponent k + n) := by
    positivity
  have hIdentityR :
      (qOneGap n : ℝ) * (3 : ℝ) ^ k + (qOneError n e : ℝ) =
        (2 : ℝ) ^ (qOneMainExponent k + n) := by
    exact_mod_cast hIdentity'
  have hGRne : (qOneGap n : ℝ) ≠ 0 := by
    exact_mod_cast hGPos.ne'
  have hThreePowRne : (3 : ℝ) ^ k ≠ 0 := by positivity
  have hRatio :
      qOneLinearForm k n =
        Real.log
          ((2 : ℝ) ^ (qOneMainExponent k + n) /
            ((qOneGap n : ℝ) * (3 : ℝ) ^ k)) := by
    unfold qOneLinearForm
    rw [Real.log_div hTopPos.ne' hDenPos.ne', Real.log_pow,
      Real.log_mul hGRne hThreePowRne, Real.log_pow]
    ring
  have hRatioEq :
      (2 : ℝ) ^ (qOneMainExponent k + n) /
          ((qOneGap n : ℝ) * (3 : ℝ) ^ k) =
        1 + (qOneError n e : ℝ) /
          ((qOneGap n : ℝ) * (3 : ℝ) ^ k) := by
    rw [← hIdentityR]
    field_simp [hDenPos.ne']
  rw [hRatio, hRatioEq]

/-- exact identity の右辺比が `1` より大きいので linear form `Λ` は正である。 -/
private theorem qOneLinearForm_pos
    {k n e : ℕ}
    (hn : 0 < n)
    (hIdentity :
      (2 ^ n - 1) * 3 ^ k + 2 ^ n + e =
        2 ^ (Nat.log 2 (3 ^ k) + n)) :
    0 < qOneLinearForm k n := by
  rw [qOneLinearForm_eq_log_one_add_ratio hn hIdentity]
  have hGPos : 0 < qOneGap n := qOneGap_pos hn
  have hDenPos :
      (0 : ℝ) < (qOneGap n : ℝ) * (3 : ℝ) ^ k := by
    positivity
  have hEPos : (0 : ℝ) < (qOneError n e : ℝ) := by
    unfold qOneError
    positivity
  have hFracPos :
      0 < (qOneError n e : ℝ) /
        ((qOneGap n : ℝ) * (3 : ℝ) ^ k) :=
    div_pos hEPos hDenPos
  exact Real.log_pos (by linarith)

/--
`log(1+x) ≤ x` を exact identity に適用し、`Λ` を誤差比 `E/(G·3^k)` で上から抑える。
-/
private theorem qOneLinearForm_le_error_ratio
    {k n e : ℕ}
    (hn : 0 < n)
    (hIdentity :
      (2 ^ n - 1) * 3 ^ k + 2 ^ n + e =
        2 ^ (Nat.log 2 (3 ^ k) + n)) :
    qOneLinearForm k n ≤
      (qOneError n e : ℝ) /
        ((qOneGap n : ℝ) * (3 : ℝ) ^ k) := by
  rw [qOneLinearForm_eq_log_one_add_ratio hn hIdentity]
  have hpos :
      (0 : ℝ) <
        1 + (qOneError n e : ℝ) /
          ((qOneGap n : ℝ) * (3 : ℝ) ^ k) := by
    have hGPos : 0 < qOneGap n := qOneGap_pos hn
    have hDenPos :
        (0 : ℝ) < (qOneGap n : ℝ) * (3 : ℝ) ^ k := by
      positivity
    have hEPos : (0 : ℝ) < (qOneError n e : ℝ) := by
      unfold qOneError
      positivity
    have hFracPos := div_pos hEPos hDenPos
    linarith
  simpa using Real.log_le_sub_one_of_pos hpos

/--
`G≥2^(n-1)`, `E≤4·2^n`, `2^M≤3^k` を合わせ、誤差比を `8/2^M` で抑える。
-/
private theorem qOneError_ratio_le_eight_div_twoPow
    {k n e : ℕ}
    (hn : 0 < n)
    (he : e ≤ 3) :
    (qOneError n e : ℝ) /
        ((qOneGap n : ℝ) * (3 : ℝ) ^ k) ≤
      8 / (2 : ℝ) ^ qOneMainExponent k := by
  have hGLower := qOneGap_lower hn
  have hELimit := qOneError_le_four_mul_twoPow (n := n) he
  have hMLower := twoPow_qOneMainExponent_le_threePow k
  have hGReal :
      (2 : ℝ) ^ (n - 1) ≤ (qOneGap n : ℝ) := by
    exact_mod_cast hGLower
  have hEReal :
      (qOneError n e : ℝ) ≤ 4 * (2 : ℝ) ^ n := by
    exact_mod_cast hELimit
  have hMReal :
      (2 : ℝ) ^ qOneMainExponent k ≤ (3 : ℝ) ^ k := by
    exact_mod_cast hMLower
  have hDenLower :
      (2 : ℝ) ^ (n - 1) * (2 : ℝ) ^ qOneMainExponent k ≤
        (qOneGap n : ℝ) * (3 : ℝ) ^ k := by
    exact mul_le_mul hGReal hMReal (by positivity) (by positivity)
  have hnPow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    rw [show n = (n - 1) + 1 by omega, pow_succ]
    ring_nf
    simp
  rw [hnPow] at hEReal
  have hNum :
      (qOneError n e : ℝ) ≤ 8 * (2 : ℝ) ^ (n - 1) := by
    nlinarith
  calc
    (qOneError n e : ℝ) /
          ((qOneGap n : ℝ) * (3 : ℝ) ^ k)
        ≤ (8 * (2 : ℝ) ^ (n - 1)) /
            ((2 : ℝ) ^ (n - 1) * (2 : ℝ) ^ qOneMainExponent k) := by
          exact div_le_div₀ (by positivity) hNum (by positivity) hDenLower
    _ = 8 / (2 : ℝ) ^ qOneMainExponent k := by field_simp

/--
linear form の positivity と誤差比評価から
`log Λ ≤ (3-M) log 2` を得る。
-/
private theorem qOneLinearForm_log_upper
    {k n e : ℕ}
    (hn : 0 < n)
    (he : e ≤ 3)
    (hIdentity :
      (2 ^ n - 1) * 3 ^ k + 2 ^ n + e =
        2 ^ (Nat.log 2 (3 ^ k) + n)) :
    Real.log (qOneLinearForm k n) ≤
      (3 - (qOneMainExponent k : ℝ)) * Real.log 2 := by
  have hΛPos := qOneLinearForm_pos hn hIdentity
  have hΛUpper0 := qOneLinearForm_le_error_ratio hn hIdentity
  have hFracUpper := qOneError_ratio_le_eight_div_twoPow (k := k) hn he
  have hΛUpper :
      qOneLinearForm k n ≤ 8 / (2 : ℝ) ^ qOneMainExponent k :=
    le_trans hΛUpper0 hFracUpper
  calc
    Real.log (qOneLinearForm k n)
        ≤ Real.log (8 / (2 : ℝ) ^ qOneMainExponent k) :=
      Real.log_le_log hΛPos hΛUpper
    _ = (3 - (qOneMainExponent k : ℝ)) * Real.log 2 := by
      rw [Real.log_div (by norm_num : (8 : ℝ) ≠ 0) (by positivity),
        show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow, Real.log_pow]
      ring

/-- `n≥3` なら Baker--Wüstholz の三つの基数 `2,G,3` はすべて正である。 -/
private theorem qOneAlpha_pos
    {n : ℕ}
    (hn : 3 ≤ n) :
    ∀ i, 0 < qOneAlpha n i := by
  intro i
  fin_cases i
  · norm_num [qOneAlpha]
  · dsimp [qOneAlpha]
    exact_mod_cast qOneGap_pos (by omega : 0 < n)
  · norm_num [qOneAlpha]

/--
`M≤2k` と `n≤log₂k+1≤k+1` から、三係数の絶対値を共通 bound `4k` で抑える。
-/
private theorem qOneCoeff_natAbs_le
    {k n : ℕ}
    (hk4 : 4 ≤ k)
    (hnLog : n ≤ Nat.log 2 k + 1) :
    ∀ i, (qOneCoeff k n i).natAbs ≤ 4 * k := by
  have hM2k := qOneMainExponent_le_two_mul k
  have hnK : n ≤ k + 1 := by
    calc
      n ≤ Nat.log 2 k + 1 := hnLog
      _ ≤ k + 1 :=
        Nat.add_le_add_right (Nat.log_le_self 2 k) 1
  have hMnB : qOneMainExponent k + n ≤ 4 * k := by omega
  intro i
  fin_cases i
  · change qOneMainExponent k + n ≤ 4 * k
    exact hMnB
  · simp [qOneCoeff]
    omega
  · simp [qOneCoeff]
    omega

/-- `qOneLinearForm` が Baker--Wüstholz に渡す三項和そのものであることを確認する。 -/
private theorem qOneLinearForm_eq_sum
    (k n : ℕ) :
    qOneLinearForm k n =
      ∑ i, (qOneCoeff k n i : ℝ) * Real.log (qOneAlpha n i : ℝ) := by
  rw [Fin.sum_univ_three]
  dsimp [qOneAlpha, qOneCoeff, qOneLinearForm, qOneMainExponent, qOneGap]
  push_cast
  ring

/-- `G=2^n-1` の modified height は `n log 2` 以下である。 -/
private theorem qOneGap_modifiedHeight_le
    {n : ℕ}
    (hn3 : 3 ≤ n) :
    BakerWustholz.modifiedHeight (Rat.castHom ℂ)
        (((qOneGap n : ℕ) : ℤ) : ℚ) ≤
      (n : ℝ) * Real.log 2 := by
  have hGPos : 0 < qOneGap n := qOneGap_pos (by omega)
  have hGOne : 1 ≤ qOneGap n := by omega
  have hGLe : qOneGap n ≤ 2 ^ n := by
    unfold qOneGap
    exact Nat.sub_le _ _
  have hGLeR : (qOneGap n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hGLe
  have hLogG : Real.log (qOneGap n : ℝ) ≤ (n : ℝ) * Real.log 2 := by
    calc
      Real.log (qOneGap n : ℝ) ≤ Real.log ((2 : ℝ) ^ n) :=
        Real.log_le_log (by exact_mod_cast hGPos) hGLeR
      _ = (n : ℝ) * Real.log 2 := by rw [Real.log_pow]
  have hOneLeNLog : (1 : ℝ) ≤ (n : ℝ) * Real.log 2 := by
    have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    nlinarith [Real.log_two_gt_d9]
  have hBase := mh_intCast (u := (qOneGap n : ℤ)) (by exact_mod_cast hGOne)
  exact le_trans hBase (max_le hLogG hOneLeNLog)

/--
三つの modified height の積を、可変なのが `G` だけであることを使って
`n log 2 log 3` 以下に抑える。
-/
private theorem qOneHeightProduct_le
    {n : ℕ}
    (hn3 : 3 ≤ n) :
    (∏ i, BakerWustholz.modifiedHeight (Rat.castHom ℂ) (qOneAlpha n i)) ≤
      (n : ℝ) * Real.log 2 * Real.log 3 := by
  rw [Fin.prod_univ_three]
  dsimp [qOneAlpha]
  have hMhG := qOneGap_modifiedHeight_le hn3
  have h12 :
      BakerWustholz.modifiedHeight (Rat.castHom ℂ) (2 : ℚ) *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ)
            (((qOneGap n : ℕ) : ℤ) : ℚ)
        ≤ 1 * ((n : ℝ) * Real.log 2) :=
    mul_le_mul mh_two hMhG (modifiedHeight_nonneg _) (by norm_num)
  have h3nonneg := modifiedHeight_nonneg (3 : ℚ)
  have hRightNonneg :
      0 ≤ (1 : ℝ) * ((n : ℝ) * Real.log 2) :=
    mul_nonneg (by norm_num) (mul_nonneg (by positivity) log_two_pos.le)
  have h := mul_le_mul h12 mh_three h3nonneg hRightNonneg
  simpa [mul_assoc] using h

/--
Baker--Wüstholz の 3-log 定理と height 積評価を合成し、
`log Λ` の共通下界を得る。
-/
private theorem qOneBW_log_lower
    {k n : ℕ}
    (hk4 : 4 ≤ k)
    (hn3 : 3 ≤ n)
    (hnLog : n ≤ Nat.log 2 k + 1)
    (hΛPos : 0 < qOneLinearForm k n) :
    -(BakerWustholz.C 3 1 * max (Real.log (4 * k)) 1 *
        ((n : ℝ) * Real.log 2 * Real.log 3)) ≤
      Real.log (qOneLinearForm k n) := by
  have hB2 : 2 ≤ 4 * k := by omega
  have hBW :=
    log_linearForm_rat_ge (n := 3) (by norm_num)
      (qOneAlpha n) (qOneAlpha_pos hn3) (qOneCoeff k n)
      (B := 4 * k) hB2 (qOneCoeff_natAbs_le hk4 hnLog)
      (qOneLinearForm_eq_sum k n) hΛPos.ne'
  have hProd := qOneHeightProduct_le hn3
  have hCNonneg : 0 ≤ BakerWustholz.C 3 1 :=
    C_one_nonneg 3
  have hHNonneg : 0 ≤ max (Real.log (4 * k)) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  have hScaleNonneg :
      0 ≤ BakerWustholz.C 3 1 * max (Real.log (4 * k)) 1 :=
    mul_nonneg hCNonneg hHNonneg
  have hMul := mul_le_mul_of_nonneg_left hProd hScaleNonneg
  have hNeg := neg_le_neg hMul
  exact le_trans (by simpa [mul_assoc] using hNeg) hBW

/--
linear form の解析上界と Baker--Wüstholz 下界を比較し、
主指数 `M` に対する実数不等式を得る。
-/
private theorem qOneMainExponent_real_bound
    {k n e : ℕ}
    (hk4 : 4 ≤ k)
    (hn3 : 3 ≤ n)
    (he : e ≤ 3)
    (hnLog : n ≤ Nat.log 2 k + 1)
    (hIdentity :
      (2 ^ n - 1) * 3 ^ k + 2 ^ n + e =
        2 ^ (Nat.log 2 (3 ^ k) + n)) :
    (qOneMainExponent k : ℝ) - 3 ≤
      BakerWustholz.C 3 1 * Real.log 3 *
        max (Real.log (4 * k)) 1 * (n : ℝ) := by
  have hΛPos := qOneLinearForm_pos (by omega : 0 < n) hIdentity
  have hLogΛUpper :=
    qOneLinearForm_log_upper (k := k) (by omega : 0 < n) he hIdentity
  have hBWCoarse := qOneBW_log_lower hk4 hn3 hnLog hΛPos
  have hCombined := le_trans hBWCoarse hLogΛUpper
  have hlog2pos := log_two_pos
  have hFactored :
      ((qOneMainExponent k : ℝ) - 3) * Real.log 2 ≤
        (BakerWustholz.C 3 1 * Real.log 3 *
          max (Real.log (4 * k)) 1 * (n : ℝ)) * Real.log 2 := by
    nlinarith
  nlinarith [hFactored, hlog2pos]

/-- `z=floor(log₂k)` を使って `log(4k) ≤ z+3` と粗く評価する。 -/
private theorem qOneLog_four_mul_le
    {k : ℕ}
    (hk4 : 4 ≤ k) :
    Real.log ((4 : ℝ) * (k : ℝ)) ≤
      ((qOneLogDepth k + 3 : ℕ) : ℝ) := by
  have hkPowUpper : k < 2 ^ (qOneLogDepth k + 1) := by
    unfold qOneLogDepth
    exact Nat.lt_pow_succ_log_self (by norm_num) k
  have hFourK : 4 * k < 2 ^ (qOneLogDepth k + 3) := by
    calc
      4 * k < 4 * 2 ^ (qOneLogDepth k + 1) :=
        (Nat.mul_lt_mul_left (by norm_num : 0 < (4 : ℕ))).2 hkPowUpper
      _ = 2 ^ (qOneLogDepth k + 3) := by
        rw [show qOneLogDepth k + 3 = (qOneLogDepth k + 1) + 2 by omega,
          pow_add]
        norm_num
        ring
  have hCast :
      (4 : ℝ) * (k : ℝ) < (2 : ℝ) ^ (qOneLogDepth k + 3) := by
    exact_mod_cast hFourK
  have hLogLt :
      Real.log ((4 : ℝ) * (k : ℝ)) <
        Real.log ((2 : ℝ) ^ (qOneLogDepth k + 3)) := by
    exact Real.log_lt_log (by positivity) hCast
  rw [Real.log_pow] at hLogLt
  have hMul :
      ((qOneLogDepth k + 3 : ℕ) : ℝ) * Real.log 2 ≤
        ((qOneLogDepth k + 3 : ℕ) : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left log_two_le_one
      (by positivity : (0 : ℝ) ≤ ((qOneLogDepth k + 3 : ℕ) : ℝ))
  linarith

/-- `B=4k` に対する Baker--Wüstholz の height parameter は `z+3` 以下である。 -/
private theorem qOneHeightParameter_le
    {k : ℕ}
    (hk4 : 4 ≤ k) :
    max (Real.log ((4 : ℝ) * (k : ℝ))) 1 ≤
      ((qOneLogDepth k + 3 : ℕ) : ℝ) := by
  apply max_le
  · exact qOneLog_four_mul_le hk4
  · exact_mod_cast (by omega : 1 ≤ qOneLogDepth k + 3)

/--
実数 bound を `z=floor(log₂k)` の二次式へ粗視化し、
`M ≤ qOnePoly z` を得る。
-/
private theorem qOneMainExponent_le_poly
    {k n : ℕ}
    (hk4 : 4 ≤ k)
    (hnLog : n ≤ Nat.log 2 k + 1)
    (hMainReal :
      (qOneMainExponent k : ℝ) - 3 ≤
        BakerWustholz.C 3 1 * Real.log 3 *
          max (Real.log (4 * k)) 1 * (n : ℝ)) :
    qOneMainExponent k ≤ qOnePoly (qOneLogDepth k) := by
  have hHNonneg : 0 ≤ max (Real.log (4 * k)) 1 :=
    le_trans zero_le_one (le_max_right _ _)
  have hH := qOneHeightParameter_le hk4
  have hnZ : n ≤ qOneLogDepth k + 1 := by
    simpa [qOneLogDepth] using hnLog
  have hC := C_three_mul_log_three_le
  have hMainCoarse :
      (qOneMainExponent k : ℝ) - 3 ≤
        (8000000000000 : ℝ) *
          (qOneLogDepth k + 3 : ℕ) * (qOneLogDepth k + 1 : ℕ) := by
    calc
      (qOneMainExponent k : ℝ) - 3 ≤
          (BakerWustholz.C 3 1 * Real.log 3) *
            max (Real.log (4 * k)) 1 * (n : ℝ) := hMainReal
      _ ≤ (8000000000000 : ℝ) *
            max (Real.log (4 * k)) 1 * (n : ℝ) := by
          have hr := mul_le_mul_of_nonneg_right hC
            (mul_nonneg hHNonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)))
          simpa [mul_assoc] using hr
      _ ≤ (8000000000000 : ℝ) *
            (qOneLogDepth k + 3 : ℕ) * (n : ℝ) := by
          have hh := mul_le_mul_of_nonneg_left hH
            (by norm_num : (0 : ℝ) ≤ 8000000000000)
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
          exact mul_le_mul_of_nonneg_right hh hn0
      _ ≤ (8000000000000 : ℝ) *
            (qOneLogDepth k + 3 : ℕ) * (qOneLogDepth k + 1 : ℕ) := by
          have hnZR : (n : ℝ) ≤ (qOneLogDepth k + 1 : ℕ) := by
            exact_mod_cast hnZ
          exact mul_le_mul_of_nonneg_left hnZR
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8000000000000) (by positivity))
  have hMain' :
      (qOneMainExponent k : ℝ) ≤
        (qOnePoly (qOneLogDepth k) : ℝ) := by
    have hMainCoarse' := hMainCoarse
    push_cast at hMainCoarse'
    dsimp [qOnePoly]
    push_cast
    linarith
  exact_mod_cast hMain'

/--
q=1 exact identity と valuation の logarithmic width bound から `k<10^23`。

証明本体では、前段で分離した5段階
「linear form 上界 → BW 下界 → `M` の実数評価 → 二次式評価 → 指数関数による支配」
だけを接続する。`e=1` が A、`e=3` が C に対応する。
-/
private theorem qOne_depth_lt_of_threeLogIdentity
    {k n e : ℕ}
    (hk4 : 4 ≤ k)
    (hn3 : 3 ≤ n)
    (he : e ≤ 3)
    (hnLog : n ≤ Nat.log 2 k + 1)
    (hIdentity :
      (2 ^ n - 1) * 3 ^ k + 2 ^ n + e =
        2 ^ (Nat.log 2 (3 ^ k) + n)) :
    k < targetOneQOneInternalDepthBound := by
  have hMainReal :=
    qOneMainExponent_real_bound hk4 hn3 he hnLog hIdentity
  have hMPoly :=
    qOneMainExponent_le_poly hk4 hnLog hMainReal
  by_contra hNot
  have hkBig : targetOneQOneInternalDepthBound ≤ k := by omega
  have hz76 : 76 ≤ qOneLogDepth k := by
    apply Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ))
    have hBase : 2 ^ 76 ≤ targetOneQOneInternalDepthBound := by
      norm_num [targetOneQOneInternalDepthBound]
    exact le_trans hBase hkBig
  have hPolyExp := qOnePoly_lt_twoPow hz76
  have hPowLeK : 2 ^ qOneLogDepth k ≤ k := by
    unfold qOneLogDepth
    exact Nat.pow_log_le_self 2 (by omega : k ≠ 0)
  have hkLeM : k ≤ qOneMainExponent k := by
    unfold qOneMainExponent
    apply Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ))
    exact Nat.pow_le_pow_left (by norm_num : (2 : ℕ) ≤ 3) k
  omega

/-! ## A/C の解析 bound -/

/-- A (`even,q=1`) は three-log identity から `k<10^23`。 -/
theorem TargetOneHoleGeometricData.even_q_one_internal_depth_bound
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hq : h.q = 1) :
    k < targetOneQOneInternalDepthBound := by
  have hkEven' : Even k := (Nat.even_iff).2 hkEven
  have hWidth := h.even_q_one_width_eq (by omega) hkEven' (by omega) hqt hq
  have hnLog : n ≤ Nat.log 2 k + 1 := by
    rw [hWidth]
    have hv := padicValNat_le_nat_log (p := 2) k
    omega
  apply qOne_depth_lt_of_threeLogIdentity hk hn (by norm_num : 1 ≤ 3) hnLog
  exact h.even_q_one_threeLogIdentity (by omega) hqt hq

/-- C (`odd,q=1`) も three-log identity から `k<10^23`。 -/
theorem TargetOneHoleGeometricData.odd_q_one_internal_depth_bound
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hq : h.q = 1) :
    k < targetOneQOneInternalDepthBound := by
  have hWidth := h.odd_q_one_width_eq (by omega) hkOdd (by omega) hqt hq
  have hnLog : n ≤ Nat.log 2 k + 1 := by
    rw [hWidth]
    have hv := padicValNat_le_nat_log (p := 2) (k - 1)
    have hlogmono : Nat.log 2 (k - 1) ≤ Nat.log 2 k :=
      Nat.log_mono_right (by omega)
    omega
  apply qOne_depth_lt_of_threeLogIdentity hk hn (by norm_num : 3 ≤ 3) hnLog
  exact h.odd_q_one_threeLogIdentity (by omega) hqt hq

/-! ## M₄ bounded finite certificate -/

private def qOneLhs (K N : ℕ) : ZMod oneHoleThreeTailModulus :=
  (3 : ZMod oneHoleThreeTailModulus) ^ K *
    ((2 : ZMod oneHoleThreeTailModulus) ^ N - 1)

private def qOneRhs (r N L : ℕ) : ZMod oneHoleThreeTailModulus :=
  (2 : ZMod oneHoleThreeTailModulus) ^ r *
    ((2 : ZMod oneHoleThreeTailModulus) ^ L - 1 -
      (2 : ZMod oneHoleThreeTailModulus) ^ (N - r)) + 1

/--
`N` と residue を一つの自然数 key に束ねる。

`native_decide` の内側で N ごとの HashSet を作り直さないための
meet-in-the-middle 用 encoding。residue は常に modulus 未満なので injective。
-/
private def qOneKey (N v : ℕ) : ℕ :=
  N * oneHoleThreeTailModulus + v

/--
固定 `r` に対して到達可能な `(N,L)` 側を一度だけ table 化する。

`78 * 486 = 37908` state。A/C でそれぞれ一個の table を共有する。
-/
private def qOneRhsAllList (r : ℕ) : List ℕ :=
  (List.range 78).flatMap fun N =>
    (List.range 486).map fun L =>
      qOneKey N (qOneRhs r N L).val

private def qOneRhsAllSet (r : ℕ) : Std.HashSet ℕ :=
  Std.HashSet.ofList (qOneRhsAllList r)

/-- `qOneRhsAllSet` が各 `N<78, L<486` の RHS residue を実際に含むことを保証する。 -/
private theorem qOneRhsAllSet_contains
    (r : ℕ)
    (N : Fin 78)
    (L : Fin 486) :
    (qOneRhsAllSet r).contains
        (qOneKey N.1 (qOneRhs r N.1 L.1).val) = true := by
  have hMem :
      qOneKey N.1 (qOneRhs r N.1 L.1).val ∈ qOneRhsAllList r := by
    unfold qOneRhsAllList
    apply List.mem_flatMap.mpr
    refine ⟨N.1, List.mem_range.mpr N.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨L.1, List.mem_range.mpr L.2, rfl⟩
  simpa only [qOneRhsAllSet, Std.HashSet.contains_ofList,
    List.contains_eq_mem, decide_eq_true_eq] using hMem

/-- A の M₄ certificate。`L` を自由にしても survivor は 0。 -/
private theorem even_q_one_m4_finite_sieve :
    ∀ K : Fin 978,
      ∀ N : Fin 78,
        4 ≤ K.1 →
        3 ≤ N.1 →
        K.1 % 4 = 0 →
        (qOneRhsAllSet 1).contains
          (qOneKey N.1 (qOneLhs K.1 N.1).val) = false := by
  native_decide

/-- C の M₄ certificate。`L` を自由にしても survivor は 0。 -/
private theorem odd_q_one_m4_finite_sieve :
    ∀ K : Fin 978,
      ∀ N : Fin 78,
        4 ≤ K.1 →
        3 ≤ N.1 →
        K.1 % 4 = 1 →
        (qOneRhsAllSet 2).contains
          (qOneKey N.1 (qOneLhs K.1 N.1).val) = false := by
  native_decide

/-- 3 の tail-loop representative は mod 4 では元の指数 `k` と一致する。 -/
private theorem threeTailRep_mod_four (k : ℕ) :
    tailLoopExponent 6 972 k % 4 = k % 4 := by
  unfold tailLoopExponent
  split
  · rfl
  · rename_i h
    have hk6 : 6 ≤ k := Nat.le_of_not_gt h
    have hmod : ((k - 6) % 972) % 4 = (k - 6) % 4 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [Nat.add_mod, hmod]
    omega

/-- `k≥4` なら 3 の tail-loop representative も少なくとも 4 である。 -/
private theorem four_le_threeTailRep
    {k : ℕ}
    (hk : 4 ≤ k) :
    4 ≤ tailLoopExponent 6 972 k := by
  unfold tailLoopExponent
  split <;> omega

/-- A 側では解析 depth bound と 2-adic valuation lock から width `n<78` を得る。 -/
private theorem qOne_width_lt_78_even
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hq : h.q = 1)
    (hBound : k < targetOneQOneInternalDepthBound) :
    n < 78 := by
  have hWidth :=
    h.even_q_one_width_eq (by omega) ((Nat.even_iff).2 hkEven) (by omega) hqt hq
  by_contra hNot
  have hv : 77 ≤ padicValNat 2 k := by omega
  have hdvd : 2 ^ 77 ∣ k :=
    (padicValNat_dvd_iff_le (p := 2) (a := k) (n := 77) (by omega)).2 hv
  have hle : 2 ^ 77 ≤ k := Nat.le_of_dvd (by omega) hdvd
  have hcut : targetOneQOneInternalDepthBound < 2 ^ 77 := by
    norm_num [targetOneQOneInternalDepthBound]
  omega

/-- C 側でも解析 depth bound と 2-adic valuation lock から width `n<78` を得る。 -/
private theorem qOne_width_lt_78_odd
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hq : h.q = 1)
    (hBound : k < targetOneQOneInternalDepthBound) :
    n < 78 := by
  have hWidth := h.odd_q_one_width_eq (by omega) hkOdd (by omega) hqt hq
  by_contra hNot
  have hv : 78 ≤ padicValNat 2 (k - 1) := by omega
  have hdvd : 2 ^ 78 ∣ k - 1 :=
    (padicValNat_dvd_iff_le (p := 2) (a := k - 1) (n := 78) (by omega)).2 hv
  have hle : 2 ^ 78 ≤ k - 1 := Nat.le_of_dvd (by omega) hdvd
  have hcut : targetOneQOneInternalDepthBound < 2 ^ 78 := by
    norm_num [targetOneQOneInternalDepthBound]
  omega

/-- A の bounded residual は既存 M₄ finite certificate で内部排除。 -/
theorem TargetOneHoleGeometricData.even_q_one_internal_finite_sieve
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hq : h.q = 1)
    (hBound : k < targetOneQOneInternalDepthBound) :
    False := by
  have hn78 := qOne_width_lt_78_even h hk hn hkEven hqt hq hBound
  have hWidth :=
    h.even_q_one_width_eq (by omega) ((Nat.even_iff).2 hkEven) (by omega) hqt hq
  have hv2 : 2 ≤ padicValNat 2 k := by omega
  have h4dvd : 4 ∣ k := by
    simpa using
      (padicValNat_dvd_iff_le (p := 2) (a := k) (n := 2) (by omega)).2 hv2
  have hk4 : k % 4 = 0 := Nat.dvd_iff_mod_eq_zero.mp h4dvd
  have hTarget := h.toTargetOneHoleEquation_of_q_one hq
  have hRed := (hTarget.to_mod oneHoleThreeTailModulus).reduce_tailLoop
    pow23TailLoops_oneHoleThreeTail
  have hb : b = n - 1 := by
    have hb0 := h.b_add_r_eq
    rw [hq] at hb0
    norm_num at hb0
    omega
  let K : ℕ := tailLoopExponent 6 972 k
  have hKlt : K < 978 := by
    dsimp [K]
    have ht := powTailLoop_three_oneHoleThreeTail.tailLoopExponent_lt (e := k)
    norm_num at ht ⊢
    exact ht
  have hK4 : 4 ≤ K := by
    dsimp [K]
    exact four_le_threeTailRep hk
  have hKmod : K % 4 = 0 := by
    dsimp [K]
    rw [threeTailRep_mod_four, hk4]
  let Kf : Fin 978 := ⟨K, hKlt⟩
  let Nf : Fin 78 := ⟨n, hn78⟩
  let Lf : Fin 486 := ⟨L % 486, Nat.mod_lt _ (by norm_num)⟩
  have hn486 : n < 486 := by omega
  have hb486 : b < 486 := by omega
  have hnRep : tailLoopExponent 0 486 n = n := by
    simp [tailLoopExponent, Nat.mod_eq_of_lt hn486]
  have hrRep : tailLoopExponent 0 486 1 = 1 := by
    norm_num [tailLoopExponent]
  have hLRep : tailLoopExponent 0 486 L = L % 486 := by
    simp [tailLoopExponent]
  have hbRep : tailLoopExponent 0 486 b = b := by
    simp [tailLoopExponent, Nat.mod_eq_of_lt hb486]
  rw [hnRep, hrRep, hLRep, hbRep, hb] at hRed
  have hEqFinite :
      qOneLhs Kf.1 Nf.1 = qOneRhs 1 Nf.1 Lf.1 := by
    dsimp [Kf, Nf, Lf]
    unfold TargetOneHoleModEquation at hRed
    unfold qOneLhs qOneRhs
    simpa [K] using hRed
  have hEqVal := congrArg ZMod.val hEqFinite
  have hMem :
      (qOneRhsAllSet 1).contains
        (qOneKey Nf.1 (qOneLhs Kf.1 Nf.1).val) = true := by
    rw [hEqVal]
    exact qOneRhsAllSet_contains 1 Nf Lf
  have hNo := even_q_one_m4_finite_sieve Kf Nf hK4 hn hKmod
  rw [hMem] at hNo
  cases hNo

/-- C の bounded residual も既存 M₄ finite certificate で内部排除。 -/
theorem TargetOneHoleGeometricData.odd_q_one_internal_finite_sieve
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hq : h.q = 1)
    (hBound : k < targetOneQOneInternalDepthBound) :
    False := by
  have hn78 := qOne_width_lt_78_odd h hk hn hkOdd hqt hq hBound
  have hWidth := h.odd_q_one_width_eq (by omega) hkOdd (by omega) hqt hq
  have hv2 : 2 ≤ padicValNat 2 (k - 1) := by omega
  have h4dvd : 4 ∣ k - 1 := by
    simpa using
      (padicValNat_dvd_iff_le (p := 2) (a := k - 1) (n := 2) (by omega)).2 hv2
  rcases h4dvd with ⟨u, hu⟩
  have hk4 : k % 4 = 1 := by
    have hkForm : k = 4 * u + 1 := by omega
    rw [hkForm]
    simp
  have hTarget := h.toTargetOneHoleEquation_of_q_one hq
  have hRed := (hTarget.to_mod oneHoleThreeTailModulus).reduce_tailLoop
    pow23TailLoops_oneHoleThreeTail
  have hb : b = n - 2 := by
    have hb0 := h.b_add_r_eq
    rw [hq] at hb0
    norm_num at hb0
    omega
  let K : ℕ := tailLoopExponent 6 972 k
  have hKlt : K < 978 := by
    dsimp [K]
    have ht := powTailLoop_three_oneHoleThreeTail.tailLoopExponent_lt (e := k)
    norm_num at ht ⊢
    exact ht
  have hK4 : 4 ≤ K := by
    dsimp [K]
    exact four_le_threeTailRep hk
  have hKmod : K % 4 = 1 := by
    dsimp [K]
    rw [threeTailRep_mod_four, hk4]
  let Kf : Fin 978 := ⟨K, hKlt⟩
  let Nf : Fin 78 := ⟨n, hn78⟩
  let Lf : Fin 486 := ⟨L % 486, Nat.mod_lt _ (by norm_num)⟩
  have hn486 : n < 486 := by omega
  have hb486 : b < 486 := by omega
  have hnRep : tailLoopExponent 0 486 n = n := by
    simp [tailLoopExponent, Nat.mod_eq_of_lt hn486]
  have hrRep : tailLoopExponent 0 486 2 = 2 := by
    norm_num [tailLoopExponent]
  have hLRep : tailLoopExponent 0 486 L = L % 486 := by
    simp [tailLoopExponent]
  have hbRep : tailLoopExponent 0 486 b = b := by
    simp [tailLoopExponent, Nat.mod_eq_of_lt hb486]
  rw [hnRep, hrRep, hLRep, hbRep, hb] at hRed
  have hEqFinite :
      qOneLhs Kf.1 Nf.1 = qOneRhs 2 Nf.1 Lf.1 := by
    dsimp [Kf, Nf, Lf]
    unfold TargetOneHoleModEquation at hRed
    unfold qOneLhs qOneRhs
    simpa [K] using hRed
  have hEqVal := congrArg ZMod.val hEqFinite
  have hMem :
      (qOneRhsAllSet 2).contains
        (qOneKey Nf.1 (qOneLhs Kf.1 Nf.1).val) = true := by
    rw [hEqVal]
    exact qOneRhsAllSet_contains 2 Nf Lf
  have hNo := odd_q_one_m4_finite_sieve Kf Nf hK4 hn hKmod
  rw [hMem] at hNo
  cases hNo

/-! ## A/C 最終無条件 closure -/

/-- A (`even,q=1`) は外部 package なしで不可能。 -/
theorem TargetOneHoleGeometricData.even_q_one_impossible_internal
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 1 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkEven : k % 2 = 0)
    (hqt : h.q < h.t)
    (hq : h.q = 1) :
    False := by
  have hBound := h.even_q_one_internal_depth_bound hk hn hkEven hqt hq
  exact h.even_q_one_internal_finite_sieve hk hn hkEven hqt hq hBound

/-- C (`odd,q=1`) も外部 package なしで不可能。 -/
theorem TargetOneHoleGeometricData.odd_q_one_impossible_internal
    {k n L b : ℕ}
    (h : TargetOneHoleGeometricData k n 2 L b)
    (hk : 4 ≤ k)
    (hn : 3 ≤ n)
    (hkOdd : k % 2 = 1)
    (hqt : h.q < h.t)
    (hq : h.q = 1) :
    False := by
  have hBound := h.odd_q_one_internal_depth_bound hk hn hkOdd hqt hq
  exact h.odd_q_one_internal_finite_sieve hk hn hkOdd hqt hq hBound

end Mersenne
end Collatz3
