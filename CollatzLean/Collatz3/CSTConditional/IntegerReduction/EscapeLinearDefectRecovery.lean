import CollatzLean.Collatz3.CSTConditional.IntegerReduction.EscapeRecordReconstruction
import CollatzLean.Collatz3.CSTConditional.IntegerReduction.ExponentialEscapeReduction
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Collatz3 CSTConditional IntegerReduction: Problem E から linear defect を回収

Work 側の独立整数問題の最後の逆向きを閉じる。

すでに

* `HasExponentialEscape y` から `coefficientScale e m → 0`、
* finite shift 後の一意な admissible decomposition の再構成、

までは得られている。

このファイルではさらに、recurrence の correction product が一様有界であることを
整数冪の上界へ戻し、admissible decomposition が与える Beatty roof と比較することで

`m ≤ K * streamDefect(e,m)`

を十分大きい全時刻で回収する。

従って特に reconstructed boundary 上でも

`F_n ≤ K * boundaryDefect(r,n)`

が成立する。

逆に admissible decomposition とこの exact linear defect lower bound があれば、
既存の `2^streamDefect < y_m` から Problem E 型指数逃走が戻る。

actual orbit / Global CST は使わない。
-/

namespace Collatz3
namespace IntegerReduction

open Filter
open scoped BigOperators Topology

/-- 自然数 `n` は `2^n` 以下。実数定数を 2 冪で覆うための初等補題。 -/
theorem nat_le_twoPow_self
    (n : ℕ) :
    n ≤ 2 ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ]
      have hPos : 1 ≤ 2 ^ n := by
        have h : 0 < (2 : ℕ) ^ n := pow_pos (by omega) n
        omega
      omega

/-- 許容分解があれば、全時刻の prefix depth は absolute Beatty roof 以下。 -/
theorem prefixDepth_le_beattyIndex_all
    {e r : ℕ → ℕ}
    (hDec : IsAdmissibleDecomposition e r)
    (m : ℕ) :
    prefixDepth e m ≤ Critical.beattyIndex m := by
  obtain ⟨n, t, ht, hm⟩ := hDec.exists_blockLocation m
  rw [hm]
  exact
    prefixDepth_le_beattyIndex_of_admissibleDecomposition
      hDec n t (Nat.le_of_lt ht)

/-- 許容分解上では Beatty index は prefix depth と pure defect に exact に分解する。 -/
theorem beattyIndex_eq_prefixDepth_add_streamDefect
    {e r : ℕ → ℕ}
    (hDec : IsAdmissibleDecomposition e r)
    (m : ℕ) :
    Critical.beattyIndex m =
      prefixDepth e m + streamDefect e m := by
  have hRoof := prefixDepth_le_beattyIndex_all hDec m
  unfold streamDefect
  omega

/-- Problem E 型指数逃走は finite shift 後にも保存される。 -/
theorem HasExponentialEscape.shift
    {y : ℕ → ℕ}
    (hEscape : HasExponentialEscape y)
    (start : ℕ) :
    HasExponentialEscape (shiftSeq y start) := by
  obtain ⟨L, M, hL, hMain⟩ := hEscape
  refine ⟨L, M, hL, ?_⟩
  intro m hm
  have hOrig := hMain (start + m) (by omega)
  have hDiv : m / L ≤ (start + m) / L := by
    exact Nat.div_le_div_right (Nat.le_add_left m start)
  have hPow : 2 ^ (m / L) ≤ 2 ^ ((start + m) / L) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDiv
  dsimp [shiftSeq]
  exact le_trans hPow hOrig

/--
Problem E の下では normalized numerator

`2^D_m * y_m`

は `2^A * 3^m` で一様に上から抑えられるような自然数 `A` が存在する。

recurrence の exact correction-product 恒等式と
`∏(1+u_i) ≤ exp(Σu_i)` だけを使う。
-/
theorem exists_normalizedNumerator_pow_bound_of_exponentialEscape
    {e y : ℕ → ℕ}
    (hRun : RunsOddRecurrence e y)
    (hEscape : HasExponentialEscape y) :
    ∃ A : ℕ,
      ∀ m : ℕ,
        2 ^ prefixDepth e m * y m <
          2 ^ A * 3 ^ m := by
  have hSum := summable_reciprocal_of_exponentialEscape hEscape
  let C : ℝ :=
    (y 0 : ℝ) * Real.exp (∑' i : ℕ, 1 / (3 * (y i : ℝ)))
  obtain ⟨A, hA⟩ := exists_nat_gt C
  have hAle : A ≤ 2 ^ A := nat_le_twoPow_self A
  have hAleR : (A : ℝ) ≤ (2 : ℝ) ^ A := by
    exact_mod_cast hAle
  have hCLt : C < (2 : ℝ) ^ A :=
    lt_of_lt_of_le hA hAleR
  refine ⟨A, ?_⟩
  intro m
  have hIdentity := coefficientScale_mul_value_eq_correctionProduct hRun m
  have hProd := correctionProduct_le_exp_tsum hSum m
  have hy0Nonneg : 0 ≤ (y 0 : ℝ) := by positivity
  have hScaleLeC :
      coefficientScale e m * (y m : ℝ) ≤ C := by
    rw [hIdentity]
    dsimp [C]
    exact mul_le_mul_of_nonneg_left hProd hy0Nonneg
  have hScaleLt :
      coefficientScale e m * (y m : ℝ) < (2 : ℝ) ^ A :=
    lt_of_le_of_lt hScaleLeC hCLt
  have hDenPos : 0 < (3 : ℝ) ^ m := by positivity
  have hDivLt :
      ((2 : ℝ) ^ prefixDepth e m * (y m : ℝ)) /
          (3 : ℝ) ^ m <
        (2 : ℝ) ^ A := by
    calc
      ((2 : ℝ) ^ prefixDepth e m * (y m : ℝ)) /
          (3 : ℝ) ^ m
          = coefficientScale e m * (y m : ℝ) := by
              unfold coefficientScale
              ring
      _ < (2 : ℝ) ^ A := hScaleLt
  have hCrossR :
      (2 : ℝ) ^ prefixDepth e m * (y m : ℝ) <
        (2 : ℝ) ^ A * (3 : ℝ) ^ m :=
    (div_lt_iff₀ hDenPos).1 hDivLt
  exact_mod_cast hCrossR

/--
Problem E と admissible decomposition から、まず additive `+1` 付きの linear defect bound を得る。

ある `K₀>0` と十分遅い時刻以降で

`m ≤ K₀ * (streamDefect(e,m)+1)`。
-/
theorem exists_eventual_streamLinearDefect_add_one_of_exponentialEscape
    {e y r : ℕ → ℕ}
    (hDec : IsAdmissibleDecomposition e r)
    (hRun : RunsOddRecurrence e y)
    (hEscape : HasExponentialEscape y) :
    ∃ K₀ R : ℕ,
      0 < K₀ ∧
        ∀ m : ℕ, R ≤ m →
          m ≤ K₀ * (streamDefect e m + 1) := by
  obtain ⟨A, hNumerator⟩ :=
    exists_normalizedNumerator_pow_bound_of_exponentialEscape hRun hEscape
  obtain ⟨L, M, hL, hEscapeMain⟩ := hEscape
  let K₀ : ℕ := L * (A + 1)
  have hK₀ : 0 < K₀ := by
    dsimp [K₀]
    positivity
  refine ⟨K₀, M, hK₀, ?_⟩
  intro m hm
  let D : ℕ := prefixDepth e m
  let d : ℕ := streamDefect e m
  let b : ℕ := Critical.beattyIndex m
  let q : ℕ := m / L
  have hY : 2 ^ q ≤ y m := by
    dsimp [q]
    exact hEscapeMain m hm
  have hNum :
      2 ^ D * y m < 2 ^ A * 3 ^ m := by
    simpa [D] using hNumerator m
  have hLeft :
      2 ^ (D + q) ≤ 2 ^ D * y m := by
    rw [pow_add]
    exact Nat.mul_le_mul_left (2 ^ D) hY
  have hBeatUpper :
      3 ^ m < 2 ^ (b + 1) := by
    dsimp [b]
    simpa [Critical.criticalTwoDepth] using
      Critical.threePow_lt_twoPow_criticalTwoDepth m
  have hApos : 0 < 2 ^ A := by positivity
  have hRight :
      2 ^ A * 3 ^ m < 2 ^ A * 2 ^ (b + 1) :=
    (Nat.mul_lt_mul_left hApos).2 hBeatUpper
  have hPowLt :
      2 ^ (D + q) < 2 ^ (A + b + 1) := by
    calc
      2 ^ (D + q) ≤ 2 ^ D * y m := hLeft
      _ < 2 ^ A * 3 ^ m := hNum
      _ < 2 ^ A * 2 ^ (b + 1) := hRight
      _ = 2 ^ (A + b + 1) := by
        rw [← pow_add]
        congr 1
  have hExpLt : D + q < A + b + 1 := by
    by_contra hNot
    have hLe : A + b + 1 ≤ D + q := by omega
    have hPowLe :
        2 ^ (A + b + 1) ≤ 2 ^ (D + q) :=
      Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hLe
    omega
  have hDefectEq : b = D + d := by
    dsimp [b, D, d]
    exact beattyIndex_eq_prefixDepth_add_streamDefect hDec m
  have hq : q ≤ A + d := by
    rw [hDefectEq] at hExpLt
    omega
  have hMod : m % L < L := Nat.mod_lt m hL
  have hDivMod : m = q * L + m % L := by
    dsimp [q]
    simpa [Nat.mul_comm] using (Nat.div_add_mod m L).symm
  have hmLt : m < (q + 1) * L := by
    rw [hDivMod, Nat.add_mul, one_mul]
    omega
  have hqOne : q + 1 ≤ A + d + 1 := by omega
  have hMul : (q + 1) * L ≤ (A + d + 1) * L :=
    Nat.mul_le_mul_right L hqOne
  have hFactor : A + d + 1 ≤ (A + 1) * (d + 1) := by
    nlinarith
  have hFactorMul :
      (A + d + 1) * L ≤ ((A + 1) * (d + 1)) * L :=
    Nat.mul_le_mul_right L hFactor
  have hFinal : m < K₀ * (d + 1) := by
    calc
      m < (q + 1) * L := hmLt
      _ ≤ (A + d + 1) * L := hMul
      _ ≤ ((A + 1) * (d + 1)) * L := hFactorMul
      _ = K₀ * (d + 1) := by
        dsimp [K₀]
        ring
  exact Nat.le_of_lt hFinal

/--
`+1` を sufficiently late に吸収し、Problem E から exact な linear defect lower bound を回収する。

ある `K>0, R` が存在して、全 `m≥R` で

`m ≤ K * streamDefect(e,m)`。
-/
theorem exists_eventual_streamLinearDefect_of_exponentialEscape
    {e y r : ℕ → ℕ}
    (hDec : IsAdmissibleDecomposition e r)
    (hRun : RunsOddRecurrence e y)
    (hEscape : HasExponentialEscape y) :
    ∃ K R : ℕ,
      0 < K ∧
        ∀ m : ℕ, R ≤ m →
          m ≤ K * streamDefect e m := by
  obtain ⟨K₀, R₀, hK₀, hAdd⟩ :=
    exists_eventual_streamLinearDefect_add_one_of_exponentialEscape
      hDec hRun hEscape
  let K : ℕ := 2 * K₀
  let R : ℕ := max R₀ (K₀ + 1)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, R, hK, ?_⟩
  intro m hm
  have hmR₀ : R₀ ≤ m := by
    dsimp [R] at hm
    omega
  have hmK : K₀ + 1 ≤ m := by
    dsimp [R] at hm
    omega
  have hMain := hAdd m hmR₀
  let d : ℕ := streamDefect e m
  have hdPos : 0 < d := by
    by_contra hNot
    have hdZero : d = 0 := by omega
    have hdZero' : streamDefect e m = 0 := by
      simpa [d] using hdZero
    rw [hdZero'] at hMain
    simp at hMain
    omega
  have hTwo : d + 1 ≤ 2 * d := by omega
  have hMul : K₀ * (d + 1) ≤ K₀ * (2 * d) :=
    Nat.mul_le_mul_left K₀ hTwo
  calc
    m ≤ K₀ * (d + 1) := hMain
    _ ≤ K₀ * (2 * d) := hMul
    _ = K * d := by
      dsimp [K]
      ring

/--
Problem E から recovered admissible decomposition の boundary 上にも exact linear defect が戻る。

block number `n` を十分大きく取れば

`F_n ≤ K * boundaryDefect(r,n)`。
-/
theorem exists_eventual_boundaryLinearDefect_of_exponentialEscape
    {e y r : ℕ → ℕ}
    (hDec : IsAdmissibleDecomposition e r)
    (hRun : RunsOddRecurrence e y)
    (hEscape : HasExponentialEscape y) :
    ∃ K R : ℕ,
      0 < K ∧
        ∀ n : ℕ, R ≤ n →
          boundaryIndex r n ≤ K * boundaryDefect r n := by
  obtain ⟨K, R, hK, hLinear⟩ :=
    exists_eventual_streamLinearDefect_of_exponentialEscape
      hDec hRun hEscape
  refine ⟨K, R, hK, ?_⟩
  intro n hn
  have hIndexLower : n ≤ boundaryIndex r n :=
    hDec.blockCount_le_boundaryIndex n
  have hRIndex : R ≤ boundaryIndex r n := le_trans hn hIndexLower
  have hMain := hLinear (boundaryIndex r n) hRIndex
  rw [streamDefect_boundaryIndex_eq_boundaryDefect hDec n] at hMain
  exact hMain

/--
逆向き：admissible decomposition 上で exact linear defect lower bound が十分遅く成立すれば、
奇整数 recurrence は Problem E 型指数逃走を満たす。
-/
theorem hasExponentialEscape_of_eventual_streamLinearDefect
    {e y r : ℕ → ℕ}
    (hDec : IsAdmissibleDecomposition e r)
    (hRun : RunsOddRecurrence e y)
    {K R : ℕ}
    (hK : 0 < K)
    (hLinear :
      ∀ m : ℕ, R ≤ m →
        m ≤ K * streamDefect e m) :
    HasExponentialEscape y := by
  refine ⟨K, max R 1, hK, ?_⟩
  intro m hm
  have hmR : R ≤ m := by omega
  have hmPos : 0 < m := by omega
  have hMain := hLinear m hmR
  have hDiv : m / K ≤ streamDefect e m := by
    apply Nat.div_le_of_le_mul
    simpa [Nat.mul_comm] using hMain
  have hPow :
      2 ^ (m / K) ≤ 2 ^ streamDefect e m :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hDiv
  obtain ⟨n, t, ht, hmEq⟩ := hDec.exists_blockLocation m
  have hValue :
      2 ^ streamDefect e m < y m := by
    have hInside :=
      twoPow_streamDefect_lt_value_inside
        hDec hRun n t (Nat.le_of_lt ht) (by simpa [hmEq] using hmPos)
    simpa [hmEq] using hInside
  exact le_trans hPow (Nat.le_of_lt hValue)

/--
Work の逆向き縮約の最終 package。

Problem E 型指数逃走を持つ独立奇整数 recurrence から、ある finite shift 後に

* 一意に決まる admissible decomposition が存在し、
* 全 sufficiently-large 時刻で exact linear stream defect lower bound が成立し、
* 従って boundary linear defect lower bound も成立する。
-/
theorem exists_shift_admissibleDecomposition_with_linearDefect_of_exponentialEscape
    {e y : ℕ → ℕ}
    (hRun : RunsOddRecurrence e y)
    (hEscape : HasExponentialEscape y) :
    ∃ h : ℕ, ∃ r : ℕ → ℕ, ∃ K R : ℕ,
      IsAdmissibleDecomposition (shiftSeq e h) r ∧
        RunsOddRecurrence (shiftSeq e h) (shiftSeq y h) ∧
        0 < K ∧
        (∀ m : ℕ, R ≤ m →
          m ≤ K * streamDefect (shiftSeq e h) m) ∧
        (∀ n : ℕ, R ≤ n →
          boundaryIndex r n ≤ K * boundaryDefect r n) := by
  obtain ⟨h, r, hDec⟩ :=
    exists_shift_admissibleDecomposition_of_exponentialEscape hRun hEscape
  have hShiftRun := hRun.shift h
  have hShiftEscape := hEscape.shift h
  obtain ⟨K, R, hK, hStream⟩ :=
    exists_eventual_streamLinearDefect_of_exponentialEscape
      hDec hShiftRun hShiftEscape
  have hBoundary :
      ∀ n : ℕ, R ≤ n →
        boundaryIndex r n ≤ K * boundaryDefect r n := by
    intro n hn
    have hIndexLower : n ≤ boundaryIndex r n :=
      hDec.blockCount_le_boundaryIndex n
    have hRIndex : R ≤ boundaryIndex r n := le_trans hn hIndexLower
    have hMain := hStream (boundaryIndex r n) hRIndex
    rw [streamDefect_boundaryIndex_eq_boundaryDefect hDec n] at hMain
    exact hMain
  exact ⟨h, r, K, R, hDec, hShiftRun, hK, hStream, hBoundary⟩

end IntegerReduction
end Collatz3
