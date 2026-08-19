import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelWronskian

/-!
# Christoffel defect: exact 3-adic propagation

raw Christoffel defect

  F_j(y) = φ_j - Γ_j y,
  Γ_j    = 2^(q_j) - 3^(p_j)

に対して、前段の exact Wronskian identity

  Γ_(j+1) F_j(y) - Γ_j F_(j+1)(y) = W_j

と

  even j : W_j = -2^(q_j-1) 3^(p_(j+1)-1),
  odd  j : W_j =  2^(q_(j+1)-1) 3^(p_j-1)

を組み合わせる。

ここでは p-adic valuation object を導入せず、

  3^t ∣ z  ∧  ¬ 3^(t+1) ∣ z

を exact 3-adic order の pure certificate として使う。

結果として、片側 defect が一段深く 3-power で割れるなら、反対側 defect は
Wronskian に現れる exponent で exact に止まる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- 整数 `z` が exact に `3^t` まで割れること。 -/
def ExactThreeAdicOrder
    (z : ℤ)
    (t : ℕ) : Prop :=
  (3 : ℤ) ^ t ∣ z ∧
    ¬ (3 : ℤ) ^ (t + 1) ∣ z

namespace ExactThreeAdicOrder

/-- exact order から lower divisibility を取り出す。 -/
theorem dvd
    {z : ℤ}
    {t : ℕ}
    (h : ExactThreeAdicOrder z t) :
    (3 : ℤ) ^ t ∣ z :=
  h.1

/-- exact order から one-step deeper nondivisibility を取り出す。 -/
theorem not_dvd_succ
    {z : ℤ}
    {t : ℕ}
    (h : ExactThreeAdicOrder z t) :
    ¬ (3 : ℤ) ^ (t + 1) ∣ z :=
  h.2

end ExactThreeAdicOrder

/-! ## elementary coprimality facts -/

/-- `3` と `2` は整数環で coprime。 -/
private theorem three_two_isCoprime :
    IsCoprime (3 : ℤ) (2 : ℤ) := by
  refine ⟨1, -1, ?_⟩
  norm_num

/-- 第二成分から第一成分の倍数を引いても coprime 性は保存される。 -/
private theorem isCoprime_sub_mul_right
    {a b c : ℤ}
    (h : IsCoprime a b) :
    IsCoprime a (b - a * c) := by
  rcases h with ⟨u, v, huv⟩
  refine ⟨u + v * c, v, ?_⟩
  calc
    (u + v * c) * a + v * (b - a * c)
        = u * a + v * b := by ring
    _ = 1 := huv

/--
`n ≤ p_j` なら `3^n` と raw power gap `Γ_j = 2^q-3^p` は coprime。

`3^p` は `3^n` の倍数なので、mod `3^n` では gap は `2^q` と同じであり、
`2` と `3` の coprimality だけが残る。
-/
theorem threePow_isCoprime_criticalRawPowerGap
    {D : CriticalContinuedFractionData}
    {j n : ℕ}
    (hn : n ≤ D.p j) :
    IsCoprime
      ((3 : ℤ) ^ n)
      (criticalRawPowerGap D j) := by
  have hPow :
      IsCoprime ((3 : ℤ) ^ n) ((2 : ℤ) ^ D.q j) := by
    exact three_two_isCoprime.pow
  have hThreeSplit :
      (3 : ℤ) ^ D.p j =
        (3 : ℤ) ^ n * (3 : ℤ) ^ (D.p j - n) := by
    rw [← pow_add]
    congr 1
    omega
  unfold criticalRawPowerGap
  rw [hThreeSplit]
  exact isCoprime_sub_mul_right hPow

/-- `r>0` なら `3^(r-1)` は `3^r` を割る。 -/
private theorem threePow_pred_dvd_threePow
    {r : ℕ}
    (hr : 0 < r) :
    (3 : ℤ) ^ (r - 1) ∣ (3 : ℤ) ^ r := by
  refine ⟨3, ?_⟩
  have hrEq : r = (r - 1) + 1 := by omega
  rw [hrEq, pow_succ]
  simp

/-- `3^(r-1)` は対応する Wronskian monomial を割る。 -/
private theorem threePow_pred_dvd_twoPow_mul_threePow_pred
    (r a : ℕ) :
    (3 : ℤ) ^ (r - 1) ∣
      (2 : ℤ) ^ a * (3 : ℤ) ^ (r - 1) := by
  refine ⟨(2 : ℤ) ^ a, ?_⟩
  ring

/--
`r>0` なら

  3^r ∤ 2^a 3^(r-1).

2-power は `3^r` と coprime なので、もし割れれば `3^r | 3^(r-1)` となり矛盾。
-/
private theorem not_threePow_dvd_twoPow_mul_threePow_pred
    (r a : ℕ)
    (hr : 0 < r) :
    ¬ (3 : ℤ) ^ r ∣
      (2 : ℤ) ^ a * (3 : ℤ) ^ (r - 1) := by
  intro hDiv
  have hCoprime :
      IsCoprime ((3 : ℤ) ^ r) ((2 : ℤ) ^ a) := by
    exact three_two_isCoprime.pow
  have hSmallInt :
      (3 : ℤ) ^ r ∣ (3 : ℤ) ^ (r - 1) :=
    hCoprime.dvd_of_dvd_mul_left hDiv
  have hSmallNat :
      (3 : ℕ) ^ r ∣ (3 : ℕ) ^ (r - 1) := by
    exact_mod_cast hSmallInt
  have hLe :
      (3 : ℕ) ^ r ≤ (3 : ℕ) ^ (r - 1) :=
    Nat.le_of_dvd (by positivity) hSmallNat
  have hLt :
      (3 : ℕ) ^ (r - 1) < (3 : ℕ) ^ r := by
    have hrEq : r = (r - 1) + 1 := by omega
    rw [hrEq, pow_succ]
    have hPos : 0 < (3 : ℕ) ^ (r - 1) := by positivity
    simp
  omega

/-! ## exact branchwise propagation -/

namespace CriticalRawChristoffelWronskianLaw

/--
even branch:

`3^(p_(j+1)) | F_(j+1)(y)` なら

`F_j(y)` は exact に `3^(p_(j+1)-1)` まで割れる。
-/
theorem even_defect_exactThreeAdicOrder_of_next_deep
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j)
    (hjEven : j % 2 = 0)
    (y : ℤ)
    (hDeep :
      (3 : ℤ) ^ D.p (j + 1) ∣
        criticalRawChristoffelDefect D (j + 1) y) :
    ExactThreeAdicOrder
      (criticalRawChristoffelDefect D j y)
      (D.p (j + 1) - 1) := by
  have hpNext : 0 < D.p (j + 1) :=
    D.p_pos (j + 1) (by omega)
  have hCross :=
    criticalRawChristoffelDefect_cross_eq_wronskian D j y
  have hW := W.even_next j hjStart hjEven
  constructor
  · have hWDiv :
        (3 : ℤ) ^ (D.p (j + 1) - 1) ∣
          criticalRawChristoffelWronskianNext D j := by
      rw [hW]
      apply dvd_neg.mpr
      exact
        threePow_pred_dvd_twoPow_mul_threePow_pred
          (D.p (j + 1)) (D.q j - 1)
    have hDeepPred :
        (3 : ℤ) ^ (D.p (j + 1) - 1) ∣
          criticalRawChristoffelDefect D (j + 1) y :=
      (threePow_pred_dvd_threePow hpNext).trans hDeep
    have hSecond :
        (3 : ℤ) ^ (D.p (j + 1) - 1) ∣
          criticalRawPowerGap D j *
            criticalRawChristoffelDefect D (j + 1) y :=
      dvd_mul_of_dvd_right hDeepPred _
    have hProduct :
        (3 : ℤ) ^ (D.p (j + 1) - 1) ∣
          criticalRawPowerGap D (j + 1) *
            criticalRawChristoffelDefect D j y := by
      have hEq :
          criticalRawPowerGap D (j + 1) *
                criticalRawChristoffelDefect D j y =
            criticalRawChristoffelWronskianNext D j +
              criticalRawPowerGap D j *
                criticalRawChristoffelDefect D (j + 1) y := by
        linarith
      rw [hEq]
      exact dvd_add hWDiv hSecond
    have hCoprime :=
      threePow_isCoprime_criticalRawPowerGap
        (D := D)
        (j := j + 1)
        (n := D.p (j + 1) - 1)
        (by omega)
    exact hCoprime.dvd_of_dvd_mul_left hProduct
  · intro hTooDeep
    have hTooDeep' :
        (3 : ℤ) ^ D.p (j + 1) ∣
          criticalRawChristoffelDefect D j y := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ D.p (j + 1))] using hTooDeep
    have hLeft :
        (3 : ℤ) ^ D.p (j + 1) ∣
          criticalRawPowerGap D (j + 1) *
            criticalRawChristoffelDefect D j y :=
      dvd_mul_of_dvd_right hTooDeep' _
    have hRight :
        (3 : ℤ) ^ D.p (j + 1) ∣
          criticalRawPowerGap D j *
            criticalRawChristoffelDefect D (j + 1) y :=
      dvd_mul_of_dvd_right hDeep _
    have hWDeep :
        (3 : ℤ) ^ D.p (j + 1) ∣
          criticalRawChristoffelWronskianNext D j := by
      rw [← hCross]
      exact dvd_sub hLeft hRight
    rw [hW] at hWDeep
    apply
      not_threePow_dvd_twoPow_mul_threePow_pred
        (D.p (j + 1)) (D.q j - 1) hpNext
    exact dvd_neg.mp hWDeep

/--
odd branch:

`3^(p_j) | F_j(y)` なら

`F_(j+1)(y)` は exact に `3^(p_j-1)` まで割れる。
-/
theorem odd_next_defect_exactThreeAdicOrder_of_current_deep
    {D : CriticalContinuedFractionData}
    (W : CriticalRawChristoffelWronskianLaw D)
    {j : ℕ}
    (hjStart : D.start ≤ j)
    (hjOdd : j % 2 = 1)
    (y : ℤ)
    (hDeep :
      (3 : ℤ) ^ D.p j ∣
        criticalRawChristoffelDefect D j y) :
    ExactThreeAdicOrder
      (criticalRawChristoffelDefect D (j + 1) y)
      (D.p j - 1) := by
  have hp : 0 < D.p j := D.p_pos j hjStart
  have hCross :=
    criticalRawChristoffelDefect_cross_eq_wronskian D j y
  have hW := W.odd_next j hjStart hjOdd
  constructor
  · have hWDiv :
        (3 : ℤ) ^ (D.p j - 1) ∣
          criticalRawChristoffelWronskianNext D j := by
      rw [hW]
      exact
        threePow_pred_dvd_twoPow_mul_threePow_pred
          (D.p j) (D.q (j + 1) - 1)
    have hDeepPred :
        (3 : ℤ) ^ (D.p j - 1) ∣
          criticalRawChristoffelDefect D j y :=
      (threePow_pred_dvd_threePow hp).trans hDeep
    have hFirst :
        (3 : ℤ) ^ (D.p j - 1) ∣
          criticalRawPowerGap D (j + 1) *
            criticalRawChristoffelDefect D j y :=
      dvd_mul_of_dvd_right hDeepPred _
    have hProduct :
        (3 : ℤ) ^ (D.p j - 1) ∣
          criticalRawPowerGap D j *
            criticalRawChristoffelDefect D (j + 1) y := by
      have hEq :
          criticalRawPowerGap D j *
                criticalRawChristoffelDefect D (j + 1) y =
            criticalRawPowerGap D (j + 1) *
                criticalRawChristoffelDefect D j y -
              criticalRawChristoffelWronskianNext D j := by
        linarith
      rw [hEq]
      exact dvd_sub hFirst hWDiv
    have hCoprime :=
      threePow_isCoprime_criticalRawPowerGap
        (D := D)
        (j := j)
        (n := D.p j - 1)
        (by omega)
    exact hCoprime.dvd_of_dvd_mul_left hProduct
  · intro hTooDeep
    have hTooDeep' :
        (3 : ℤ) ^ D.p j ∣
          criticalRawChristoffelDefect D (j + 1) y := by
      simpa [Nat.sub_add_cancel (by omega : 1 ≤ D.p j)] using hTooDeep
    have hLeft :
        (3 : ℤ) ^ D.p j ∣
          criticalRawPowerGap D (j + 1) *
            criticalRawChristoffelDefect D j y :=
      dvd_mul_of_dvd_right hDeep _
    have hRight :
        (3 : ℤ) ^ D.p j ∣
          criticalRawPowerGap D j *
            criticalRawChristoffelDefect D (j + 1) y :=
      dvd_mul_of_dvd_right hTooDeep' _
    have hWDeep :
        (3 : ℤ) ^ D.p j ∣
          criticalRawChristoffelWronskianNext D j := by
      rw [← hCross]
      exact dvd_sub hLeft hRight
    rw [hW] at hWDeep
    exact
      not_threePow_dvd_twoPow_mul_threePow_pred
        (D.p j) (D.q (j + 1) - 1) hp
        hWDeep

end CriticalRawChristoffelWronskianLaw

/-! ## actual critical sequence wrappers -/

/-- actual even branch の exact 3-adic propagation。 -/
theorem actual_even_defect_exactThreeAdicOrder_of_next_deep
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (y : ℤ)
    (hDeep :
      (3 : ℤ) ^ criticalPowerP (j + 1) ∣
        criticalRawChristoffelDefect
          actualCriticalContinuedFractionData (j + 1) y) :
    ExactThreeAdicOrder
      (criticalRawChristoffelDefect
        actualCriticalContinuedFractionData j y)
      (criticalPowerP (j + 1) - 1) := by
  exact
    actualCriticalRawChristoffelWronskianLaw.even_defect_exactThreeAdicOrder_of_next_deep
      (by simpa using hj)
      hjEven
      y
      hDeep

/-- actual odd branch の exact 3-adic propagation。 -/
theorem actual_odd_next_defect_exactThreeAdicOrder_of_current_deep
    {j : ℕ}
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (y : ℤ)
    (hDeep :
      (3 : ℤ) ^ criticalPowerP j ∣
        criticalRawChristoffelDefect
          actualCriticalContinuedFractionData j y) :
    ExactThreeAdicOrder
      (criticalRawChristoffelDefect
        actualCriticalContinuedFractionData (j + 1) y)
      (criticalPowerP j - 1) := by
  exact
    actualCriticalRawChristoffelWronskianLaw.odd_next_defect_exactThreeAdicOrder_of_current_deep
      (by simpa using hj)
      hjOdd
      y
      hDeep

end ExternalArithmetic
end CSTMicro
end Collatz2
