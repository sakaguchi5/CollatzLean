import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBRelativeChristoffelDefectValuation
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBResidualLocalWronskian

/-!
# Pure B Stage 8R2: corridor-free residual dyadic rigidity

旧 Stage 8R は full q-jump 仮定 `beta(a)<Q_j` を residual exponent

  rho(a,j)
    = min(
        Q_(j+1)-Q_j,
        strongPrecision(j) - (beta(a)+Q_j))

へ置き換えたが、canonical shifted dictionary を criticalization start で直接使うため

  a + P_j     < P_(j+1)
  a + P_(j+1) < P_(j+2)

という二本の corridor 条件をまだ要求していた。

この Stage 8R2 では、`PureBResidualLocalWronskian` の corridor-free local theorem

  2^(S_j-beta(a)) | Wloc(a,j)

を使い、上の二本を live theorem の仮定から除去する。

重要な論理分岐は `rho=0 / rho>0` である。

* `rho=0` では dyadic divisibility は情報を持たない。
* `rho>0` なら
    beta(a) < Q_(j+1)-1
  が自動的に従い、Beatty monotonicity と endpoint formula から
    a < P_(j+1)
  が自動的に従う。
  したがって residual local Wronskian theorem と extended Beatty shift を
  仮定追加なしで起動できる。

その結果、nontrivial branch の最終 theorem は

  2 <= criticalizationStart
  9 <= j
  criticalizationStart + P_(j+1) <= m
  0 < rho(criticalizationStart,j)

だけから

  2^rho <= 4*yNat

を与える。

一般形は正確に

  rho = 0  OR  2^rho <= 4*yNat

である。

旧 `beta(a)<Q_j` を仮定すれば rho は full q-jump なので正であり、
corridor 条件なしで旧 full-q-jump bound も回収できる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-! ## 1. residual exponent -/

/--
Stage 8R2 の residual dyadic exponent。

local Wronskian が持つ residual precision
`S_j-beta(a)` を、next block が持つ `Q_(j+1)` で cap し、
first block factor `Q_j` を消した残りに等しい。
-/
def residualQJumpExponent (a j : ℕ) : ℕ :=
  min
    (criticalPowerQ (j + 1) - criticalPowerQ j)
    (actualCriticalContinuedFractionData.strongPrecision j -
      (beattyIndex a + criticalPowerQ j))

/-- residual exponent の phase-loss 表示。 -/
theorem residualQJumpExponent_eq_phaseLoss
    (a j : ℕ) :
    residualQJumpExponent a j =
      min
        (criticalPowerQ (j + 1) - criticalPowerQ j)
        (criticalPowerQ (j + 1) - 1 - beattyIndex a) := by
  unfold residualQJumpExponent
  have hStrong :
      actualCriticalContinuedFractionData.strongPrecision j =
        criticalPowerQ j + criticalPowerQ (j + 1) - 1 := by
    simp [actualCriticalContinuedFractionData]
  rw [hStrong]
  have hLoss :
      (criticalPowerQ j + criticalPowerQ (j + 1) - 1) -
          (beattyIndex a + criticalPowerQ j) =
        criticalPowerQ (j + 1) - 1 - beattyIndex a := by
    omega
  rw [hLoss]

/--
旧 full-precision 条件 `beta(a)<Q_j` の下では residual exponent は
full adjacent q-jump に戻る。
-/
theorem residualQJumpExponent_eq_full_of_precision
    {a j : ℕ}
    (hj : 9 ≤ j)
    (hPrecision : beattyIndex a < criticalPowerQ j) :
    residualQJumpExponent a j =
      criticalPowerQ (j + 1) - criticalPowerQ j := by
  rw [residualQJumpExponent_eq_phaseLoss]
  have hQlt :
      criticalPowerQ j < criticalPowerQ (j + 1) :=
    criticalPowerQ_lt_next hj
  have hLe :
      criticalPowerQ (j + 1) - criticalPowerQ j ≤
        criticalPowerQ (j + 1) - 1 - beattyIndex a := by
    omega
  exact min_eq_left hLe

/-! ## 2. rho>0 が phase window を自動的に強制する -/

/--
`rho(a,j)>0` なら phase-loss 側も正なので

  beta(a) < Q_(j+1)-1.

これは Stage 8R2 で local Wronskian window を自動生成する第一段。
-/
theorem beattyIndex_lt_nextQ_pred_of_residualQJumpExponent_pos
    {a j : ℕ}
    (hRhoPos : 0 < residualQJumpExponent a j) :
    beattyIndex a < criticalPowerQ (j + 1) - 1 := by
  rw [residualQJumpExponent_eq_phaseLoss] at hRhoPos
  have hLe :
      residualQJumpExponent a j ≤
        criticalPowerQ (j + 1) - 1 - beattyIndex a := by
    rw [residualQJumpExponent_eq_phaseLoss]
    exact min_le_right _ _
  omega

/--
`rho(a,j)>0` なら `a<P_(j+1)`。

`P_(j+1)` endpoint では parity に応じて

* odd  : beta(P_(j+1)) = Q_(j+1)
* even : beta(P_(j+1)) = Q_(j+1)-1

なので、`beta(a)<Q_(j+1)-1` と strict monotonicity により
`a` は必ず next numerator より左にある。
-/
theorem lt_nextP_of_residualQJumpExponent_pos
    {a j : ℕ}
    (hj : 9 ≤ j)
    (hRhoPos : 0 < residualQJumpExponent a j) :
    a < criticalPowerP (j + 1) := by
  have hBeta :=
    beattyIndex_lt_nextQ_pred_of_residualQJumpExponent_pos
      (a := a) (j := j) hRhoPos
  by_contra hNot
  have hPLe :
      criticalPowerP (j + 1) ≤ a := by
    omega
  have hBetaMono :
      beattyIndex (criticalPowerP (j + 1)) ≤ beattyIndex a := by
    by_cases hEq : criticalPowerP (j + 1) = a
    · subst a
      exact le_rfl
    · have hLt : criticalPowerP (j + 1) < a := by
        omega
      exact le_of_lt (beattyIndex_strictMono hLt)
  have hmod :
      (j + 1) % 2 < 2 :=
    Nat.mod_lt (j + 1) (by decide)
  by_cases hOdd : (j + 1) % 2 = 1
  · have hEnd :=
      actual_beattyIndex_currentP_eq_Q_of_odd
        (j := j + 1) (by omega) hOdd
    rw [hEnd] at hBetaMono
    omega
  · have hEven : (j + 1) % 2 = 0 := by
      omega
    have hEnd :=
      actual_beattyIndex_currentP_eq_Q_pred_of_even
        (j := j + 1) (by omega) hEven
    rw [hEnd] at hBetaMono
    omega

/-! ## 3. local Wronskian と affine defects の exact cross identity -/

/--
positive next-numerator window では local numerator Wronskian は
同じ left state `y` で読む affine defects の cross と exact に一致する。

state parameter の項は

  Gamma_(j+1) Gamma_j y - Gamma_j Gamma_(j+1) y

として消える。
-/
theorem residualLocalAdjacentWronskian_eq_defectCross
    {a j : ℕ}
    (hj : 9 ≤ j)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1))
    (y : ℤ) :
    residualLocalAdjacentWronskian a j =
      actualCriticalRawPowerGap (j + 1) *
          criticalIntervalDefectZ
            a (a + criticalPowerP j) y -
        actualCriticalRawPowerGap j *
          criticalIntervalDefectZ
            a (a + criticalPowerP (j + 1)) y := by
  have hGapJ :=
    residualLocalBlockGap_eq_rawGap
      (a := a) (j := j) hj haPos haLt
  have hGapNext :=
    residualLocalNextBlockGap_eq_rawGap
      (a := a) (j := j) hj haPos haLt
  unfold residualLocalBlockGap at hGapJ hGapNext
  unfold residualLocalAdjacentWronskian residualLocalBlockNumerator
  unfold criticalIntervalDefectZ
  rw [hGapJ, hGapNext]
  ring

/-! ## 4. endpoint-state conversion without old corridor inequalities -/

/--
`0<a<P_(j+1)` では current standard block defect は exact に

  2^Q_j (Z_(a+P_j)-Z_a).

旧 8R-A の `a+P_j<P_(j+1)` は不要で、
extended Beatty shift の `a<P_(j+1)` だけでよい。
-/
theorem integralCurrentBlockDefect_eq_twoPow_mul_stateDifference
    (P : PureBProfileObstruction)
    {a j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1))
    (hBlockEnd : a + criticalPowerP j ≤ P.m)
    (hj : 9 ≤ j) :
    criticalIntervalDefectZ
        a (a + criticalPowerP j)
        (P.integralCriticalTailStateInt A a le_rfl A.1) =
      (2 : ℤ) ^ criticalPowerQ j *
        (P.integralCriticalTailStateInt
            A (a + criticalPowerP j) (by omega) hBlockEnd -
          P.integralCriticalTailStateInt A a le_rfl A.1) := by
  have hRise :=
    actual_beattyIndex_currentP_rise_eq_Q_of_pos_lt_nextP
      (j := j) (x := a) hj haPos haLt
  have hState :=
    P.criticalIntervalDefectZ_at_integralLeftState
      (A := A)
      (s := a)
      (r := criticalPowerP j)
      le_rfl
      hBlockEnd
  rw [hRise] at hState
  exact hState

/--
同じ `0<a<P_(j+1)` だけで next standard block も

  2^Q_(j+1) (Z_(a+P_(j+1))-Z_a)

へ変換できる。
-/
theorem integralNextBlockDefect_eq_twoPow_mul_stateDifference
    (P : PureBProfileObstruction)
    {a j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1))
    (hBlockEnd : a + criticalPowerP (j + 1) ≤ P.m)
    (hj : 9 ≤ j) :
    criticalIntervalDefectZ
        a (a + criticalPowerP (j + 1))
        (P.integralCriticalTailStateInt A a le_rfl A.1) =
      (2 : ℤ) ^ criticalPowerQ (j + 1) *
        (P.integralCriticalTailStateInt
            A (a + criticalPowerP (j + 1)) (by omega) hBlockEnd -
          P.integralCriticalTailStateInt A a le_rfl A.1) := by
  have hRise :=
    actual_beattyIndex_nextP_rise_eq_nextQ_of_pos_lt_nextP
      (j := j) (x := a) hj haPos haLt
  have hState :=
    P.criticalIntervalDefectZ_at_integralLeftState
      (A := A)
      (s := a)
      (r := criticalPowerP (j + 1))
      le_rfl
      hBlockEnd
  rw [hRise] at hState
  exact hState

/-! ## 5. corridor-free residual divisibility on the useful branch -/

/--
`a<P_(j+1)` の local Wronskian precision と endpoint-state identity を合成する。

old Stage 8R-B の二本の corridor

  a + P_j     < P_(j+1)
  a + P_(j+1) < P_(j+2)

は消えている。

必要なのは、adjacent pair の大きい endpoint が integral tail 内にあることだけ。
-/
theorem twoPow_residualQJump_dvd_integralStateDifference_of_lt_nextP
    (P : PureBProfileObstruction)
    {a j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (haLt : a < criticalPowerP (j + 1))
    (hBlockEndNext : a + criticalPowerP (j + 1) ≤ P.m)
    (hj : 9 ≤ j) :
    (2 : ℤ) ^ residualQJumpExponent a j ∣
      (P.integralCriticalTailStateInt
          A (a + criticalPowerP j)
          (by
            have _hPmono :
                criticalPowerP j < criticalPowerP (j + 1) :=
              criticalPowerP_strict_succ (r := j) (by omega)
            omega)
          (by
            have hPmono :
                criticalPowerP j < criticalPowerP (j + 1) :=
              criticalPowerP_strict_succ (r := j) (by omega)
            omega) -
        P.integralCriticalTailStateInt A a le_rfl A.1) := by
  let r : ℕ := residualQJumpExponent a j
  let S : ℕ := actualCriticalContinuedFractionData.strongPrecision j
  let E : ℕ := S - beattyIndex a
  have hPmono :
      criticalPowerP j < criticalPowerP (j + 1) :=
    criticalPowerP_strict_succ (r := j) (by omega)
  have hBlockEndJ :
      a + criticalPowerP j ≤ P.m := by
    omega
  let Za : ℤ :=
    P.integralCriticalTailStateInt A a le_rfl A.1
  let Zj : ℤ :=
    P.integralCriticalTailStateInt
      A (a + criticalPowerP j) (by omega) hBlockEndJ
  let Zn : ℤ :=
    P.integralCriticalTailStateInt
      A (a + criticalPowerP (j + 1)) (by omega) hBlockEndNext
  let Dj : ℤ := Zj - Za
  let Dn : ℤ := Zn - Za
  change (2 : ℤ) ^ r ∣ Dj
  by_cases hr0 : r = 0
  · rw [hr0]
    simp
  have hrPos : 0 < r := by omega
  have hStrong :
      S = criticalPowerQ j + criticalPowerQ (j + 1) - 1 := by
    dsimp [S]
    simp [actualCriticalContinuedFractionData]
  have hRLeJump :
      r ≤ criticalPowerQ (j + 1) - criticalPowerQ j := by
    dsimp [r, residualQJumpExponent]
    exact min_le_left _ _
  have hRLeBudget :
      r ≤ S - (beattyIndex a + criticalPowerQ j) := by
    dsimp [r, S, residualQJumpExponent]
    exact min_le_right _ _
  have hBudgetPos :
      0 < S - (beattyIndex a + criticalPowerQ j) := by
    omega
  have hBudget :
      beattyIndex a + criticalPowerQ j ≤ S := by
    omega
  have hQPos : 0 < criticalPowerQ j :=
    criticalPowerQ_pos j
  have hQNextPos : 0 < criticalPowerQ (j + 1) :=
    criticalPowerQ_pos (j + 1)
  have hQlt :
      criticalPowerQ j < criticalPowerQ (j + 1) :=
    criticalPowerQ_lt_next hj
  have hQPlusRLeE :
      criticalPowerQ j + r ≤ E := by
    dsimp [E]
    omega
  have hQPlusRLeNext :
      criticalPowerQ j + r ≤ criticalPowerQ (j + 1) := by
    omega
  have hLocalDvdE :
      (2 : ℤ) ^ E ∣ residualLocalAdjacentWronskian a j := by
    simpa [E, S] using
      twoPow_residualPrecision_dvd_residualLocalAdjacentWronskian
        (a := a) (j := j) hj haPos haLt
  have hPowSmallDvdE :
      (2 : ℤ) ^ (criticalPowerQ j + r) ∣ (2 : ℤ) ^ E := by
    refine ⟨
      (2 : ℤ) ^ (E - (criticalPowerQ j + r)),
      ?_⟩
    have hSplit :
        E =
          (criticalPowerQ j + r) +
            (E - (criticalPowerQ j + r)) := by
      omega
    rw [hSplit, pow_add]
    simp
  have hLocalDvd :
      (2 : ℤ) ^ (criticalPowerQ j + r) ∣
        residualLocalAdjacentWronskian a j :=
    dvd_trans hPowSmallDvdE hLocalDvdE
  have hCross :=
    residualLocalAdjacentWronskian_eq_defectCross
      (a := a) (j := j) hj haPos haLt Za
  have hJ0 :=
    P.integralCurrentBlockDefect_eq_twoPow_mul_stateDifference
      (A := A)
      haPos
      haLt
      hBlockEndJ
      hj
  have hJ :
      criticalIntervalDefectZ
          a (a + criticalPowerP j) Za =
        (2 : ℤ) ^ criticalPowerQ j * Dj := by
    simpa [Za, Zj, Dj] using hJ0
  have hN0 :=
    P.integralNextBlockDefect_eq_twoPow_mul_stateDifference
      (A := A)
      haPos
      haLt
      hBlockEndNext
      hj
  have hN :
      criticalIntervalDefectZ
          a (a + criticalPowerP (j + 1)) Za =
        (2 : ℤ) ^ criticalPowerQ (j + 1) * Dn := by
    simpa [Za, Zn, Dn] using hN0
  rw [hCross, hJ, hN] at hLocalDvd
  have hNextSplit :
      criticalPowerQ (j + 1) =
        (criticalPowerQ j + r) +
          (criticalPowerQ (j + 1) - (criticalPowerQ j + r)) := by
    omega
  have hSecond :
      (2 : ℤ) ^ (criticalPowerQ j + r) ∣
        actualCriticalRawPowerGap j *
          ((2 : ℤ) ^ criticalPowerQ (j + 1) * Dn) := by
    refine ⟨
      actualCriticalRawPowerGap j *
        ((2 : ℤ) ^
            (criticalPowerQ (j + 1) - (criticalPowerQ j + r)) * Dn),
      ?_⟩
    rw [hNextSplit, pow_add]
    ring_nf
    simp
  have hFirst :
      (2 : ℤ) ^ (criticalPowerQ j + r) ∣
        actualCriticalRawPowerGap (j + 1) *
          ((2 : ℤ) ^ criticalPowerQ j * Dj) := by
    have hAdd := dvd_add hLocalDvd hSecond
    have hEq :
        (actualCriticalRawPowerGap (j + 1) *
              ((2 : ℤ) ^ criticalPowerQ j * Dj) -
            actualCriticalRawPowerGap j *
              ((2 : ℤ) ^ criticalPowerQ (j + 1) * Dn)) +
          actualCriticalRawPowerGap j *
            ((2 : ℤ) ^ criticalPowerQ (j + 1) * Dn) =
        actualCriticalRawPowerGap (j + 1) *
          ((2 : ℤ) ^ criticalPowerQ j * Dj) := by
      ring
    rw [hEq] at hAdd
    exact hAdd
  have hProduct :
      (2 : ℤ) ^ r ∣
        actualCriticalRawPowerGap (j + 1) * Dj := by
    rcases hFirst with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have hPowSplit :
        (2 : ℤ) ^ (criticalPowerQ j + r) =
          (2 : ℤ) ^ criticalPowerQ j * (2 : ℤ) ^ r := by
      rw [pow_add]
    have hTwoNe : (2 : ℤ) ^ criticalPowerQ j ≠ 0 := by
      positivity
    apply mul_left_cancel₀ hTwoNe
    calc
      (2 : ℤ) ^ criticalPowerQ j *
          (actualCriticalRawPowerGap (j + 1) * Dj) =
        actualCriticalRawPowerGap (j + 1) *
          ((2 : ℤ) ^ criticalPowerQ j * Dj) := by
            ring
      _ = (2 : ℤ) ^ (criticalPowerQ j + r) * u := hu
      _ =
        (2 : ℤ) ^ criticalPowerQ j *
          ((2 : ℤ) ^ r * u) := by
            rw [hPowSplit]
            ring
  have hRLeNext : r ≤ criticalPowerQ (j + 1) := by
    omega
  have hNextRSplit :
      criticalPowerQ (j + 1) =
        r + (criticalPowerQ (j + 1) - r) := by
    omega
  have hGapCoprime :
      IsCoprime
        ((2 : ℤ) ^ r)
        (actualCriticalRawPowerGap (j + 1)) := by
    have h23 : IsCoprime (2 : ℤ) (3 : ℤ) := by
      refine ⟨-1, 1, ?_⟩
      norm_num
    have hBase :
        IsCoprime
          ((2 : ℤ) ^ r)
          ((3 : ℤ) ^ criticalPowerP (j + 1)) := by
      exact h23.pow
    rcases hBase with ⟨u, v, huv⟩
    refine ⟨
      u + v *
        (2 : ℤ) ^ (criticalPowerQ (j + 1) - r),
      -v,
      ?_⟩
    unfold actualCriticalRawPowerGap
    have hTwoSplit :
        (2 : ℤ) ^ criticalPowerQ (j + 1) =
          (2 : ℤ) ^ r *
            (2 : ℤ) ^ (criticalPowerQ (j + 1) - r) := by
      rw [hNextRSplit, pow_add]
      simp
    rw [hTwoSplit]
    calc
      (u + v *
            (2 : ℤ) ^ (criticalPowerQ (j + 1) - r)) *
            (2 : ℤ) ^ r +
          (-v) *
            ((2 : ℤ) ^ r *
                (2 : ℤ) ^ (criticalPowerQ (j + 1) - r) -
              (3 : ℤ) ^ criticalPowerP (j + 1))
          =
        u * (2 : ℤ) ^ r +
          v * (3 : ℤ) ^ criticalPowerP (j + 1) := by
            ring
      _ = 1 := huv
  exact hGapCoprime.dvd_of_dvd_mul_left hProduct

/--
Stage 8R2 が実際に使う wrapper。

`rho>0` なら `a<P_(j+1)` が自動なので、公開仮定には phase window すら現れない。
-/
theorem twoPow_residualQJump_dvd_integralStateDifference
    (P : PureBProfileObstruction)
    {a j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hBlockEndNext : a + criticalPowerP (j + 1) ≤ P.m)
    (hj : 9 ≤ j)
    (hRhoPos : 0 < residualQJumpExponent a j) :
    (2 : ℤ) ^ residualQJumpExponent a j ∣
      (P.integralCriticalTailStateInt
          A (a + criticalPowerP j)
          (by
            have _hPmono :
                criticalPowerP j < criticalPowerP (j + 1) :=
              criticalPowerP_strict_succ (r := j) (by omega)
            omega)
          (by
            have hPmono :
                criticalPowerP j < criticalPowerP (j + 1) :=
              criticalPowerP_strict_succ (r := j) (by omega)
            omega) -
        P.integralCriticalTailStateInt A a le_rfl A.1) := by
  have haLt :=
    lt_nextP_of_residualQJumpExponent_pos
      (a := a) (j := j) hj hRhoPos
  exact
    P.twoPow_residualQJump_dvd_integralStateDifference_of_lt_nextP
      (A := A)
      haPos
      haLt
      hBlockEndNext
      hj

/-! ## 6. criticalization start nonreturn without old corridor -/

/--
criticalization start では、`2<=a<P_(j+1)` の standard shift による state return は不可能。

old 8R-C の corridor 条件を、extended Beatty shift が与える
predecessor one-cell equality に置き換えた。
-/
theorem criticalizationStart_integralState_ne_of_standardShift_residual
    (P : PureBProfileObstruction)
    {j : ℕ}
    (hStartTwo : 2 ≤ P.criticalizationStart)
    (hj : 9 ≤ j)
    (hBlockEnd :
      P.criticalizationStart + criticalPowerP j ≤ P.m)
    (hStartLt :
      P.criticalizationStart < criticalPowerP (j + 1)) :
    P.integralCriticalTailStateInt
        P.criticalizationStart_spec
        (P.criticalizationStart + criticalPowerP j)
        (by omega)
        hBlockEnd ≠
      P.integralCriticalTailStateInt
        P.criticalizationStart_spec
        P.criticalizationStart
        le_rfl
        P.criticalizationStart_spec.1 := by
  let a := P.criticalizationStart
  let A : IsIntegralCriticalTail P a := P.criticalizationStart_spec
  change
    P.integralCriticalTailStateInt
        A (a + criticalPowerP j) (by omega) hBlockEnd ≠
      P.integralCriticalTailStateInt A a le_rfl A.1
  intro hReturn
  have haTwo : 2 ≤ a := by
    simpa [a] using hStartTwo
  have haLt : a < criticalPowerP (j + 1) := by
    simpa [a] using hStartLt
  have hPPos : 0 < criticalPowerP j :=
    criticalPowerP_pos (by omega)
  have hGapEq :=
    actual_beattyIndex_currentP_preserves_pred_cell_of_two_le_lt_nextP
      (j := j) (x := a) hj haTwo haLt
  have hStepStart :
      a ≤ a + criticalPowerP j - 1 := by
    omega
  have hStepLt :
      a + criticalPowerP j - 1 < P.m := by
    omega
  have hStepLe :
      a + criticalPowerP j - 1 ≤ P.m :=
    Nat.le_of_lt hStepLt
  have hRec0 :=
    P.integralCriticalTailStateInt_step
      (A := A)
      (s := a + criticalPowerP j - 1)
      hStepStart
      hStepLt
  have hSucc :
      (a + criticalPowerP j - 1) + 1 =
        a + criticalPowerP j := by
    omega
  have hShiftStart :
      a ≤ a + criticalPowerP j := by
    omega
  have hRec :
      (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
          P.integralCriticalTailStateInt
            A
            (a + criticalPowerP j)
            hShiftStart
            hBlockEnd =
        3 *
            P.integralCriticalTailStateInt
              A
              (a + criticalPowerP j - 1)
              hStepStart
              hStepLe +
          1 := by
    simpa [hSucc, hGapEq] using hRec0
  have hReturn' :
      P.integralCriticalTailStateInt
          A
          (a + criticalPowerP j)
          hShiftStart
          hBlockEnd =
        P.integralCriticalTailStateInt
          A
          a
          le_rfl
          A.1 := by
    simpa using hReturn
  have hRecReturn :
      (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
          P.integralCriticalTailStateInt A a le_rfl A.1 =
        3 *
            P.integralCriticalTailStateInt
              A
              (a + criticalPowerP j - 1)
              hStepStart
              hStepLe +
          1 := by
    simpa [hReturn'] using hRec
  have hBracket :
      (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
          P.integralCriticalTailStateInt A a le_rfl A.1 - 1 =
        3 *
          P.integralCriticalTailStateInt
            A
            (a + criticalPowerP j - 1)
            hStepStart
            hStepLe := by
    linarith [hRecReturn]
  have hPredLtM :
      a - 1 < P.m := by
    omega
  have hPredLeM :
      a - 1 ≤ P.m :=
    Nat.le_of_lt hPredLtM
  have hRaw0 :=
    P.terminalRawTail_step_raw
      (s := a - 1)
      hPredLtM
  have hPredSucc :
      (a - 1) + 1 = a := by
    omega
  rw [hPredSucc] at hRaw0
  have hSpecA :=
    P.integralCriticalTailStateInt_spec
      (A := A)
      (s := a)
      le_rfl
      A.1
  have hLen :
      P.m - (a - 1) = (P.m - a) + 1 := by
    omega
  let Zprev : ℤ :=
    P.integralCriticalTailStateInt
      A
      (a + criticalPowerP j - 1)
      hStepStart
      hStepLe
  have hBracketZ :
      (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
          P.integralCriticalTailStateInt A a le_rfl A.1 - 1 =
        3 * Zprev := by
    simpa [Zprev] using hBracket
  have hSpecA_scaled :
      (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
            P.terminalRawTail a -
          (3 : ℤ) ^ (P.m - a) =
        (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
            ((3 : ℤ) ^ (P.m - a) *
              P.integralCriticalTailStateInt A a le_rfl A.1) -
          (3 : ℤ) ^ (P.m - a) := by
    exact congrArg
      (fun z : ℤ =>
        (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) * z -
          (3 : ℤ) ^ (P.m - a))
      hSpecA
  have hPrev :
      IsIntegralCriticalTail P (a - 1) := by
    constructor
    · exact hPredLeM
    · refine ⟨Zprev, ?_⟩
      rw [hLen, pow_succ]
      calc
        P.terminalRawTail (a - 1) =
            (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
                P.terminalRawTail a -
              (3 : ℤ) ^ (P.m - a) := hRaw0
        _ =
            (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
                ((3 : ℤ) ^ (P.m - a) *
                  P.integralCriticalTailStateInt A a le_rfl A.1) -
              (3 : ℤ) ^ (P.m - a) := hSpecA_scaled
        _ =
            (3 : ℤ) ^ (P.m - a) *
              ((2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
                  P.integralCriticalTailStateInt A a le_rfl A.1 - 1) := by
                ring
        _ =
            (3 : ℤ) ^ (P.m - a) *
              (3 * Zprev) := by
                rw [hBracketZ]
        _ =
            ((3 : ℤ) ^ (P.m - a) * 3) *
              Zprev := by
                ring
  have hMin :=
    P.criticalizationStart_minimal hPrev
  change a ≤ a - 1 at hMin
  omega

/-! ## 7. final corridor-free Stage 8R2 -/

/--
nontrivial residual branch の final dyadic rigidity。

公開仮定から old corridor は完全に消えた。
`rho>0` 自身が必要な local phase window を自動生成する。
-/
theorem criticalizationStart_residualQJump_dyadic_bound
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    {j : ℕ}
    (hStartTwo : 2 ≤ P.criticalizationStart)
    (hj : 9 ≤ j)
    (hBlockEndNext :
      P.criticalizationStart + criticalPowerP (j + 1) ≤ P.m)
    (hRhoPos :
      0 <
        residualQJumpExponent P.criticalizationStart j) :
    2 ^ residualQJumpExponent P.criticalizationStart j ≤
      4 * P.yNat := by
  let a := P.criticalizationStart
  let A : IsIntegralCriticalTail P a :=
    P.criticalizationStart_spec
  have haTwo : 2 ≤ a := by
    simpa [a] using hStartTwo
  have haPos : 0 < a := by omega
  have hRhoPos' :
      0 < residualQJumpExponent a j := by
    simpa [a] using hRhoPos
  have haLt :
      a < criticalPowerP (j + 1) :=
    lt_nextP_of_residualQJumpExponent_pos
      (a := a) (j := j) hj hRhoPos'
  have hPmono :
      criticalPowerP j < criticalPowerP (j + 1) :=
    criticalPowerP_strict_succ (r := j) (by omega)
  have hEndNext :
      a + criticalPowerP (j + 1) ≤ P.m := by
    simpa [a] using hBlockEndNext
  have hBlockEndJ :
      a + criticalPowerP j ≤ P.m := by
    omega
  have hDiv :=
    P.twoPow_residualQJump_dvd_integralStateDifference
      (A := A)
      haPos
      hEndNext
      hj
      hRhoPos'
  have hNe :=
    P.criticalizationStart_integralState_ne_of_standardShift_residual
      (j := j)
      hStartTwo
      hj
      (by simpa [a] using hBlockEndJ)
      (by simpa [a] using haLt)
  let Za : ℤ :=
    P.integralCriticalTailStateInt A a le_rfl A.1
  let Zj : ℤ :=
    P.integralCriticalTailStateInt
      A (a + criticalPowerP j) (by omega) hBlockEndJ
  let D : ℤ := Zj - Za
  have hDivD :
      (2 : ℤ) ^ residualQJumpExponent a j ∣ D := by
    simpa [D, Zj, Za, a, A] using hDiv
  have hDNe : D ≠ 0 := by
    intro hZero
    apply hNe
    have hEq : Zj = Za := by
      dsimp [D] at hZero
      linarith
    simpa [Zj, Za, a, A] using hEq
  have hZaNonneg : 0 ≤ Za := by
    dsimp [Za]
    exact
      P.integralCriticalTailStateInt_nonneg
        A hy le_rfl A.1
  have hZjNonneg : 0 ≤ Zj := by
    dsimp [Zj]
    exact
      P.integralCriticalTailStateInt_nonneg
        A hy (by omega) hBlockEndJ
  have hZaLe : Za ≤ 4 * P.y := by
    dsimp [Za]
    exact
      P.integralCriticalTailStateInt_le_four_y
        A hy le_rfl A.1
  have hZjLe : Zj ≤ 4 * P.y := by
    dsimp [Zj]
    exact
      P.integralCriticalTailStateInt_le_four_y
        A hy (by omega) hBlockEndJ
  have hPowPos :
      0 < (2 : ℤ) ^ residualQJumpExponent a j := by
    positivity
  have hBoundInt :
      (2 : ℤ) ^ residualQJumpExponent a j ≤
        4 * P.y := by
    rcases lt_or_gt_of_ne hDNe with hDNeg | hDPos
    · have hDivNeg :
          (2 : ℤ) ^ residualQJumpExponent a j ∣ -D :=
        dvd_neg.mpr hDivD
      rcases hDivNeg with ⟨u, hu⟩
      have huPos : 0 < u := by
        have hNegPos : 0 < -D := by
          linarith
        nlinarith
      have hPowLeNeg :
          (2 : ℤ) ^ residualQJumpExponent a j ≤ -D := by
        rw [hu]
        have huOne : (1 : ℤ) ≤ u := by omega
        nlinarith
      have hNegLe : -D ≤ Za := by
        dsimp [D]
        linarith
      exact
        le_trans hPowLeNeg (le_trans hNegLe hZaLe)
    · rcases hDivD with ⟨u, hu⟩
      have huPos : 0 < u := by
        nlinarith
      have hPowLeD :
          (2 : ℤ) ^ residualQJumpExponent a j ≤ D := by
        rw [hu]
        have huOne : (1 : ℤ) ≤ u := by omega
        nlinarith
      have hDLe : D ≤ Zj := by
        dsimp [D]
        linarith
      exact
        le_trans hPowLeD (le_trans hDLe hZjLe)
  have hBoundCast :
      (2 : ℤ) ^ residualQJumpExponent a j ≤
        4 * (P.yNat : ℤ) := by
    rw [P.yNat_cast hy]
    exact hBoundInt
  have hNat :
      2 ^ residualQJumpExponent a j ≤ 4 * P.yNat := by
    exact_mod_cast hBoundCast
  simpa [a] using hNat

/--
corridor-free Stage 8R2 の unconditional presentation。

`rho=0` は情報ゼロ branch として明示的に残し、
nontrivial branch では dyadic bound を得る。
-/
theorem criticalizationStart_residualQJump_zero_or_dyadic_bound
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    {j : ℕ}
    (hStartTwo : 2 ≤ P.criticalizationStart)
    (hj : 9 ≤ j)
    (hBlockEndNext :
      P.criticalizationStart + criticalPowerP (j + 1) ≤ P.m) :
    residualQJumpExponent P.criticalizationStart j = 0 ∨
      2 ^ residualQJumpExponent P.criticalizationStart j ≤
        4 * P.yNat := by
  by_cases hZero :
      residualQJumpExponent P.criticalizationStart j = 0
  · exact Or.inl hZero
  · right
    apply
      P.criticalizationStart_residualQJump_dyadic_bound
        hy
        hStartTwo
        hj
        hBlockEndNext
    omega

/-! ## 8. old full-q-jump compatibility, now corridor-free -/

/--
旧 precision 仮定 `beta(a)<Q_j` を置く場合は `rho=Q_(j+1)-Q_j>0`。

したがって旧 full-q-jump bound は、二本の corridor 条件なしで回収される。
-/
theorem criticalizationStart_fullQJump_dyadic_bound_of_precision_residual
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    {j : ℕ}
    (hStartTwo : 2 ≤ P.criticalizationStart)
    (hj : 9 ≤ j)
    (hBlockEndNext :
      P.criticalizationStart + criticalPowerP (j + 1) ≤ P.m)
    (hPrecision :
      beattyIndex P.criticalizationStart < criticalPowerQ j) :
    2 ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ≤
      4 * P.yNat := by
  have hEq :=
    residualQJumpExponent_eq_full_of_precision
      (a := P.criticalizationStart)
      (j := j)
      hj
      hPrecision
  have hQlt :
      criticalPowerQ j < criticalPowerQ (j + 1) :=
    criticalPowerQ_lt_next hj
  have hRhoPos :
      0 <
        residualQJumpExponent P.criticalizationStart j := by
    rw [hEq]
    omega
  have hBound :=
    P.criticalizationStart_residualQJump_dyadic_bound
      hy
      hStartTwo
      hj
      hBlockEndNext
      hRhoPos
  rw [hEq] at hBound
  exact hBound

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
