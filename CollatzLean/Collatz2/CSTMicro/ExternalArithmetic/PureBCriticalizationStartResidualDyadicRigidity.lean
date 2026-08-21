import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBRelativeChristoffelDefectValuation

/-!
# Pure B Stage 8R: criticalization start の residual dyadic rigidity

旧 Stage 8
`PureBCriticalizationStartDyadicRigidity.lean`
では、canonical adjacent corrected Wronskian の full precision を使うために

  beattyIndex a < criticalPowerQ j

を仮定し、

  2^(Q_(j+1)-Q_j) ∣ (Z_(a+P_j)-Z_a)

を得ていた。

しかし full q-jump を最初から要求する必要はない。
canonical Wronskian が持つ strong precision

  S_j = Q_j + Q_(j+1) - 1

から phase cost `beta(a)` と block factor `Q_j` を差し引いた残余を

  rho(a,j)
    := min
         (Q_(j+1)-Q_j)
         (S_j - (beta(a)+Q_j))

とする。

この Stage 8R では `beta(a) < Q_j` を完全に削除し、

  2^rho(a,j) ∣ (Z_(a+P_j)-Z_a)

を証明する。criticalization start で state difference は nonzero なので、
uniform state bound と合わせて

  2^rho(a,j) <= 4*yNat

を得る。

旧 precision 仮定 `beta(a) < Q_j` が成立する場合には
`rho(a,j)=Q_(j+1)-Q_j` となるため、旧 Stage 8 の full q-jump は
この residual theorem の特殊ケースとして回収される。

重要:
* このファイルは旧 Stage 8 を import しない。
* `PureBGoodScaleCounterexample.lean` も import しない。
* 旧 Stage 8 と counterexample は archive / diagnostic record として残し、
  live aggregate からは外すことを想定している。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/--
Stage 8R の residual dyadic exponent。

`S_j` を corrected Wronskian の canonical strong precision とすると

  rho(a,j) = min(Q_(j+1)-Q_j, S_j-(beta(a)+Q_j)).

第一項は adjacent denominator jump そのもの。
第二項は phase `a` と first block factor `2^Q_j` を消したあとに
Wronskian から実際に残る precision。
-/
def residualQJumpExponent (a j : ℕ) : ℕ :=
  min
    (criticalPowerQ (j + 1) - criticalPowerQ j)
    (actualCriticalContinuedFractionData.strongPrecision j -
      (beattyIndex a + criticalPowerQ j))

/--
residual exponent の phase-loss 表示。

`S_j = Q_j + Q_(j+1) - 1` を代入すると

  rho(a,j)
    = min(Q_(j+1)-Q_j, Q_(j+1)-1-beta(a)).

これは `a=1000, j=9` の diagnostic counterexample で現れた
exact loss と同じ形である。
-/
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
旧 Stage 8 の precision 仮定を置けば residual exponent は full q-jump に戻る。

したがって Stage 8R は旧 Stage 8B の真の一般化になっている。
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

/--
8R-A: integral tail の canonical standard block defect は endpoint state difference の
exact pure-two-power multiple。

corridor 内では block の Beatty rise が exact に `Q_j` なので

  B_j(a) = F[a,a+P_j](Z_a)
         = 2^Q_j (Z_(a+P_j)-Z_a).

旧 8A と数学内容は同じだが、旧 Stage 8 を import せず live route を独立させるため
ここで再証明する。
-/
theorem integralCanonicalBlockDefect_eq_twoPow_mul_stateDifference_residual
    (P : PureBProfileObstruction)
    {a j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hBlockEnd : a + criticalPowerP j ≤ P.m)
    (hj : 9 ≤ j)
    (hRange :
      a + criticalPowerP j < criticalPowerP (j + 1)) :
    P.integralCanonicalBlockDefect A j =
      (2 : ℤ) ^ criticalPowerQ j *
        (P.integralCriticalTailStateInt
            A (a + criticalPowerP j) (by omega) hBlockEnd -
          P.integralCriticalTailStateInt A a le_rfl A.1) := by
  have hRise :
      beattyIndex (a + criticalPowerP j) - beattyIndex a =
        criticalPowerQ j := by
    have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
    by_cases hjOdd : j % 2 = 1
    · have hShift0 :=
        actual_beattyIndex_add_currentP_eq_add_Q_of_odd
          (j := j)
          (x := a)
          hj
          hjOdd
          (by
            simpa [Nat.add_comm] using hRange)
      have hShift :
          beattyIndex (a + criticalPowerP j) =
            criticalPowerQ j + beattyIndex a := by
        rw [Nat.add_comm a (criticalPowerP j)]
        exact hShift0
      omega
    · have hjEven : j % 2 = 0 := by omega
      have hShift0 :=
        actual_beattyIndex_add_currentP_eq_add_Q_of_even
          (j := j)
          (x := a)
          hj
          hjEven
          haPos
          (by
            simpa [Nat.add_comm] using hRange)
      have hShift :
          beattyIndex (a + criticalPowerP j) =
            criticalPowerQ j + beattyIndex a := by
        rw [Nat.add_comm a (criticalPowerP j)]
        exact hShift0
      omega
  have hLeft :=
    P.criticalIntervalDefectZ_at_integralLeftState
      (A := A)
      (s := a)
      (r := criticalPowerP j)
      le_rfl
      hBlockEnd
  rw [hRise] at hLeft
  simpa [integralCanonicalBlockDefect] using hLeft

/--
8R-B: corrected Wronskian の strong precision を「使えるだけ」使う。

旧 8B は `beta(a) < Q_j` により full exponent
`Q_(j+1)-Q_j` を要求していた。

ここでは

  rho = min(
    Q_(j+1)-Q_j,
    strongPrecision(j) - (beta(a)+Q_j))

だけを取り出す。したがって追加の `hPrecision` は不要。

結論:

  2^rho | Z_(a+P_j)-Z_a.
-/
theorem twoPow_residualQJump_dvd_integralStateDifference
    (P : PureBProfileObstruction)
    {a j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hBlockEndJ : a + criticalPowerP j ≤ P.m)
    (hBlockEndNext : a + criticalPowerP (j + 1) ≤ P.m)
    (hj : 9 ≤ j)
    (hRangeJ :
      a + criticalPowerP j < criticalPowerP (j + 1))
    (hRangeNext :
      a + criticalPowerP (j + 1) < criticalPowerP (j + 2)) :
    (2 : ℤ) ^ residualQJumpExponent a j ∣
      (P.integralCriticalTailStateInt
          A (a + criticalPowerP j) (by omega) hBlockEndJ -
        P.integralCriticalTailStateInt A a le_rfl A.1) := by
  let r : ℕ := residualQJumpExponent a j
  change
    (2 : ℤ) ^ r ∣
      (P.integralCriticalTailStateInt
          A (a + criticalPowerP j) (by omega) hBlockEndJ -
        P.integralCriticalTailStateInt A a le_rfl A.1)
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
  have hJ0 :=
    P.integralCanonicalBlockDefect_eq_twoPow_mul_stateDifference_residual
      (A := A)
      haPos
      hBlockEndJ
      hj
      hRangeJ
  have hJ :
      P.integralCanonicalBlockDefect A j =
        (2 : ℤ) ^ criticalPowerQ j * Dj := by
    simpa [Dj, Zj, Za] using hJ0
  have hN0 :=
    P.integralCanonicalBlockDefect_eq_twoPow_mul_stateDifference_residual
      (A := A)
      (j := j + 1)
      haPos
      hBlockEndNext
      (by omega)
      hRangeNext
  have hN :
      P.integralCanonicalBlockDefect A (j + 1) =
        (2 : ℤ) ^ criticalPowerQ (j + 1) * Dn := by
    simpa [Dn, Zn, Za] using hN0
  have hCross :=
    P.integralCanonicalBlockDefect_adjacentWronskian
      (A := A)
      haPos
      hj
      hRangeJ
      hRangeNext
  have hStrong :
      actualCriticalContinuedFractionData.strongPrecision j =
        criticalPowerQ j + criticalPowerQ (j + 1) - 1 := by
    simp [actualCriticalContinuedFractionData]
  by_cases hBudget :
      beattyIndex a + criticalPowerQ j ≤
        actualCriticalContinuedFractionData.strongPrecision j
  · have hRLeJump :
        r ≤ criticalPowerQ (j + 1) - criticalPowerQ j := by
      dsimp [r, residualQJumpExponent]
      exact min_le_left _ _
    have hRLeLoss :
        r ≤
          actualCriticalContinuedFractionData.strongPrecision j -
            (beattyIndex a + criticalPowerQ j) := by
      dsimp [r, residualQJumpExponent]
      exact min_le_right _ _
    have hExpLe :
        beattyIndex a + (criticalPowerQ j + r) ≤
          actualCriticalContinuedFractionData.strongPrecision j := by
      omega
    have hPurePowDvd :
        (2 : ℤ) ^ (beattyIndex a + (criticalPowerQ j + r)) ∣
          (2 : ℤ) ^
            actualCriticalContinuedFractionData.strongPrecision j := by
      refine ⟨
        (2 : ℤ) ^
          (actualCriticalContinuedFractionData.strongPrecision j -
            (beattyIndex a + (criticalPowerQ j + r))),
        ?_⟩
      have hSplit :
          actualCriticalContinuedFractionData.strongPrecision j =
            (beattyIndex a + (criticalPowerQ j + r)) +
              (actualCriticalContinuedFractionData.strongPrecision j -
                (beattyIndex a + (criticalPowerQ j + r))) := by
        omega
      rw [hSplit, pow_add]
      simp
    have hWronskianDvd :
        (2 : ℤ) ^ (beattyIndex a + (criticalPowerQ j + r)) ∣
          correctedChristoffelWronskianNext
            actualCriticalContinuedFractionData j := by
      rcases
          actualCorrectedChristoffelWronskianNext_signed_strongPrecision
            hj with
        hEven | hOdd
      · rw [hEven.2]
        exact dvd_neg.mpr hPurePowDvd
      · rw [hOdd.2]
        exact hPurePowDvd
    have hRhsDvd :
        (2 : ℤ) ^ (beattyIndex a + (criticalPowerQ j + r)) ∣
          (3 : ℤ) ^ (a - 1) *
            correctedChristoffelWronskianNext
              actualCriticalContinuedFractionData j :=
      dvd_mul_of_dvd_right hWronskianDvd _
    have hLeftDvd :
        (2 : ℤ) ^ (beattyIndex a + (criticalPowerQ j + r)) ∣
          (2 : ℤ) ^ beattyIndex a *
            (actualCriticalRawPowerGap (j + 1) *
                P.integralCanonicalBlockDefect A j -
              actualCriticalRawPowerGap j *
                P.integralCanonicalBlockDefect A (j + 1)) := by
      rw [hCross]
      exact hRhsDvd
    have hCrossDvd :
        (2 : ℤ) ^ (criticalPowerQ j + r) ∣
          (actualCriticalRawPowerGap (j + 1) *
              P.integralCanonicalBlockDefect A j -
            actualCriticalRawPowerGap j *
              P.integralCanonicalBlockDefect A (j + 1)) := by
      rcases hLeftDvd with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      have hPowSplit :
          (2 : ℤ) ^ (beattyIndex a + (criticalPowerQ j + r)) =
            (2 : ℤ) ^ beattyIndex a *
              (2 : ℤ) ^ (criticalPowerQ j + r) := by
        rw [pow_add]
      have hTwoNe : (2 : ℤ) ^ beattyIndex a ≠ 0 := by
        positivity
      apply mul_left_cancel₀ hTwoNe
      calc
        (2 : ℤ) ^ beattyIndex a *
            (actualCriticalRawPowerGap (j + 1) *
                P.integralCanonicalBlockDefect A j -
              actualCriticalRawPowerGap j *
                P.integralCanonicalBlockDefect A (j + 1))
            =
          (2 : ℤ) ^ (beattyIndex a + (criticalPowerQ j + r)) * u := hu
        _ =
          (2 : ℤ) ^ beattyIndex a *
            ((2 : ℤ) ^ (criticalPowerQ j + r) * u) := by
              rw [hPowSplit]
              ring
    rw [hJ, hN] at hCrossDvd
    have hQlt :
        criticalPowerQ j < criticalPowerQ (j + 1) :=
      criticalPowerQ_lt_next hj
    have hQRLe :
        criticalPowerQ j + r ≤ criticalPowerQ (j + 1) := by
      omega
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
      have hAdd := dvd_add hCrossDvd hSecond
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
    have hDj :
        (2 : ℤ) ^ r ∣ Dj :=
      hGapCoprime.dvd_of_dvd_mul_left hProduct
    simpa [Dj, Zj, Za] using hDj
  · have hLossZero :
        actualCriticalContinuedFractionData.strongPrecision j -
            (beattyIndex a + criticalPowerQ j) = 0 := by
      omega
    have hrZero : r = 0 := by
      dsimp [r, residualQJumpExponent]
      rw [hLossZero]
      simp
    rw [hrZero]
    simp

/--
8R-C: canonical arithmetic criticalization start では standard-period shift による
state return は起こらない。

この部分は旧 8C と同じで、`hPrecision` を一切使っていない。
もし `Z_(a+P_j)=Z_a` なら、P-periodicity により one-cell Beatty gap も
`a-1 -> a` と `a+P_j-1 -> a+P_j` で一致する。integral recurrence を一歩戻すと
`terminalRawTail(a-1)` に extra factor 3 が入り、`a` の minimality に矛盾する。
-/
theorem criticalizationStart_integralState_ne_of_standardShift_residual
    (P : PureBProfileObstruction)
    {j : ℕ}
    (hStartTwo : 2 ≤ P.criticalizationStart)
    (hj : 9 ≤ j)
    (hBlockEnd :
      P.criticalizationStart + criticalPowerP j ≤ P.m)
    (hRange :
      P.criticalizationStart + criticalPowerP j <
        criticalPowerP (j + 1)) :
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
  have haPos : 0 < a := by
    omega
  have hPPos : 0 < criticalPowerP j :=
    criticalPowerP_pos (by omega)
  have hShiftA :
      beattyIndex (a + criticalPowerP j) =
        criticalPowerQ j + beattyIndex a := by
    have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
    by_cases hjOdd : j % 2 = 1
    · have h :=
        actual_beattyIndex_add_currentP_eq_add_Q_of_odd
          (j := j) (x := a) hj hjOdd
          (by simpa [Nat.add_comm] using hRange)
      rw [Nat.add_comm a (criticalPowerP j)]
      exact h
    · have hjEven : j % 2 = 0 := by
        omega
      have h :=
        actual_beattyIndex_add_currentP_eq_add_Q_of_even
          (j := j) (x := a) hj hjEven haPos
          (by simpa [Nat.add_comm] using hRange)
      rw [Nat.add_comm a (criticalPowerP j)]
      exact h
  have hRangePred :
      criticalPowerP j + (a - 1) <
        criticalPowerP (j + 1) := by
    omega
  have hShiftPred0 :
      beattyIndex (criticalPowerP j + (a - 1)) =
        criticalPowerQ j + beattyIndex (a - 1) := by
    have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
    by_cases hjOdd : j % 2 = 1
    · exact
        actual_beattyIndex_add_currentP_eq_add_Q_of_odd
          (j := j) (x := a - 1) hj hjOdd hRangePred
    · have hjEven : j % 2 = 0 := by
        omega
      exact
        actual_beattyIndex_add_currentP_eq_add_Q_of_even
          (j := j) (x := a - 1) hj hjEven (by omega) hRangePred
  have hShiftPred :
      beattyIndex (a + criticalPowerP j - 1) =
        criticalPowerQ j + beattyIndex (a - 1) := by
    have hIndex :
        criticalPowerP j + (a - 1) =
          a + criticalPowerP j - 1 := by
      omega
    rw [← hIndex]
    exact hShiftPred0
  have hGapEq :
      beattyIndex (a + criticalPowerP j) -
          beattyIndex (a + criticalPowerP j - 1) =
        beattyIndex a - beattyIndex (a - 1) := by
    rw [hShiftA, hShiftPred]
    omega
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
/--
8R-D: residual divisibility、criticalization-start nonreturn、
uniform `0 <= Z_s <= 4y` を合わせる。

旧 Stage 8D の `hPrecision` は完全に消え、残る仮定は

  a + P_(j+1) <= m
  a + P_j     < P_(j+1)
  a + P_(j+1) < P_(j+2)

の三つだけ。

結論:

  2^rho(a,j) <= 4*yNat.
-/
theorem criticalizationStart_residualQJump_dyadic_bound
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    {j : ℕ}
    (hStartTwo : 2 ≤ P.criticalizationStart)
    (hj : 9 ≤ j)
    (hBlockEndNext :
      P.criticalizationStart + criticalPowerP (j + 1) ≤ P.m)
    (hRangeJ :
      P.criticalizationStart + criticalPowerP j <
        criticalPowerP (j + 1))
    (hRangeNext :
      P.criticalizationStart + criticalPowerP (j + 1) <
        criticalPowerP (j + 2)) :
    2 ^ residualQJumpExponent P.criticalizationStart j ≤
      4 * P.yNat := by
  let a := P.criticalizationStart
  let A : IsIntegralCriticalTail P a :=
    P.criticalizationStart_spec
  have haTwo : 2 ≤ a := by
    simpa [a] using hStartTwo
  have haPos : 0 < a := by
    omega
  have hPmono :
      criticalPowerP j < criticalPowerP (j + 1) :=
    criticalPowerP_strict_succ (r := j) (by omega)
  have hBlockEndJ :
      a + criticalPowerP j ≤ P.m := by
    have hNext :
        a + criticalPowerP (j + 1) ≤ P.m := by
      simpa [a] using hBlockEndNext
    omega
  have hRangeJ' :
      a + criticalPowerP j < criticalPowerP (j + 1) := by
    simpa [a] using hRangeJ
  have hRangeNext' :
      a + criticalPowerP (j + 1) <
        criticalPowerP (j + 2) := by
    simpa [a] using hRangeNext
  have hEndNext :
      a + criticalPowerP (j + 1) ≤ P.m := by
    simpa [a] using hBlockEndNext
  have hDiv :=
    P.twoPow_residualQJump_dvd_integralStateDifference
      (A := A)
      haPos
      hBlockEndJ
      hEndNext
      hj
      hRangeJ'
      hRangeNext'
  have hNe :=
    P.criticalizationStart_integralState_ne_of_standardShift_residual
      (j := j)
      hStartTwo
      hj
      (by simpa [a] using hBlockEndJ)
      hRangeJ
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
      have huOne : (1 : ℤ) ≤ u := by
        omega
      have hPowLeNeg :
          (2 : ℤ) ^ residualQJumpExponent a j ≤ -D := by
        rw [hu]
        nlinarith
      have hNegLe : -D ≤ Za := by
        dsimp [D]
        linarith
      exact
        le_trans hPowLeNeg (le_trans hNegLe hZaLe)
    · rcases hDivD with ⟨u, hu⟩
      have huPos : 0 < u := by
        nlinarith
      have huOne : (1 : ℤ) ≤ u := by
        omega
      have hPowLeD :
          (2 : ℤ) ^ residualQJumpExponent a j ≤ D := by
        rw [hu]
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
8R-E: 旧 full-q-jump bound は residual theorem の特殊ケースとして回収できる。

この theorem は compatibility checkpoint。
live route の本体は `criticalizationStart_residualQJump_dyadic_bound` であり、
今後の scale selection は residual exponent を直接評価する。
-/
theorem criticalizationStart_fullQJump_dyadic_bound_of_precision_residual
    (P : PureBProfileObstruction)
    (hy : 0 ≤ P.y)
    {j : ℕ}
    (hStartTwo : 2 ≤ P.criticalizationStart)
    (hj : 9 ≤ j)
    (hBlockEndNext :
      P.criticalizationStart + criticalPowerP (j + 1) ≤ P.m)
    (hRangeJ :
      P.criticalizationStart + criticalPowerP j <
        criticalPowerP (j + 1))
    (hRangeNext :
      P.criticalizationStart + criticalPowerP (j + 1) <
        criticalPowerP (j + 2))
    (hPrecision :
      beattyIndex P.criticalizationStart < criticalPowerQ j) :
    2 ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ≤
      4 * P.yNat := by
  have hResidual :=
    P.criticalizationStart_residualQJump_dyadic_bound
      hy
      hStartTwo
      hj
      hBlockEndNext
      hRangeJ
      hRangeNext
  rw [
    residualQJumpExponent_eq_full_of_precision
      hj hPrecision
  ] at hResidual
  exact hResidual

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
