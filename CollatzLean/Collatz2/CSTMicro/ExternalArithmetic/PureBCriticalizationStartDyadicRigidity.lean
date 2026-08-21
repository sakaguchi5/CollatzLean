import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBRelativeChristoffelDefectValuation

/-!
# Pure B Stage 8: criticalization start の dyadic rigidity

Stage 6 の canonical adjacent Wronskian を 3-adic ではなく 2-adic に読む。

8A. canonical block defect は integral state difference の pure two-power 倍。
8B. adjacent corrected Wronskian から denominator jump の two-power が state difference を割る。
8C. criticalization start ではその state difference は zero になれない。
8D. uniform state bound と合わせて denominator jump 自体を `4*yNat` で抑える。

最終形は

  2^(Q_(j+1)-Q_j) <= 4*yNat

であり、後段では convergent denominator growth と直接衝突させる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/--
8A: integral tail の canonical standard block defect は endpoint state difference の
exact pure-two-power multiple。

corridor 内では block の Beatty rise が exact に `Q_j` なので

  B_j(a) = F[a,a+P_j](Z_a)
         = 2^Q_j (Z_(a+P_j)-Z_a).
-/
theorem integralCanonicalBlockDefect_eq_twoPow_mul_stateDifference
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
8B: Stage 6 Wronskian の 2-adic side。

`beta(a) < Q_j` なら corrected Wronskian の pure two-power は
`2^(beta(a)+Q_(j+1))` を含む。8A を consecutive pair に代入して共通 factor を消すと

  2^(Q_(j+1)-Q_j) | Z_(a+P_j)-Z_a

が得られる。
-/
theorem twoPow_qJump_dvd_integralStateDifference
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
      a + criticalPowerP (j + 1) < criticalPowerP (j + 2))
    (hPrecision : beattyIndex a < criticalPowerQ j) :
    (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ∣
      (P.integralCriticalTailStateInt
          A (a + criticalPowerP j) (by omega) hBlockEndJ -
        P.integralCriticalTailStateInt A a le_rfl A.1) := by
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
    P.integralCanonicalBlockDefect_eq_twoPow_mul_stateDifference
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
    P.integralCanonicalBlockDefect_eq_twoPow_mul_stateDifference
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
  have hExpLe :
      beattyIndex a + criticalPowerQ (j + 1) ≤
        actualCriticalContinuedFractionData.strongPrecision j := by
    rw [hStrong]
    omega
  have hPurePowDvd :
      (2 : ℤ) ^ (beattyIndex a + criticalPowerQ (j + 1)) ∣
        (2 : ℤ) ^
          actualCriticalContinuedFractionData.strongPrecision j := by
    refine ⟨
      (2 : ℤ) ^
        (actualCriticalContinuedFractionData.strongPrecision j -
          (beattyIndex a + criticalPowerQ (j + 1))),
      ?_⟩
    have hSplit :
        actualCriticalContinuedFractionData.strongPrecision j =
          (beattyIndex a + criticalPowerQ (j + 1)) +
            (actualCriticalContinuedFractionData.strongPrecision j -
              (beattyIndex a + criticalPowerQ (j + 1))) := by
      omega
    rw [hSplit, pow_add]
    simp
  have hWronskianDvd :
      (2 : ℤ) ^ (beattyIndex a + criticalPowerQ (j + 1)) ∣
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
      (2 : ℤ) ^ (beattyIndex a + criticalPowerQ (j + 1)) ∣
        (3 : ℤ) ^ (a - 1) *
          correctedChristoffelWronskianNext
            actualCriticalContinuedFractionData j :=
    dvd_mul_of_dvd_right hWronskianDvd _
  have hLeftDvd :
      (2 : ℤ) ^ (beattyIndex a + criticalPowerQ (j + 1)) ∣
        (2 : ℤ) ^ beattyIndex a *
          (actualCriticalRawPowerGap (j + 1) *
              P.integralCanonicalBlockDefect A j -
            actualCriticalRawPowerGap j *
              P.integralCanonicalBlockDefect A (j + 1)) := by
    rw [hCross]
    exact hRhsDvd
  have hCrossDvd :
      (2 : ℤ) ^ criticalPowerQ (j + 1) ∣
        (actualCriticalRawPowerGap (j + 1) *
            P.integralCanonicalBlockDefect A j -
          actualCriticalRawPowerGap j *
            P.integralCanonicalBlockDefect A (j + 1)) := by
    rcases hLeftDvd with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have hPowSplit :
        (2 : ℤ) ^ (beattyIndex a + criticalPowerQ (j + 1)) =
          (2 : ℤ) ^ beattyIndex a *
            (2 : ℤ) ^ criticalPowerQ (j + 1) := by
      rw [pow_add]
    have hTwoNe : (2 : ℤ) ^ beattyIndex a ≠ 0 := by positivity
    apply mul_left_cancel₀ hTwoNe
    calc
      (2 : ℤ) ^ beattyIndex a *
          (actualCriticalRawPowerGap (j + 1) *
              P.integralCanonicalBlockDefect A j -
            actualCriticalRawPowerGap j *
              P.integralCanonicalBlockDefect A (j + 1))
          =
        (2 : ℤ) ^ (beattyIndex a + criticalPowerQ (j + 1)) * u := hu
      _ =
        (2 : ℤ) ^ beattyIndex a *
          ((2 : ℤ) ^ criticalPowerQ (j + 1) * u) := by
            rw [hPowSplit]
            ring
  rw [hJ, hN] at hCrossDvd
  have hSecond :
      (2 : ℤ) ^ criticalPowerQ (j + 1) ∣
        actualCriticalRawPowerGap j *
          ((2 : ℤ) ^ criticalPowerQ (j + 1) * Dn) := by
    refine ⟨actualCriticalRawPowerGap j * Dn, ?_⟩
    ring
  have hFirst :
      (2 : ℤ) ^ criticalPowerQ (j + 1) ∣
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
  have hQlt : criticalPowerQ j < criticalPowerQ (j + 1) :=
    criticalPowerQ_lt_next hj
  have hQSplit :
      criticalPowerQ (j + 1) =
        criticalPowerQ j +
          (criticalPowerQ (j + 1) - criticalPowerQ j) := by
    omega
  have hProduct :
      (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ∣
        actualCriticalRawPowerGap (j + 1) * Dj := by
    rcases hFirst with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    have hPowSplit :
        (2 : ℤ) ^ criticalPowerQ (j + 1) =
          (2 : ℤ) ^ criticalPowerQ j *
            (2 : ℤ) ^
              (criticalPowerQ (j + 1) - criticalPowerQ j) := by
      rw [hQSplit, pow_add]
      simp
    have hTwoNe : (2 : ℤ) ^ criticalPowerQ j ≠ 0 := by positivity
    apply mul_left_cancel₀ hTwoNe
    calc
      (2 : ℤ) ^ criticalPowerQ j *
          (actualCriticalRawPowerGap (j + 1) * Dj) =
        actualCriticalRawPowerGap (j + 1) *
          ((2 : ℤ) ^ criticalPowerQ j * Dj) := by ring
      _ = (2 : ℤ) ^ criticalPowerQ (j + 1) * u := hu
      _ =
        (2 : ℤ) ^ criticalPowerQ j *
          ((2 : ℤ) ^
              (criticalPowerQ (j + 1) - criticalPowerQ j) * u) := by
            rw [hPowSplit]
            ring
  have hGapCoprime :
      IsCoprime
        ((2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j))
        (actualCriticalRawPowerGap (j + 1)) := by
    have h23 : IsCoprime (2 : ℤ) (3 : ℤ) := by
      refine ⟨-1, 1, ?_⟩
      norm_num
    have hBase :
        IsCoprime
          ((2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j))
          ((3 : ℤ) ^ criticalPowerP (j + 1)) := by
      exact h23.pow
    rcases hBase with ⟨u, v, huv⟩
    refine ⟨
      u + v * (2 : ℤ) ^ criticalPowerQ j,
      -v,
      ?_⟩
    unfold actualCriticalRawPowerGap
    have hTwoSplit :
        (2 : ℤ) ^ criticalPowerQ (j + 1) =
          (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) *
            (2 : ℤ) ^ criticalPowerQ j := by
      rw [hQSplit, pow_add]
      ring_nf
      simp
    rw [hTwoSplit]
    calc
      (u + v * (2 : ℤ) ^ criticalPowerQ j) *
            (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) +
          (-v) *
            ((2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) *
                (2 : ℤ) ^ criticalPowerQ j -
              (3 : ℤ) ^ criticalPowerP (j + 1))
          =
        u * (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) +
          v * (3 : ℤ) ^ criticalPowerP (j + 1) := by
            ring
      _ = 1 := huv
  have hDj :
      (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ∣ Dj :=
    hGapCoprime.dvd_of_dvd_mul_left hProduct
  simpa [Dj, Zj, Za] using hDj

/--
8C: canonical arithmetic criticalization start では standard-period shift による
state return は起こらない。

もし `Z_(a+P_j)=Z_a` なら、P-periodicity により one-cell Beatty gap も
`a-1 -> a` と `a+P_j-1 -> a+P_j` で一致する。integral recurrence を一歩戻すと
`terminalRawTail(a-1)` に extra factor 3 が入り、`a` の minimality に矛盾する。
-/
theorem criticalizationStart_integralState_ne_of_standardShift
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
  have haTwo : 2 ≤ a := by simpa [a] using hStartTwo
  have haPos : 0 < a := by omega
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
    · have hjEven : j % 2 = 0 := by omega
      have h :=
        actual_beattyIndex_add_currentP_eq_add_Q_of_even
          (j := j) (x := a) hj hjEven haPos
          (by simpa [Nat.add_comm] using hRange)
      rw [Nat.add_comm a (criticalPowerP j)]
      exact h
  have hRangePred :
      criticalPowerP j + (a - 1) < criticalPowerP (j + 1) := by
    omega
  have hShiftPred0 :
      beattyIndex (criticalPowerP j + (a - 1)) =
        criticalPowerQ j + beattyIndex (a - 1) := by
    have hmod : j % 2 < 2 := Nat.mod_lt j (by decide)
    by_cases hjOdd : j % 2 = 1
    · exact
        actual_beattyIndex_add_currentP_eq_add_Q_of_odd
          (j := j) (x := a - 1) hj hjOdd hRangePred
    · have hjEven : j % 2 = 0 := by omega
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
  have hStepStart : a ≤ a + criticalPowerP j - 1 := by
    omega
  have hStepLt : a + criticalPowerP j - 1 < P.m := by
    omega
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
              (Nat.le_of_lt hStepLt) +
          1 := by
    simpa [hSucc, hGapEq] using hRec0
  have hReturn' :
      P.integralCriticalTailStateInt
          A (a + criticalPowerP j) (by omega) hBlockEnd =
        P.integralCriticalTailStateInt A a le_rfl A.1 := by
    simpa using hReturn
  rw [hReturn'] at hRec
  have hBracket :
      (2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
          P.integralCriticalTailStateInt A a le_rfl A.1 - 1 =
        3 *
          P.integralCriticalTailStateInt
            A (a + criticalPowerP j - 1) hStepStart (by omega) := by
    linarith
  have hRaw0 :=
    P.terminalRawTail_step_raw
      (s := a - 1)
      (by omega : a - 1 < P.m)
  have hPredSucc : (a - 1) + 1 = a := by omega
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
  have hPrev : IsIntegralCriticalTail P (a - 1) := by
    constructor
    · omega
    · refine ⟨
        P.integralCriticalTailStateInt
          A (a + criticalPowerP j - 1) hStepStart (by omega),
        ?_⟩
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
              (3 : ℤ) ^ (P.m - a) := by
                exact congrArg
                  (fun z : ℤ =>
                    (2 : ℤ) ^
                        (beattyIndex a - beattyIndex (a - 1)) * z -
                      (3 : ℤ) ^ (P.m - a))
                  hSpecA
        _ =
            (3 : ℤ) ^ (P.m - a) *
              ((2 : ℤ) ^ (beattyIndex a - beattyIndex (a - 1)) *
                  P.integralCriticalTailStateInt A a le_rfl A.1 - 1) := by
                ring
        _ =
            (3 : ℤ) ^ (P.m - a) *
              (3 *
                P.integralCriticalTailStateInt
                  A (a + criticalPowerP j - 1) hStepStart (by omega)) := by
                rw [hBracket]
        _ =
            ((3 : ℤ) ^ (P.m - a) * 3) *
              P.integralCriticalTailStateInt
                A (a + criticalPowerP j - 1) hStepStart (by omega) := by
                ring
  have hMin := P.criticalizationStart_minimal hPrev
  change a ≤ a - 1 at hMin
  omega

/--
8D: 8B の divisibility、8C の nonreturn、uniform `0 <= Z_s <= 4y` を合わせる。

nonzero state difference が `2^(Q_(j+1)-Q_j)` の倍数なので、その two-power は
state range `4*y` を越えられない。Nat 化すると

  2^(Q_(j+1)-Q_j) <= 4*yNat.
-/
theorem criticalizationStart_adjacentQJump_dyadic_bound
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
  let a := P.criticalizationStart
  let A : IsIntegralCriticalTail P a := P.criticalizationStart_spec
  have haTwo : 2 ≤ a := by simpa [a] using hStartTwo
  have haPos : 0 < a := by omega
  have hPmono : criticalPowerP j < criticalPowerP (j + 1) :=
    criticalPowerP_strict_succ (r := j) (by omega)
  have hBlockEndJ : a + criticalPowerP j ≤ P.m := by
    have hNext : a + criticalPowerP (j + 1) ≤ P.m := by
      simpa [a] using hBlockEndNext
    omega
  have hRangeJ' : a + criticalPowerP j < criticalPowerP (j + 1) := by
    simpa [a] using hRangeJ
  have hRangeNext' :
      a + criticalPowerP (j + 1) < criticalPowerP (j + 2) := by
    simpa [a] using hRangeNext
  have hEndNext : a + criticalPowerP (j + 1) ≤ P.m := by
    simpa [a] using hBlockEndNext
  have hPrecision' : beattyIndex a < criticalPowerQ j := by
    simpa [a] using hPrecision
  have hDiv :=
    P.twoPow_qJump_dvd_integralStateDifference
      (A := A)
      haPos
      hBlockEndJ
      hEndNext
      hj
      hRangeJ'
      hRangeNext'
      hPrecision'
  have hNe :=
    P.criticalizationStart_integralState_ne_of_standardShift
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
      (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ∣ D := by
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
    exact P.integralCriticalTailStateInt_nonneg A hy le_rfl A.1
  have hZjNonneg : 0 ≤ Zj := by
    dsimp [Zj]
    exact
      P.integralCriticalTailStateInt_nonneg
        A hy (by omega) hBlockEndJ
  have hZaLe : Za ≤ 4 * P.y := by
    dsimp [Za]
    exact P.integralCriticalTailStateInt_le_four_y A hy le_rfl A.1
  have hZjLe : Zj ≤ 4 * P.y := by
    dsimp [Zj]
    exact
      P.integralCriticalTailStateInt_le_four_y
        A hy (by omega) hBlockEndJ
  have hPowPos :
      0 < (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) := by
    positivity
  have hBoundInt :
      (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ≤
        4 * P.y := by
    rcases lt_or_gt_of_ne hDNe with hDNeg | hDPos
    · have hDivNeg :
          (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ∣
            -D := dvd_neg.mpr hDivD
      rcases hDivNeg with ⟨u, hu⟩
      have huPos : 0 < u := by
        have hNegPos : 0 < -D := by linarith
        nlinarith
      have huOne : (1 : ℤ) ≤ u := by omega
      have hPowLeNeg :
          (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ≤
            -D := by
        rw [hu]
        nlinarith
      have hNegLe : -D ≤ Za := by
        dsimp [D]
        linarith
      exact le_trans hPowLeNeg (le_trans hNegLe hZaLe)
    · rcases hDivD with ⟨u, hu⟩
      have huPos : 0 < u := by
        nlinarith
      have huOne : (1 : ℤ) ≤ u := by omega
      have hPowLeD :
          (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ≤ D := by
        rw [hu]
        nlinarith
      have hDLe : D ≤ Zj := by
        dsimp [D]
        linarith
      exact le_trans hPowLeD (le_trans hDLe hZjLe)
  have hBoundCast :
      (2 : ℤ) ^ (criticalPowerQ (j + 1) - criticalPowerQ j) ≤
        4 * (P.yNat : ℤ) := by
    rw [P.yNat_cast hy]
    exact hBoundInt
  exact_mod_cast hBoundCast

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
