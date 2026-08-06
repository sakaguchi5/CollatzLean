import CollatzLean.CollatzSecondLayer3.NoCriticalDiscountedSpecialC3
import CollatzLean.CollatzOrbitCore.PeriodicExponent

/-!
# first critical transition towerの三分岐
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

def CriticalCaptureAtTime
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (t : ℕ) : Prop :=
  ∃ C : CriticalCaptureInFirstDeferred F, C.time = t

private theorem exists_criticalCaptureAtTime
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (h : Nonempty (CriticalCaptureInFirstDeferred F)) :
    ∃ t : ℕ, CriticalCaptureAtTime F t := by
  rcases h with ⟨C⟩
  exact ⟨C.time, C, rfl⟩

noncomputable def firstCriticalTime
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (h : Nonempty (CriticalCaptureInFirstDeferred F)) : ℕ := by
  classical
  exact Nat.find (exists_criticalCaptureAtTime F h)

noncomputable def firstCriticalCertificate
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (h : Nonempty (CriticalCaptureInFirstDeferred F)) :
    CriticalCaptureInFirstDeferred F := by
  classical
  exact Classical.choose (Nat.find_spec (exists_criticalCaptureAtTime F h))

theorem firstCriticalCertificate_time
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (h : Nonempty (CriticalCaptureInFirstDeferred F)) :
    (firstCriticalCertificate F h).time = firstCriticalTime F h := by
  classical
  exact Classical.choose_spec (Nat.find_spec (exists_criticalCaptureAtTime F h))

theorem noCriticalBefore_firstCriticalTime
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (F : O.FiniteCaptureNormalizationData D₀)
    (h : Nonempty (CriticalCaptureInFirstDeferred F))
    {t : ℕ}
    (ht : t < firstCriticalTime F h) :
    ¬ CriticalCaptureAtTime F t := by
  classical
  intro hcritical
  have hmin : firstCriticalTime F h ≤ t :=
    Nat.find_min' (exists_criticalCaptureAtTime F h) hcritical
  omega

structure FirstCriticalTransitionTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) where
  source : StandardNormalizationGeneratedObstructionTowerData hGap O
  firstDeferred : FirstDeferredNormalizationTowerData source
  select : ℕ → ℕ
  select_strict : StrictMono select
  terminalSuperPolynomial : ∀ K A : ℕ,
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      K * (firstDeferred.windowLength (select j) + 1) ^ A <
        firstDeferred.terminalEndpoint (select j)
  criticalExists : ∀ j : ℕ,
    Nonempty (CriticalCaptureInFirstDeferred (firstDeferred.data (select j)))

namespace FirstCriticalTransitionTowerData

noncomputable def firstCritical
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) :
    CriticalCaptureInFirstDeferred (R.firstDeferred.data (R.select j)) :=
  firstCriticalCertificate _ (R.criticalExists j)

noncomputable def firstCriticalTime
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) : ℕ :=
  CollatzSecondLayer2.firstCriticalTime _ (R.criticalExists j)

@[simp] theorem firstCritical_time_eq
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) :
    (R.firstCritical j).time = R.firstCriticalTime j :=
  firstCriticalCertificate_time _ (R.criticalExists j)

theorem noCriticalBefore
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j t : ℕ)
    (ht : t < R.firstCriticalTime j) :
    ¬ CriticalCaptureAtTime (R.firstDeferred.data (R.select j)) t :=
  noCriticalBefore_firstCriticalTime _ (R.criticalExists j) ht

def windowLength
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) : ℕ :=
  R.firstDeferred.windowLength (R.select j)

noncomputable def start
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) : ℕ :=
  R.firstDeferred.start (R.select j)

noncomputable def postCriticalStart
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) : ℕ :=
  R.start j + R.firstCriticalTime j + 1

noncomputable def postCriticalWord
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) : ExpWord :=
  O.segmentWord (R.postCriticalStart j) (R.windowLength j)

noncomputable def postCriticalDefect
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) : ℕ :=
  expandingDefect (R.postCriticalWord j) (O.value (R.postCriticalStart j))

theorem postCriticalWord_expanding
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) :
    Expanding (R.postCriticalWord j) := by
  have h := (R.firstCritical j).afterExpanding
  simpa [Expanding, postCriticalWord, postCriticalStart,
    FirstCriticalTransitionTowerData.start,
    FirstCriticalTransitionTowerData.windowLength,
    FirstDeferredNormalizationTowerData.start,
    FirstDeferredNormalizationTowerData.windowLength,
    StandardNormalizationGeneratedObstructionTowerData.start,
    StandardNormalizationGeneratedObstructionTowerData.windowLength,
    PolynomialPreparedFullWindowFamily.start,
    OddOrbit.windowTwoSteps, oddSteps, Nat.add_assoc] using h

theorem postCriticalDefect_pos
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) :
    0 < R.postCriticalDefect j := by
  have hB := affineConst_pos_of_nonempty
    (nonempty_of_expanding (R.postCriticalWord_expanding j))
  dsimp [postCriticalDefect, expandingDefect]
  omega

def LargeExpandingDefectAt
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) : Prop :=
  (2 ^ twoSteps (R.postCriticalWord j)) ^ R.windowLength j ≤
    R.postCriticalDefect j

def TerminalSpecialC3At
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ) : Prop :=
  Nonempty (SpecialC3At O
    (R.start j + R.firstDeferred.terminalTime (R.select j))
    (R.windowLength j))

end FirstCriticalTransitionTowerData

structure LargeExpandingDefectTransitionTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) where
  source : FirstCriticalTransitionTowerData hGap O
  select : ℕ → ℕ
  select_strict : StrictMono select
  large : ∀ j : ℕ, source.LargeExpandingDefectAt (select j)

structure TerminalSpecialC3TransitionTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) where
  source : FirstCriticalTransitionTowerData hGap O
  select : ℕ → ℕ
  select_strict : StrictMono select
  special : ∀ j : ℕ, source.TerminalSpecialC3At (select j)

structure CaptureDenseTransitionTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) where
  source : FirstCriticalTransitionTowerData hGap O
  select : ℕ → ℕ
  select_strict : StrictMono select
  terminalNotSpecial : ∀ j : ℕ, ¬ source.TerminalSpecialC3At (select j)
  smallDefect : ∀ j : ℕ, ¬ source.LargeExpandingDefectAt (select j)
  shortOrNextCapture : ∀ j : ℕ,
    let n := select j
    let C := source.firstCritical n
    let q := source.windowLength n
    let F := source.firstDeferred.data (source.select n)
    F.terminalTime < C.time + 1 + q * q ∨
      ∃ k : ℕ, C.time + 1 ≤ k ∧ k < C.time + 1 + q * q ∧
        Nonempty (O.CapturedWindowAt (source.start n + k) q)

inductive FirstCriticalTransitionOutcomeTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) : Type
  | largeExpandingDefect
      (data : LargeExpandingDefectTransitionTowerData hGap O)
  | captureDenseTransition
      (data : CaptureDenseTransitionTowerData hGap O)
  | terminalSpecialC3
      (data : TerminalSpecialC3TransitionTowerData hGap O)

namespace ExpWord

theorem finiteRepeatedRealization_defect_balance
    {w : ExpWord} (hexpanding : Expanding w)
    {x : ℕ → ℕ} {N : ℕ}
    (hrealizes : ∀ n : ℕ, n < N → Realizes w (x n) (x (n + 1))) :
    ∀ n : ℕ, n ≤ N →
      (2 ^ twoSteps w) ^ n * expandingDefect w (x n) =
        (3 ^ oddSteps w) ^ n * expandingDefect w (x 0) := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
      have hnlt : n < N := by omega
      have hstep := expandingDefect_transport hexpanding (hrealizes n hnlt)
      have hprev := ih (by omega)
      calc
        (2 ^ twoSteps w) ^ (n + 1) * expandingDefect w (x (n + 1))
            = (2 ^ twoSteps w) ^ n *
                (2 ^ twoSteps w * expandingDefect w (x (n + 1))) := by
                  rw [pow_succ]; ring
        _ = (2 ^ twoSteps w) ^ n *
              (3 ^ oddSteps w * expandingDefect w (x n)) := by rw [hstep]
        _ = 3 ^ oddSteps w *
              ((2 ^ twoSteps w) ^ n * expandingDefect w (x n)) := by ring
        _ = 3 ^ oddSteps w *
              ((3 ^ oddSteps w) ^ n * expandingDefect w (x 0)) := by rw [hprev]
        _ = (3 ^ oddSteps w) ^ (n + 1) * expandingDefect w (x 0) := by
              rw [pow_succ]; ring

theorem finiteRepeatedRealization_basePow_dvd_initialDefect
    {w : ExpWord} (hexpanding : Expanding w)
    {x : ℕ → ℕ} {N : ℕ}
    (hrealizes : ∀ n : ℕ, n < N → Realizes w (x n) (x (n + 1)))
    (n : ℕ) (hn : n ≤ N) :
    (2 ^ twoSteps w) ^ n ∣ expandingDefect w (x 0) := by
  have hbalance := finiteRepeatedRealization_defect_balance
    hexpanding hrealizes n hn
  have hdvdProduct : (2 ^ twoSteps w) ^ n ∣
      (3 ^ oddSteps w) ^ n * expandingDefect w (x 0) :=
    ⟨expandingDefect w (x n), hbalance.symm⟩
  have h23 : Nat.Coprime 2 3 := by decide
  have hbaseCoprime := h23.pow (twoSteps w) (oddSteps w)
  have hpowersCoprime := hbaseCoprime.pow n n
  exact hpowersCoprime.dvd_of_dvd_mul_left hdvdProduct

end ExpWord

namespace OddOrbit

theorem segmentWord_add_period_eq_of_range
    (O : OddOrbit) {anchor q L : ℕ}
    (hperiod : ∀ t : ℕ, t < L →
      O.exponent (anchor + t + q) = O.exponent (anchor + t)) :
    ∀ t m : ℕ, t + m ≤ L →
      O.segmentWord (anchor + t + q) m = O.segmentWord (anchor + t) m := by
  intro t m
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
      intro hbound
      simp only [segmentWord_succ]
      rw [hperiod t (by omega)]
      have htail := ih (t + 1) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

end OddOrbit

namespace FirstCriticalTransitionTowerData

theorem expanding_after_firstCritical
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j u : ℕ)
    (hu : R.firstCriticalTime j + 1 + u ≤
      (R.firstDeferred.data (R.select j)).terminalTime) :
    Expanding (O.segmentWord (R.postCriticalStart j + u) (R.windowLength j)) := by
  let F := R.firstDeferred.data (R.select j)
  let q := R.windowLength j
  let t0 := R.firstCriticalTime j + 1
  have hbase : 2 ^ O.windowTwoSteps (R.start j + t0) q < 3 ^ q := by
    have h := R.postCriticalWord_expanding j
    simpa [Expanding, postCriticalWord, postCriticalStart,
      OddOrbit.windowTwoSteps, oddSteps, q, t0, Nat.add_assoc] using h
  have hprop : ∀ n : ℕ, t0 + n ≤ F.terminalTime →
      2 ^ O.windowTwoSteps (R.start j + t0 + n) q < 3 ^ q := by
    intro n
    induction n with
    | zero => intro _; simpa using hbase
    | succ n ih =>
      intro hn
      have hnlt : t0 + n < F.terminalTime := by omega
      have hprev := ih (by omega)
      rcases F.before (t0 + n) hnlt with ⟨C | S⟩
      · have hdrop : O.windowTwoSteps (R.start j + t0 + (n + 1)) q <
            O.windowTwoSteps (R.start j + t0 + n) q := by
          simpa [F, q, FirstCriticalTransitionTowerData.start,
            FirstCriticalTransitionTowerData.windowLength,
            FirstDeferredNormalizationTowerData.start,
            FirstDeferredNormalizationTowerData.windowLength,
            StandardNormalizationGeneratedObstructionTowerData.start,
            StandardNormalizationGeneratedObstructionTowerData.windowLength,
            PolynomialPreparedFullWindowFamily.start, Nat.add_assoc] using
            C.windowTwoSteps_strict_decrease
        exact lt_trans (Nat.pow_lt_pow_right (by omega : 1 < (2 : ℕ)) hdrop) hprev
      · have heq : O.windowTwoSteps (R.start j + t0 + (n + 1)) q =
            O.windowTwoSteps (R.start j + t0 + n) q := by
          simpa [F, q, FirstCriticalTransitionTowerData.start,
            FirstCriticalTransitionTowerData.windowLength,
            FirstDeferredNormalizationTowerData.start,
            FirstDeferredNormalizationTowerData.windowLength,
            StandardNormalizationGeneratedObstructionTowerData.start,
            StandardNormalizationGeneratedObstructionTowerData.windowLength,
            PolynomialPreparedFullWindowFamily.start, Nat.add_assoc] using
            S.windowTwoSteps_eq
        simpa [heq] using hprev
  have h := hprop u (by simpa [F, t0] using hu)
  simpa [Expanding, OddOrbit.windowTwoSteps, oddSteps,
    postCriticalStart, q, t0, Nat.add_assoc] using h

noncomputable def postCriticalSample
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j n : ℕ) : ℕ :=
  O.value (R.postCriticalStart j + n * R.windowLength j)

theorem postCriticalExponent_periodic_of_noCaptureBeforeSquare
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ)
    (hinside : R.firstCriticalTime j + 1 +
      R.windowLength j * R.windowLength j ≤
      (R.firstDeferred.data (R.select j)).terminalTime)
    (hNoCapture : ∀ k : ℕ,
      R.firstCriticalTime j + 1 ≤ k →
      k < R.firstCriticalTime j + 1 + R.windowLength j * R.windowLength j →
      ¬ Nonempty (O.CapturedWindowAt (R.start j + k) (R.windowLength j))) :
    ∀ t : ℕ, t < R.windowLength j * R.windowLength j →
      O.exponent (R.postCriticalStart j + t + R.windowLength j) =
        O.exponent (R.postCriticalStart j + t) := by
  classical
  intro t ht
  let F := R.firstDeferred.data (R.select j)
  let q := R.windowLength j
  have htime : R.firstCriticalTime j + 1 + t < F.terminalTime := by
    dsimp [F]; omega
  have hNo : ¬ Nonempty (O.CapturedWindowAt
      (R.start j + (R.firstCriticalTime j + 1 + t)) q) := by
    apply hNoCapture
    · omega
    · omega
  let S := F.synchronized_of_not_captured
    (R.firstCriticalTime j + 1 + t) htime hNo
  have h := S.upperExponent_eq_lower
  simpa [F, q, postCriticalStart, FirstCriticalTransitionTowerData.start,
    FirstCriticalTransitionTowerData.windowLength,
    FirstDeferredNormalizationTowerData.start,
    FirstDeferredNormalizationTowerData.windowLength,
    StandardNormalizationGeneratedObstructionTowerData.start,
    StandardNormalizationGeneratedObstructionTowerData.windowLength,
    PolynomialPreparedFullWindowFamily.start,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem postCriticalBlockWord_eq_of_periodic
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ)
    (hperiod : ∀ t : ℕ, t < R.windowLength j * R.windowLength j →
      O.exponent (R.postCriticalStart j + t + R.windowLength j) =
        O.exponent (R.postCriticalStart j + t)) :
    ∀ n : ℕ, n < R.windowLength j →
      O.segmentWord (R.postCriticalStart j + n * R.windowLength j)
        (R.windowLength j) = R.postCriticalWord j := by
  intro n hn
  induction n with
  | zero => simp [postCriticalWord]
  | succ n ih =>
      have hnq : (n + 1) * R.windowLength j ≤
          R.windowLength j * R.windowLength j :=
        Nat.mul_le_mul_right (R.windowLength j) (by omega)
      have hshift := O.segmentWord_add_period_eq_of_range hperiod
        (n * R.windowLength j) (R.windowLength j)
        (by simpa [Nat.succ_mul] using hnq)
      have hprev := ih (by omega)
      simpa [Nat.succ_mul, Nat.add_assoc] using hshift.trans hprev

theorem postCriticalBlock_realizes_of_word_eq
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ)
    (hword : ∀ n : ℕ, n < R.windowLength j →
      O.segmentWord (R.postCriticalStart j + n * R.windowLength j)
        (R.windowLength j) = R.postCriticalWord j) :
    ∀ n : ℕ, n < R.windowLength j →
      Realizes (R.postCriticalWord j)
        (R.postCriticalSample j n) (R.postCriticalSample j (n + 1)) := by
  intro n hn
  have hrun := O.realizes_segment
    (R.postCriticalStart j + n * R.windowLength j) (R.windowLength j)
  rw [hword n hn] at hrun
  have hend : R.postCriticalStart j + n * R.windowLength j + R.windowLength j =
      R.postCriticalStart j + (n + 1) * R.windowLength j := by ring
  simpa [postCriticalSample, hend] using hrun

theorem largeExpandingDefectAt_of_noCaptureBeforeSquare
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ)
    (hinside : R.firstCriticalTime j + 1 + R.windowLength j * R.windowLength j ≤
      (R.firstDeferred.data (R.select j)).terminalTime)
    (hNoCapture : ∀ k : ℕ,
      R.firstCriticalTime j + 1 ≤ k →
      k < R.firstCriticalTime j + 1 + R.windowLength j * R.windowLength j →
      ¬ Nonempty (O.CapturedWindowAt (R.start j + k) (R.windowLength j))) :
    R.LargeExpandingDefectAt j := by
  classical
  have hperiod := R.postCriticalExponent_periodic_of_noCaptureBeforeSquare
    j hinside hNoCapture
  have hword := R.postCriticalBlockWord_eq_of_periodic j hperiod
  have hrealizes := R.postCriticalBlock_realizes_of_word_eq j hword
  have hdvd : (2 ^ twoSteps (R.postCriticalWord j)) ^ R.windowLength j ∣
      expandingDefect (R.postCriticalWord j) (R.postCriticalSample j 0) :=
    ExpWord.finiteRepeatedRealization_basePow_dvd_initialDefect
      (R.postCriticalWord_expanding j) hrealizes (R.windowLength j) le_rfl
  have hDpos : 0 < expandingDefect
      (R.postCriticalWord j) (R.postCriticalSample j 0) := by
    simpa [postCriticalSample, postCriticalDefect] using R.postCriticalDefect_pos j
  have hle := Nat.le_of_dvd hDpos hdvd
  simpa [LargeExpandingDefectAt, postCriticalSample, postCriticalDefect] using hle

theorem shortOrNextCapture_of_smallDefect
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) (j : ℕ)
    (hsmall : ¬ R.LargeExpandingDefectAt j) :
    let C := R.firstCritical j
    let q := R.windowLength j
    let F := R.firstDeferred.data (R.select j)
    F.terminalTime < C.time + 1 + q * q ∨
      ∃ k : ℕ, C.time + 1 ≤ k ∧ k < C.time + 1 + q * q ∧
        Nonempty (O.CapturedWindowAt (R.start j + k) q) := by
  classical
  dsimp
  rw [R.firstCritical_time_eq j]
  by_cases hshort : (R.firstDeferred.data (R.select j)).terminalTime <
      R.firstCriticalTime j + 1 + R.windowLength j * R.windowLength j
  · exact Or.inl hshort
  · right
    by_contra hNoCapture
    push Not at hNoCapture
    have hinside : R.firstCriticalTime j + 1 +
        R.windowLength j * R.windowLength j ≤
      (R.firstDeferred.data (R.select j)).terminalTime := Nat.le_of_not_gt hshort
    have hNoCapture' : ∀ k : ℕ,
        R.firstCriticalTime j + 1 ≤ k →
        k < R.firstCriticalTime j + 1 + R.windowLength j * R.windowLength j →
        ¬ Nonempty (O.CapturedWindowAt (R.start j + k) (R.windowLength j)) := by
      intro k hkLower hkUpper hcap
      rcases hcap with ⟨C⟩
      exact (hNoCapture k hkLower hkUpper).false C
    apply hsmall
    exact R.largeExpandingDefectAt_of_noCaptureBeforeSquare j hinside hNoCapture'

end FirstCriticalTransitionTowerData

noncomputable def firstCriticalTransitionTowerOfPersistent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (hPolynomial : ¬ HasPersistentPolynomialTerminalBound T)
    (hCritical : HasPersistentCriticalCapture T) :
    FirstCriticalTransitionTowerData hGap O := by
  classical
  let P : ℕ → Prop := fun j => Nonempty (CriticalCaptureInFirstDeferred (T.data j))
  let select := Persistently.select P hCritical
  refine
    { source := D
      firstDeferred := T
      select := select
      select_strict := Persistently.select_strict P hCritical
      terminalSuperPolynomial := ?_
      criticalExists := ?_ }
  · intro K A
    obtain ⟨N, hN⟩ := terminalSuperPolynomial_of_not_persistent T hPolynomial K A
    refine ⟨N, ?_⟩
    intro j hj
    apply hN (select j)
    exact le_trans hj (Persistently.select_ge P hCritical j)
  · intro j
    exact Persistently.select_spec P hCritical j

noncomputable def terminalSpecialTowerOfPersistent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (h : Persistently R.TerminalSpecialC3At) :
    TerminalSpecialC3TransitionTowerData hGap O where
  source := R
  select := Persistently.select R.TerminalSpecialC3At h
  select_strict := Persistently.select_strict R.TerminalSpecialC3At h
  special := Persistently.select_spec R.TerminalSpecialC3At h

noncomputable def largeDefectTowerOfPersistent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (h : Persistently R.LargeExpandingDefectAt) :
    LargeExpandingDefectTransitionTowerData hGap O where
  source := R
  select := Persistently.select R.LargeExpandingDefectAt h
  select_strict := Persistently.select_strict R.LargeExpandingDefectAt h
  large := Persistently.select_spec R.LargeExpandingDefectAt h

noncomputable def captureDenseTowerOfExclusions
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (hTerminal : ¬ Persistently R.TerminalSpecialC3At)
    (hLarge : ¬ Persistently R.LargeExpandingDefectAt) :
    CaptureDenseTransitionTowerData hGap O := by
  classical
  let hTerminalEventually := Persistently.eventually_not_of_not
    R.TerminalSpecialC3At hTerminal
  let Nt : ℕ := Classical.choose hTerminalEventually
  have hNt := Classical.choose_spec hTerminalEventually
  let hLargeEventually := Persistently.eventually_not_of_not
    R.LargeExpandingDefectAt hLarge
  let Nl : ℕ := Classical.choose hLargeEventually
  have hNl := Classical.choose_spec hLargeEventually
  let N := max Nt Nl
  let select : ℕ → ℕ := fun j => N + j
  refine
    { source := R
      select := select
      select_strict := by intro a b hab; exact Nat.add_lt_add_left hab N
      terminalNotSpecial := ?_
      smallDefect := ?_
      shortOrNextCapture := ?_ }
  · intro j
    apply hNt (select j)
    dsimp [select, N]
    omega
  · intro j
    apply hNl (select j)
    dsimp [select, N]
    omega
  · intro j
    apply R.shortOrNextCapture_of_smallDefect
    apply hNl (select j)
    dsimp [select, N]
    omega

theorem firstCriticalTransition_classification
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) :
    Nonempty (LargeExpandingDefectTransitionTowerData hGap O) ∨
      Nonempty (CaptureDenseTransitionTowerData hGap O) ∨
      Nonempty (TerminalSpecialC3TransitionTowerData hGap O) := by
  classical
  by_cases hTerminal : Persistently R.TerminalSpecialC3At
  · exact Or.inr (Or.inr ⟨terminalSpecialTowerOfPersistent R hTerminal⟩)
  · by_cases hLarge : Persistently R.LargeExpandingDefectAt
    · exact Or.inl ⟨largeDefectTowerOfPersistent R hLarge⟩
    · exact Or.inr (Or.inl ⟨captureDenseTowerOfExclusions R hTerminal hLarge⟩)

theorem firstCriticalTransition_outcome
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) :
    Nonempty (FirstCriticalTransitionOutcomeTowerData hGap O) := by
  rcases firstCriticalTransition_classification R with hL | hD | hS
  · exact ⟨.largeExpandingDefect (Classical.choice hL)⟩
  · exact ⟨.captureDenseTransition (Classical.choice hD)⟩
  · exact ⟨.terminalSpecialC3 (Classical.choice hS)⟩

end CollatzSecondLayer2
