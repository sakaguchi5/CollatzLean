import CollatzLean.CollatzSecondLayer3.FirstCriticalTransition
import CollatzLean.CollatzSecondLayer3.ContractingWindowBounds
import CollatzLean.CollatzFirstLayer.DownwardReplay
import Mathlib.Data.Finset.Max

/-!
# first-critical枝のterminal三分岐

first-critical transitionの各項について、terminal deferred windowのcanonical replay
座標を調べる。

* terminal quotientが正なら、同じterminal語を一段下でactualに実行する
  deep lower-replay terminalを得る。
* terminal quotientが0でpredecessor shadowが正なら、最後のcaptureからterminalまでが
  q^2未満であるshort positive-shadow terminalを得る。
* terminal quotientが0でpredecessor shadowが負ならterminal Special C3である。

positive-shadow枝のshort性は、最後のcapture後にq^2段以上captureがなければ
同じexpanding q-wordがq回反復されてlarge defectになること、large defectなら
terminal quotientが正になることから従う。
-/

namespace CollatzSecondLayer2

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

private theorem nat_le_twoPow (n : ℕ) :
    n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hpos : 0 < 2 ^ n := Nat.pow_pos (by omega)
      omega

private theorem threePow_lt_fourPow_of_pos
    (n : ℕ) (hn : 0 < n) :
    3 ^ n < 4 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · have hi := ih (Nat.pos_of_ne_zero hn0)
        rw [pow_succ, pow_succ]
        calc
          3 ^ n * 3 < 4 ^ n * 3 :=
            (Nat.mul_lt_mul_right (by omega : 0 < (3 : ℕ))).2 hi
          _ < 4 ^ n * 4 :=
            (Nat.mul_lt_mul_left (Nat.pow_pos (by omega))).2 (by omega)

private theorem three_mul_threePow_lt_quadratic_twoPow
    (q : ℕ) (hq : 5 ≤ q) :
    3 * 3 ^ q < 2 ^ (q * (q - 2)) := by
  have hlinear : 2 * (q + 1) ≤ 3 * q := by omega
  have hsub : 3 ≤ q - 2 := by omega
  have hmul : 3 * q ≤ (q - 2) * q :=
    Nat.mul_le_mul_right q hsub
  have hexponent : 2 * (q + 1) ≤ q * (q - 2) := by
    calc
      2 * (q + 1) ≤ 3 * q := hlinear
      _ ≤ (q - 2) * q := hmul
      _ = q * (q - 2) := by ring
  calc
    3 * 3 ^ q = 3 ^ (q + 1) := by
      rw [pow_succ]
      ring
    _ < 4 ^ (q + 1) :=
      threePow_lt_fourPow_of_pos (q + 1) (by omega)
    _ = 2 ^ (2 * (q + 1)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
    _ ≤ 2 ^ (q * (q - 2)) :=
      Nat.pow_le_pow_right (by omega) hexponent

private theorem three_mul_threePow_lt_basePow_sub_two
    {q H : ℕ}
    (hq : 5 ≤ q)
    (hH : q ≤ H) :
    3 * 3 ^ q < (2 ^ H) ^ (q - 2) := by
  have hbase : 2 ^ q ≤ 2 ^ H :=
    Nat.pow_le_pow_right (by omega) hH
  calc
    3 * 3 ^ q < 2 ^ (q * (q - 2)) :=
      three_mul_threePow_lt_quadratic_twoPow q hq
    _ = (2 ^ q) ^ (q - 2) := by
      rw [pow_mul]
    _ ≤ (2 ^ H) ^ (q - 2) :=
      pow_le_pow_left' hbase (q - 2)

namespace CanonicalReplayCoordinate

/--
一段lower runにもcanonical replay座標を付ける。
そのquotientは元のquotientからexactに1減る。
-/
noncomputable def lowerRunReplayCoordinate
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (L : LowerNaturalRunReplayData w X Y)
    (hpos : 0 < C.quotient) :
    CanonicalReplayCoordinate w L.lowerStart L.lowerFinish := by
  let q := C.quotient - 1
  have hq : C.quotient = q + 1 := by
    dsimp [q]
    omega
  refine
    { quotient := q
      start_eq := ?_
      finish_eq := ?_ }
  · have hsum :
        canonicalStart w + residueModulus w * q + residueModulus w =
          L.lowerStart + residueModulus w := by
      calc
        canonicalStart w + residueModulus w * q + residueModulus w
            = canonicalStart w + residueModulus w * (q + 1) := by
                ring
        _ = canonicalStart w +
              residueModulus w * C.quotient := by
                rw [hq]
        _ = X := C.start_eq.symm
        _ = L.lowerStart + residueModulus w := L.start_step
    exact (Nat.add_right_cancel hsum).symm
  · let width := 2 * 3 ^ oddSteps w
    have hsum :
        canonicalEnd w + width * q + width =
          L.lowerFinish + width := by
      calc
        canonicalEnd w + width * q + width
            = canonicalEnd w + width * (q + 1) := by
                ring
        _ = canonicalEnd w + width * C.quotient := by
                rw [hq]
        _ = Y := by
                simpa [width] using C.finish_eq.symm
        _ = L.lowerFinish + width := by
                simpa [width] using L.finish_step
    exact (Nat.add_right_cancel hsum).symm

@[simp] theorem lowerRunReplayCoordinate_quotient
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (L : LowerNaturalRunReplayData w X Y)
    (hpos : 0 < C.quotient) :
    (lowerRunReplayCoordinate C L hpos).quotient =
      C.quotient - 1 := by
  rfl

/-- canonicalに選んだ一段lower runへ適用する短縮版。 -/
noncomputable def lowerNaturalRunReplayCoordinate
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (hRun : Runs w X Y)
    (hpos : 0 < C.quotient) :
    CanonicalReplayCoordinate w
      (C.lowerNaturalRunReplay hRun hpos).lowerStart
      (C.lowerNaturalRunReplay hRun hpos).lowerFinish :=
  lowerRunReplayCoordinate C (C.lowerNaturalRunReplay hRun hpos) hpos

@[simp] theorem lowerNaturalRunReplayCoordinate_quotient
    {w : ExpWord} {X Y : ℕ}
    (C : CanonicalReplayCoordinate w X Y)
    (hRun : Runs w X Y)
    (hpos : 0 < C.quotient) :
    (lowerNaturalRunReplayCoordinate C hRun hpos).quotient =
      C.quotient - 1 := by
  rfl

end CanonicalReplayCoordinate

namespace FirstCriticalTransitionTowerData

noncomputable def terminalTime
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) : ℕ :=
  R.firstDeferred.terminalTime (R.select j)

noncomputable def terminalStart
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) : ℕ :=
  R.start j + R.terminalTime j

noncomputable def terminalWord
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) : ExpWord :=
  O.segmentWord (R.terminalStart j) (R.windowLength j)

noncomputable def terminalPacket
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) :
    O.PreparedWindowPacket (R.terminalStart j) (R.windowLength j) := by
  have hsourceStart :
      R.source.start (R.firstDeferred.select (R.select j)) =
        R.source.crossing.minima.index
            (R.source.source.select
              (R.firstDeferred.select (R.select j))) +
          (movingFullWindowPreparation R.source.crossing
            (R.source.source.select
              (R.firstDeferred.select (R.select j)))).boundaryLength := by
    rfl
  simpa [
    terminalStart,
    terminalTime,
    FirstCriticalTransitionTowerData.start,
    FirstCriticalTransitionTowerData.windowLength,
    FirstDeferredNormalizationTowerData.start,
    FirstDeferredNormalizationTowerData.windowLength,
    FirstDeferredNormalizationTowerData.terminalTime,
    hsourceStart,
    Nat.add_assoc
  ] using
    (R.firstDeferred.data (R.select j)).terminalPacket
      (R.firstDeferred.windowLength_pos (R.select j))

noncomputable def terminalDeferred
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) :
    O.DeferredWindowAt (R.terminalStart j) (R.windowLength j) := by
  have hstart :
      R.source.start
          (R.firstDeferred.select (R.select j)) =
        R.source.crossing.minima.index
            (R.source.source.select
              (R.firstDeferred.select (R.select j))) +
          (polynomialPreparedFullWindowFamily
              hGap R.source.crossing).offset
            (R.source.source.select
              (R.firstDeferred.select (R.select j))) := by
    rfl
  have hlength :
      R.source.windowLength
          (R.firstDeferred.select (R.select j)) =
        R.source.crossing.crossingLength
          (R.source.source.select
            (R.firstDeferred.select (R.select j))) := by
    rfl
  simpa [
    terminalStart,
    terminalTime,
    FirstCriticalTransitionTowerData.start,
    FirstCriticalTransitionTowerData.windowLength,
    FirstDeferredNormalizationTowerData.start,
    FirstDeferredNormalizationTowerData.windowLength,
    FirstDeferredNormalizationTowerData.terminalTime,
    hstart,
    hlength,
    Nat.add_assoc
  ] using
    (R.firstDeferred.data (R.select j)).terminal

noncomputable def terminalReplayQuotient
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) : ℕ :=
  (R.terminalPacket j).replayCoordinate.quotient

noncomputable def terminalPredecessorShadow
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) : ℤ :=
  predecessorShadow (R.terminalWord j)

/-- terminal packetを同じ位置・同じ語の三枝へ直接分類する。 -/
theorem terminalOutcome_nonempty
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) :
    Nonempty (DeferredPreparedWindowOutcome (R.terminalPacket j)) := by
  classical
  let P := R.terminalPacket j
  let C := P.replayCoordinate
  by_cases hq0 : C.quotient = 0
  · have hstart :
        O.value (R.terminalStart j) =
          canonicalStart (R.terminalWord j) := by
      simpa [terminalWord] using
        C.start_eq_canonical_of_quotient_eq_zero hq0
    have hend :
        O.value (R.terminalStart j + R.windowLength j) =
          canonicalEnd (R.terminalWord j) := by
      have h := C.finish_eq
      rw [hq0] at h
      simpa [terminalWord] using h
    let W : ExpWord :=
      O.segmentWord (R.terminalStart j) (R.windowLength j)
    by_cases hneg : W.predecessorShadow < 0
    · exact
        ⟨DeferredPreparedWindowOutcome.special
          (specialC3At_of_deferred
            (R.terminalDeferred j)
            (by
              simpa [FirstCriticalTransitionTowerData.windowLength] using
                R.firstDeferred.windowLength_pos (R.select j))
            hstart
            hend
            (by
              simpa only [W] using hneg))⟩
    · by_cases hzero : W.predecessorShadow = 0
      · exact False.elim
          ((predecessorShadow_ne_zero W) hzero)
      · have hpos : 0 < W.predecessorShadow := by
          omega
        exact
          ⟨DeferredPreparedWindowOutcome.positivePredecessorShadow
            (by simpa [C] using hq0)
            (by
              simpa only [W] using hpos)⟩
  · have hqpos : 0 < C.quotient :=
      Nat.pos_of_ne_zero hq0
    exact
      ⟨DeferredPreparedWindowOutcome.lowerNaturalReplay
        (C.lowerNaturalRunReplay P.run hqpos)⟩

noncomputable def terminalOutcome
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) :
    DeferredPreparedWindowOutcome (R.terminalPacket j) :=
  Classical.choice (R.terminalOutcome_nonempty j)

end FirstCriticalTransitionTowerData

/-- terminalに一段下のactual canonical replayを持つ局所枝。 -/
structure DeepLowerReplayTerminalAt
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) where
  lowerReplay :
    LowerNaturalRunReplayData
      (R.terminalWord j)
      (O.value (R.terminalStart j))
      (O.value (R.terminalStart j + R.windowLength j))
  lowerCoordinate :
    CanonicalReplayCoordinate
      (R.terminalWord j)
      lowerReplay.lowerStart
      lowerReplay.lowerFinish
  quotient_pos : 0 < R.terminalReplayQuotient j
  quotient_decrement :
    lowerCoordinate.quotient + 1 = R.terminalReplayQuotient j
  modulus_deep :
    2 ^ (R.windowLength j + 1) ≤ residueModulus (R.terminalWord j)

/-- quotient 0・positive shadowで、最後のcaptureからq^2未満のterminal。 -/
structure ShortPositiveShadowTerminalAt
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) where
  anchorTime : ℕ
  firstCritical_le : R.firstCriticalTime j ≤ anchorTime
  anchor_lt_terminal : anchorTime < R.terminalTime j
  anchorCaptured :
    O.CapturedWindowAt (R.start j + anchorTime) (R.windowLength j)
  short :
    R.terminalTime j <
      anchorTime + 1 + R.windowLength j * R.windowLength j
  canonicalBoundary : R.terminalReplayQuotient j = 0
  positiveShadow : 0 < R.terminalPredecessorShadow j

namespace FirstCriticalTransitionTowerData

noncomputable def postCaptureStart
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ) : ℕ :=
  R.start j + k + 1

noncomputable def postCaptureWord
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ) : ExpWord :=
  O.segmentWord (R.postCaptureStart j k) (R.windowLength j)

noncomputable def postCaptureDefect
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ) : ℕ :=
  expandingDefect (R.postCaptureWord j k)
    (O.value (R.postCaptureStart j k))

/-- 任意のpost-capture anchorに対するlarge defect。 -/
def LargePostCaptureDefectAt
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ) : Prop :=
  (2 ^ twoSteps (R.postCaptureWord j k)) ^ R.windowLength j ≤
    R.postCaptureDefect j k


/-- terminal q-wordは非空。 -/
theorem terminalWord_nonempty
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) :
    R.terminalWord j ≠ [] := by
  apply segmentWord_nonempty_of_length_pos
  simpa [FirstCriticalTransitionTowerData.windowLength] using
    R.firstDeferred.windowLength_pos (R.select j)

/-- terminal replay modulusは少なくとも`2^(q+1)`。 -/
theorem terminalReplayModulus_deep
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) :
    2 ^ (R.windowLength j + 1) ≤
      residueModulus (R.terminalWord j) := by
  have hvalid : Valid (R.terminalWord j) := by
    exact (O.runs_segment (R.terminalStart j) (R.windowLength j)).valid
  have hlen := oddSteps_le_twoSteps hvalid
  have hqH : R.windowLength j ≤ twoSteps (R.terminalWord j) := by
    simpa [terminalWord, oddSteps] using hlen
  unfold residueModulus
  exact Nat.pow_le_pow_right (by omega) (by omega)

/-- captureではpost-critical window総指数が下降し、次windowもexpanding。 -/
theorem postCriticalCaptureDescent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j u : ℕ)
    (hinside :
      R.firstCriticalTime j + 1 + u < R.terminalTime j)
    (C : O.CapturedWindowAt
      (R.postCriticalStart j + u) (R.windowLength j)) :
    O.windowTwoSteps
        (R.postCriticalStart j + u + 1) (R.windowLength j) <
      O.windowTwoSteps
        (R.postCriticalStart j + u) (R.windowLength j) ∧
      Expanding
        (O.segmentWord
          (R.postCriticalStart j + u + 1)
          (R.windowLength j)) := by
  constructor
  · simpa [Nat.add_assoc] using C.windowTwoSteps_strict_decrease
  · apply R.expanding_after_firstCritical j (u + 1)
    simpa [
      FirstCriticalTransitionTowerData.terminalTime,
      FirstDeferredNormalizationTowerData.terminalTime,
      Nat.add_assoc
    ] using Nat.succ_le_of_lt hinside

/-- 任意のpost-capture q-block境界の値。 -/
noncomputable def postCaptureSample
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k n : ℕ) : ℕ :=
  O.value
    (R.postCaptureStart j k + n * R.windowLength j)

/--
post-capture後のq^2区間がterminal以前にあり、その区間にcaptureがなければ
指数列はq周期。
-/
theorem postCaptureExponent_periodic_of_noCaptureBeforeSquare
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hinside :
      k + 1 + R.windowLength j * R.windowLength j ≤
        R.terminalTime j)
    (hNoCapture :
      ∀ m : ℕ,
        k + 1 ≤ m →
        m < k + 1 + R.windowLength j * R.windowLength j →
        ¬ Nonempty
          (O.CapturedWindowAt
            (R.start j + m)
            (R.windowLength j))) :
    ∀ t : ℕ,
      t < R.windowLength j * R.windowLength j →
      O.exponent
          (R.postCaptureStart j k + t + R.windowLength j) =
        O.exponent (R.postCaptureStart j k + t) := by
  classical
  intro t ht
  let F := R.firstDeferred.data (R.select j)
  let q := R.windowLength j
  have htime : k + 1 + t < F.terminalTime := by
    dsimp [F]
    simpa [
      FirstCriticalTransitionTowerData.terminalTime,
      FirstDeferredNormalizationTowerData.terminalTime
    ] using
      (show k + 1 + t < R.terminalTime j by omega)
  have hNo :
      ¬ Nonempty
        (O.CapturedWindowAt
          (R.start j + (k + 1 + t)) q) := by
    apply hNoCapture (k + 1 + t)
    · omega
    · omega
  let S := F.synchronized_of_not_captured
    (k + 1 + t) htime hNo
  have h := S.upperExponent_eq_lower
  simpa [
    F,
    q,
    postCaptureStart,
    FirstCriticalTransitionTowerData.start,
    FirstCriticalTransitionTowerData.windowLength,
    FirstDeferredNormalizationTowerData.start,
    FirstDeferredNormalizationTowerData.windowLength,
    StandardNormalizationGeneratedObstructionTowerData.start,
    StandardNormalizationGeneratedObstructionTowerData.windowLength,
    PolynomialPreparedFullWindowFamily.start,
    Nat.add_assoc,
    Nat.add_comm,
    Nat.add_left_comm
  ] using h

/-- q周期なら最初のq個のq-blockは同じpost-capture word。 -/
theorem postCaptureBlockWord_eq_of_periodic
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hperiod :
      ∀ t : ℕ,
        t < R.windowLength j * R.windowLength j →
        O.exponent
            (R.postCaptureStart j k + t + R.windowLength j) =
          O.exponent (R.postCaptureStart j k + t)) :
    ∀ n : ℕ,
      n < R.windowLength j →
      O.segmentWord
          (R.postCaptureStart j k + n * R.windowLength j)
          (R.windowLength j) =
        R.postCaptureWord j k := by
  intro n hn
  induction n with
  | zero =>
      simp [postCaptureWord]
  | succ n ih =>
      have hnq :
          (n + 1) * R.windowLength j ≤
            R.windowLength j * R.windowLength j := by
        exact Nat.mul_le_mul_right
          (R.windowLength j)
          (by omega)
      have hshift :=
        O.segmentWord_add_period_eq_of_range
          hperiod
          (n * R.windowLength j)
          (R.windowLength j)
          (by simpa [Nat.succ_mul] using hnq)
      have hprev := ih (by omega)
      simpa [Nat.succ_mul, Nat.add_assoc] using hshift.trans hprev

/-- 同じq-wordが並ぶなら各sample間で同じ語が実現される。 -/
theorem postCaptureBlock_realizes_of_word_eq
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hword :
      ∀ n : ℕ,
        n < R.windowLength j →
        O.segmentWord
            (R.postCaptureStart j k + n * R.windowLength j)
            (R.windowLength j) =
          R.postCaptureWord j k) :
    ∀ n : ℕ,
      n < R.windowLength j →
      Realizes
        (R.postCaptureWord j k)
        (R.postCaptureSample j k n)
        (R.postCaptureSample j k (n + 1)) := by
  intro n hn
  have hrun :=
    O.realizes_segment
      (R.postCaptureStart j k + n * R.windowLength j)
      (R.windowLength j)
  rw [hword n hn] at hrun
  have hend :
      R.postCaptureStart j k + n * R.windowLength j +
          R.windowLength j =
        R.postCaptureStart j k + (n + 1) * R.windowLength j := by
    ring
  simpa [postCaptureSample, hend] using hrun

/--
q^2区間がterminal内にあり、その区間にcaptureがなければpost-capture defectはlarge。
-/
theorem largePostCaptureDefectAt_of_noCaptureBeforeSquare
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hexpanding : Expanding (R.postCaptureWord j k))
    (hinside :
      k + 1 + R.windowLength j * R.windowLength j ≤
        R.terminalTime j)
    (hNoCapture :
      ∀ m : ℕ,
        k + 1 ≤ m →
        m < k + 1 + R.windowLength j * R.windowLength j →
        ¬ Nonempty
          (O.CapturedWindowAt
            (R.start j + m)
            (R.windowLength j))) :
    R.LargePostCaptureDefectAt j k := by
  classical
  have hperiod :=
    R.postCaptureExponent_periodic_of_noCaptureBeforeSquare
      j k hinside hNoCapture
  have hword := R.postCaptureBlockWord_eq_of_periodic j k hperiod
  have hrealizes := R.postCaptureBlock_realizes_of_word_eq j k hword
  have hdvd :
      (2 ^ twoSteps (R.postCaptureWord j k)) ^ R.windowLength j ∣
        expandingDefect
          (R.postCaptureWord j k)
          (R.postCaptureSample j k 0) := by
    exact
      ExpWord.finiteRepeatedRealization_basePow_dvd_initialDefect
        hexpanding
        hrealizes
        (R.windowLength j)
        le_rfl
  have hDpos :
      0 < expandingDefect
          (R.postCaptureWord j k)
          (R.postCaptureSample j k 0) := by
    have hBpos := affineConst_pos_of_nonempty
      (nonempty_of_expanding hexpanding)
    dsimp [expandingDefect]
    omega
  have hle := Nat.le_of_dvd hDpos hdvd
  simpa [LargePostCaptureDefectAt, postCaptureDefect, postCaptureSample] using hle

/-- expanding語のactual realizationは開始値を真に増加させる。 -/
theorem value_lt_of_expanding_segment
    (O : OddOrbit)
    {s q : ℕ}
    (hexp : Expanding (O.segmentWord s q)) :
    O.value s < O.value (s + q) := by
  let w := O.segmentWord s q
  let C := 2 ^ twoSteps w
  let A := 3 ^ oddSteps w
  let B := affineConst w
  have hrun : C * O.value (s + q) = A * O.value s + B := by
    simpa [w, C, A, B, Realizes] using O.realizes_segment s q
  have hCA : C < A := by simpa [C, A, Expanding] using hexp
  have hBpos : 0 < B := by
    exact affineConst_pos_of_nonempty (nonempty_of_expanding hexp)
  by_contra hnot
  have hyx : O.value (s + q) ≤ O.value s := Nat.le_of_not_gt hnot
  have hleft : C * O.value (s + q) ≤ C * O.value s :=
    Nat.mul_le_mul_left C hyx
  have hmiddle : C * O.value s ≤ A * O.value s :=
    Nat.mul_le_mul_right (O.value s) hCA.le
  have hright : A * O.value s < A * O.value s + B := by omega
  omega

/-- large-defect gap恒等式の基礎。 -/
theorem postCaptureDefect_eq_twoPow_mul_gap
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hexpanding : Expanding (R.postCaptureWord j k)) :
    R.postCaptureDefect j k =
      2 ^ twoSteps (R.postCaptureWord j k) *
        (O.value (R.postCaptureStart j k + R.windowLength j) -
          O.value (R.postCaptureStart j k)) := by
  let w := R.postCaptureWord j k
  let s := R.postCaptureStart j k
  let x := O.value s
  let y := O.value (s + R.windowLength j)
  let C := 2 ^ twoSteps w
  let A := 3 ^ oddSteps w
  let B := affineConst w
  have hrun : C * y = A * x + B := by
    simpa [w, s, x, y, C, A, B, Realizes, postCaptureWord] using
      O.realizes_segment s (R.windowLength j)
  have hq : 0 < R.windowLength j :=
    R.firstDeferred.windowLength_pos (R.select j)
  have hword :
      Expanding
        (O.segmentWord s (R.windowLength j)) := by
    simpa [s, postCaptureWord] using hexpanding
  have hxy : x < y := by
    simpa [x, y] using
      value_lt_of_expanding_segment
        (O := O)
        (s := s)
        (q := R.windowLength j)
        hword
  have hy : y = x + (y - x) := by
    omega
  have hCA : C ≤ A := by
    simpa [C, A, w, Expanding] using hexpanding.le
  have hA : A = C + (A - C) :=
    (Nat.add_sub_of_le hCA).symm
  have hsum :
      C * x + C * (y - x) =
        C * x + ((A - C) * x + B) := by
    calc
      C * x + C * (y - x)
          = C * (x + (y - x)) := by
              ring
      _ = C * y := by
              rw [← hy]
      _ = A * x + B := hrun
      _ = (C + (A - C)) * x + B := by
            exact congrArg (fun n : ℕ => n * x + B) hA
      _ = C * x + ((A - C) * x + B) := by
              ring
  have hcancel :
      C * (y - x) = (A - C) * x + B :=
    Nat.add_left_cancel hsum
  simpa [
    postCaptureDefect,
    expandingDefect,
    w,
    s,
    x,
    y,
    C,
    A,
    B,
    oddSteps
  ] using hcancel.symm

/-- 第三命題：large defectはq-window gapへexactに移る。 -/
theorem largePostCaptureDefectGapIdentity
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hexpanding : Expanding (R.postCaptureWord j k))
    (hLarge : R.LargePostCaptureDefectAt j k) :
    (2 ^ twoSteps (R.postCaptureWord j k)) ^
        (R.windowLength j - 1) ≤
      O.value (R.postCaptureStart j k + R.windowLength j) -
        O.value (R.postCaptureStart j k) := by
  let C := 2 ^ twoSteps (R.postCaptureWord j k)
  let gap :=
    O.value (R.postCaptureStart j k + R.windowLength j) -
      O.value (R.postCaptureStart j k)
  have hq : 0 < R.windowLength j :=
    R.firstDeferred.windowLength_pos (R.select j)
  have hCpos : 0 < C := Nat.pow_pos (by omega)
  have hdefect := R.postCaptureDefect_eq_twoPow_mul_gap j k hexpanding
  have hmul : C ^ (R.windowLength j - 1) * C ≤ gap * C := by
    calc
      C ^ (R.windowLength j - 1) * C
          = C ^ R.windowLength j := by
            rw [← pow_succ]
            congr 1
            omega
      _ ≤ R.postCaptureDefect j k := by
            simpa [LargePostCaptureDefectAt, C] using hLarge
      _ = C * gap := by
            simpa [C, gap] using hdefect
      _ = gap * C := by ring
  have hmul' : C * C ^ (R.windowLength j - 1) ≤ C * gap := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact Nat.le_of_mul_le_mul_left hmul' hCpos

/-- 第四命題：large gapは深い2進部分か巨大奇数部分へ分かれる。 -/
theorem largePostCaptureDefectDepthOddSplit
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (D : O.WindowDifferenceData
      (R.postCaptureStart j k) (R.windowLength j))
    (hexpanding : Expanding (R.postCaptureWord j k))
    (hLarge : R.LargePostCaptureDefectAt j k) :
    let N := twoSteps (R.postCaptureWord j k) *
      (R.windowLength j - 1)
    N ≤ 2 * D.depth ∨
      2 ^ (N - D.depth) ≤ D.oddPart := by
  let H := twoSteps (R.postCaptureWord j k)
  let N := H * (R.windowLength j - 1)
  have hgap :=
    R.largePostCaptureDefectGapIdentity j k hexpanding hLarge
  have hgapEq :
      O.value (R.postCaptureStart j k + R.windowLength j) -
          O.value (R.postCaptureStart j k) =
        2 ^ D.depth * D.oddPart := by
    rw [D.difference]
    omega
  have hpowN :
      (2 ^ H) ^ (R.windowLength j - 1) = 2 ^ N := by
    dsimp [N]
    rw [pow_mul]
  have hN : 2 ^ N ≤ 2 ^ D.depth * D.oddPart := by
    calc
      2 ^ N = (2 ^ H) ^ (R.windowLength j - 1) := hpowN.symm
      _ ≤ O.value (R.postCaptureStart j k + R.windowLength j) -
            O.value (R.postCaptureStart j k) := by
          simpa [H] using hgap
      _ = 2 ^ D.depth * D.oddPart := hgapEq
  dsimp
  by_cases hdeep : N ≤ 2 * D.depth
  · exact Or.inl hdeep
  · right
    have hdN : D.depth ≤ N := by omega
    have hmul :
        2 ^ D.depth * 2 ^ (N - D.depth) ≤
          2 ^ D.depth * D.oddPart := by
      calc
        2 ^ D.depth * 2 ^ (N - D.depth)
            = 2 ^ N := by
              rw [← pow_add]
              congr 1
              omega
        _ ≤ 2 ^ D.depth * D.oddPart := hN
    exact Nat.le_of_mul_le_mul_left hmul (Nat.pow_pos (by omega))

/-- finite normalization内ではwindow総指数は時刻について非増加。 -/
theorem windowTwoSteps_antitone_before_terminal
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ)
    {a b : ℕ}
    (hab : a ≤ b)
    (hb : b ≤ R.terminalTime j) :
    O.windowTwoSteps (R.start j + b) (R.windowLength j) ≤
      O.windowTwoSteps (R.start j + a) (R.windowLength j) := by
  let F := R.firstDeferred.data (R.select j)
  induction b generalizing a with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      simp
  | succ b ih =>
      by_cases ha : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a ≤ b := by
          omega
        have hterminal :
            R.terminalTime j =
              (R.firstDeferred.data (R.select j)).terminalTime := by
          rfl
        have hbterm : b < F.terminalTime := by
          dsimp [F]
          rw [← hterminal]
          omega
        have hstep :
            O.windowTwoSteps (R.start j + (b + 1)) (R.windowLength j) ≤
              O.windowTwoSteps (R.start j + b) (R.windowLength j) := by
          rcases F.before b hbterm with ⟨C | S⟩
          · exact Nat.le_of_lt (by
              simpa [
                F,
                FirstCriticalTransitionTowerData.start,
                FirstCriticalTransitionTowerData.windowLength,
                FirstDeferredNormalizationTowerData.start,
                FirstDeferredNormalizationTowerData.windowLength,
                StandardNormalizationGeneratedObstructionTowerData.start,
                StandardNormalizationGeneratedObstructionTowerData.windowLength,
                PolynomialPreparedFullWindowFamily.start,
                Nat.add_assoc
              ] using C.windowTwoSteps_strict_decrease)
          · exact (by
              simpa [
                F,
                FirstCriticalTransitionTowerData.start,
                FirstCriticalTransitionTowerData.windowLength,
                FirstDeferredNormalizationTowerData.start,
                FirstDeferredNormalizationTowerData.windowLength,
                StandardNormalizationGeneratedObstructionTowerData.start,
                StandardNormalizationGeneratedObstructionTowerData.windowLength,
                PolynomialPreparedFullWindowFamily.start,
                Nat.add_assoc
              ] using S.windowTwoSteps_eq.le)
        exact hstep.trans (ih hab' (by omega))

/--
post-capture開始値は、terminalまで進んでも初期`2^H`倍以内には失われない。
-/
theorem postCaptureStart_le_base_mul_value
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hexpanding :
      ∀ u : ℕ,
        k + 1 + u ≤ R.terminalTime j →
        Expanding
          (O.segmentWord
            (R.postCaptureStart j k + u)
            (R.windowLength j))) :
    ∀ t : ℕ,
      k + 1 + t ≤ R.terminalTime j →
      O.value (R.postCaptureStart j k) ≤
        2 ^ twoSteps (R.postCaptureWord j k) *
          O.value (R.postCaptureStart j k + t) := by
  have hq : 0 < R.windowLength j :=
    R.firstDeferred.windowLength_pos (R.select j)
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro ht
      by_cases hsmall : t < R.windowLength j
      · let w := O.segmentWord (R.postCaptureStart j k) t
        let Ht := twoSteps w
        let H := twoSteps (R.postCaptureWord j k)
        have hsplit :=
          O.segmentWord_add
            (R.postCaptureStart j k)
            t
            (R.windowLength j - t)
        have hsum : Ht ≤ H := by
          have htq : t ≤ R.windowLength j := hsmall.le
          have hqeq : t + (R.windowLength j - t) = R.windowLength j := by omega
          have hs := congrArg twoSteps hsplit
          rw [twoSteps_append] at hs
          have hs' :
              Ht + twoSteps
                  (O.segmentWord
                    (R.postCaptureStart j k + t)
                    (R.windowLength j - t)) = H := by
            simpa [Ht, H, w, postCaptureWord, hqeq] using hs.symm
          omega
        have hpow : 2 ^ Ht ≤ 2 ^ H :=
          Nat.pow_le_pow_right (by omega) hsum
        have hrun := O.realizes_segment (R.postCaptureStart j k) t
        have hright :
            O.value (R.postCaptureStart j k) ≤
              2 ^ Ht * O.value (R.postCaptureStart j k + t) := by
          calc
            O.value (R.postCaptureStart j k)
                ≤ 3 ^ t * O.value (R.postCaptureStart j k) := by
                  have hone : 1 ≤ 3 ^ t := by
                    have hpos : 0 < 3 ^ t :=
                      Nat.pow_pos (by omega)
                    omega
                  simpa only [Nat.one_mul] using
                    Nat.mul_le_mul_right
                      (O.value (R.postCaptureStart j k))
                      hone
            _ ≤ 3 ^ t * O.value (R.postCaptureStart j k) +
                  affineConst w := by
                  omega
            _ = 2 ^ Ht *
                  O.value (R.postCaptureStart j k + t) := by
                  simpa [w, Ht, Realizes, oddSteps] using hrun.symm
        exact hright.trans
          (Nat.mul_le_mul_right
            (O.value (R.postCaptureStart j k + t))
            hpow)
      · have hqle : R.windowLength j ≤ t := Nat.le_of_not_gt hsmall
        let u := t - R.windowLength j
        have hut : u < t := by
          dsimp [u]
          omega
        have htu : u + R.windowLength j = t := by
          dsimp [u]
          omega
        have huinside : k + 1 + u ≤ R.terminalTime j := by omega
        have hi := ih u hut huinside
        have hexp := hexpanding u huinside
        have hlt :=
            value_lt_of_expanding_segment
              (O := O)
              (s := R.postCaptureStart j k + u)
              (q := R.windowLength j)
              hexp
        have hindex :
            R.postCaptureStart j k + u + R.windowLength j =
              R.postCaptureStart j k + t := by omega
        rw [hindex] at hlt
        exact hi.trans
          (Nat.mul_le_mul_left
            (2 ^ twoSteps (R.postCaptureWord j k)) hlt.le)

/-- large defectはpost-capture開始値を`2*(2^H)^2`以上にする。 -/
theorem postCaptureStart_large_of_largeDefect
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hq : 5 ≤ R.windowLength j)
    (hLarge : R.LargePostCaptureDefectAt j k) :
    2 * (2 ^ twoSteps (R.postCaptureWord j k)) ^ 2 ≤
      O.value (R.postCaptureStart j k) := by
  let q := R.windowLength j
  let w := R.postCaptureWord j k
  let H := twoSteps w
  let C := 2 ^ H
  let A := 3 ^ q
  let B := affineConst w
  let x := O.value (R.postCaptureStart j k)
  let D := R.postCaptureDefect j k
  have hvalid : Valid w := by
    simpa [w, postCaptureWord] using
      (O.runs_segment (R.postCaptureStart j k) q).valid
  have hqH : q ≤ H := by
    have h := oddSteps_le_twoSteps hvalid
    simpa [q, H, w, oddSteps, postCaptureWord] using h
  have hCpos : 0 < C := Nat.pow_pos (by omega)
  have hCge : 2 ^ q ≤ C :=
    Nat.pow_le_pow_right (by omega) hqH
  have hCone : 1 ≤ C := hCpos
  have hCsq : C ≤ C ^ 2 := by
    rw [pow_two]
    simpa using Nat.mul_le_mul_left C hCone
  have hbudget0 :=
    OddOrbit.WindowDifferenceData.twoPow_length_mul_segmentAffineConst_le
      (O := O)
      (i := R.postCaptureStart j k)
      (q := q)
  have hB : B ≤ A * C := by
    have hone : 1 ≤ 2 ^ q := by
      have hpos : 0 < 2 ^ q :=
        Nat.pow_pos (by omega)
      omega
    calc
      B = 1 * B := by simp
      _ ≤ 2 ^ q * B :=
        Nat.mul_le_mul_right B hone
      _ ≤ A * C := by
        simpa [A, C, H, B, w, postCaptureWord,
          OddOrbit.windowTwoSteps] using hbudget0
  have hodd : oddSteps w = q := by
    simp [w, q, postCaptureWord, oddSteps]
  have hDform : D = (A - C) * x + B := by
    dsimp [D]
    simp only [postCaptureDefect, expandingDefect]
    change
      (3 ^ oddSteps w - 2 ^ twoSteps w) * x + B =
        (A - C) * x + B
    rw [hodd]
  have hDupper : D ≤ A * (x + C) := by
    calc
      D = (A - C) * x + B := hDform
      _ ≤ A * x + A * C :=
        Nat.add_le_add
          (Nat.mul_le_mul_right x (Nat.sub_le A C))
          hB
      _ = A * (x + C) := by
        ring
  have hscale :=
    three_mul_threePow_lt_basePow_sub_two hq hqH
  by_contra hnot
  have hx : x < 2 * C ^ 2 := Nat.lt_of_not_ge hnot
  have hsum : x + C < 3 * C ^ 2 := by omega
  have hDlt : D < 3 * A * C ^ 2 := by
    calc
      D ≤ A * (x + C) := hDupper
      _ < A * (3 * C ^ 2) :=
        (Nat.mul_lt_mul_left (Nat.pow_pos (by omega))).2 hsum
      _ = 3 * A * C ^ 2 := by ring
  have hscale2 : 3 * A * C ^ 2 < C ^ q := by
    calc
      3 * A * C ^ 2 < C ^ (q - 2) * C ^ 2 :=
        (Nat.mul_lt_mul_right (Nat.pow_pos (by omega))).2
          (by simpa [A, C] using hscale)
      _ = C ^ q := by
        rw [← pow_add]
        congr 1
        omega
  have hlarge0 : C ^ q ≤ D := by
    simpa [LargePostCaptureDefectAt, D, C, H, q, w] using hLarge
  omega

/-- large post-capture defectならterminal replay quotientは正。 -/
theorem largeDefectTerminalBridge_quotient_pos
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hq : 5 ≤ R.windowLength j)
    (hanchor : k + 1 ≤ R.terminalTime j)
    (hexpanding :
      ∀ u : ℕ,
        k + 1 + u ≤ R.terminalTime j →
        Expanding
          (O.segmentWord
            (R.postCaptureStart j k + u)
            (R.windowLength j)))
    (hLarge : R.LargePostCaptureDefectAt j k) :
    0 < R.terminalReplayQuotient j := by
  let q := R.windowLength j
  let w := R.postCaptureWord j k
  let H := twoSteps w
  let C := 2 ^ H
  have hCpos : 0 < C := Nat.pow_pos (by omega)
  let t := R.terminalTime j - (k + 1)
  have ht : k + 1 + t = R.terminalTime j := by
    dsimp [t]
    omega
  have hstartLarge := R.postCaptureStart_large_of_largeDefect j k hq hLarge
  have htransport :=
    R.postCaptureStart_le_base_mul_value
      j k
      (by omega)
      t
      (by rw [ht])
  have hterminalIndex :
      R.postCaptureStart j k + t = R.terminalStart j := by
    dsimp [postCaptureStart, terminalStart]
    omega
  have hterminalLarge :
      2 * C ≤ O.value (R.terminalStart j) := by
    have hmul :
        C * (2 * C) ≤ C * O.value (R.terminalStart j) := by
      calc
        C * (2 * C) = 2 * C ^ 2 := by ring
        _ ≤ O.value (R.postCaptureStart j k) := by
          simpa [C, H, w] using hstartLarge
        _ ≤ C * O.value (R.postCaptureStart j k + t) := by
          simpa [C, H, w] using htransport
        _ = C * O.value (R.terminalStart j) := by rw [hterminalIndex]
    exact Nat.le_of_mul_le_mul_left hmul hCpos
  have hHterminal :
      twoSteps (R.terminalWord j) ≤ H := by
    have hmono :=
      R.windowTwoSteps_antitone_before_terminal
        j
        (a := k + 1)
        (b := R.terminalTime j)
        hanchor
        le_rfl
    simpa [terminalWord, terminalStart, postCaptureWord,
      postCaptureStart, H, w, OddOrbit.windowTwoSteps,
      Nat.add_assoc] using hmono
  have hmodulus :
      residueModulus (R.terminalWord j) ≤ 2 * C := by
    unfold residueModulus
    rw [pow_succ]
    simpa [C, H, Nat.mul_comm] using
      (Nat.mul_le_mul_left 2
        (Nat.pow_le_pow_right (by omega) hHterminal))
  by_contra hnot
  have hzero : R.terminalReplayQuotient j = 0 := Nat.eq_zero_of_not_pos hnot
  have hcanonical0 :=
    (R.terminalPacket j).replayCoordinate.start_eq_canonical_of_quotient_eq_zero
      (by simpa [terminalReplayQuotient] using hzero)
  have hcanonical :
      O.value (R.terminalStart j) = canonicalStart (R.terminalWord j) := by
    simpa [terminalWord] using hcanonical0
  have hlt :
      O.value (R.terminalStart j) <
        residueModulus (R.terminalWord j) := by
    rw [hcanonical]
    exact canonicalStart_lt_modulus _
  omega

/-- large post-capture defectからdeep lower-replay terminalを構成する。 -/
noncomputable def deepLowerReplayTerminalOfLargeDefect
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hq : 5 ≤ R.windowLength j)
    (hanchor : k + 1 ≤ R.terminalTime j)
    (hexpanding :
      ∀ u : ℕ,
        k + 1 + u ≤ R.terminalTime j →
        Expanding
          (O.segmentWord
            (R.postCaptureStart j k + u)
            (R.windowLength j)))
    (hLarge : R.LargePostCaptureDefectAt j k) :
    DeepLowerReplayTerminalAt R j := by
  classical
  let P := R.terminalPacket j
  let C := P.replayCoordinate
  have hqpos : 0 < C.quotient := by
    simpa [C, P, terminalReplayQuotient] using
      R.largeDefectTerminalBridge_quotient_pos
        j k hq hanchor hexpanding hLarge
  let L := C.lowerNaturalRunReplay P.run hqpos
  let CLower := CanonicalReplayCoordinate.lowerRunReplayCoordinate C L hqpos
  refine
    { lowerReplay := L
      lowerCoordinate := CLower
      quotient_pos := ?_
      quotient_decrement := ?_
      modulus_deep := R.terminalReplayModulus_deep j }
  · simpa [C, P, terminalReplayQuotient] using hqpos
  · have hqone : 1 ≤ C.quotient := by
      omega
    calc
      CLower.quotient + 1
          = (C.quotient - 1) + 1 := by
              simp only [
                CLower,
                CanonicalReplayCoordinate.lowerRunReplayCoordinate_quotient
              ]
      _ = C.quotient := Nat.sub_add_cancel hqone
      _ = R.terminalReplayQuotient j := by
              rfl

/--
既存の`LargeExpandingDefectAt`枝をdeep lower-replay terminalへ直接送るbridge。
-/
noncomputable def largeDefectTerminalBridge
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ)
    (hq : 5 ≤ R.windowLength j)
    (hLarge : R.LargeExpandingDefectAt j) :
    DeepLowerReplayTerminalAt R j := by
  let k := R.firstCriticalTime j
  have hterminal :
      R.terminalTime j =
        (R.firstDeferred.data (R.select j)).terminalTime := by
    rfl
  have hkterminal : k < R.terminalTime j := by
    dsimp [k]
    rw [hterminal]
    rw [← R.firstCritical_time_eq j]
    exact (R.firstCritical j).time_lt_terminal
  have hLargePost : R.LargePostCaptureDefectAt j k := by
    simpa [
      k,
      LargePostCaptureDefectAt,
      LargeExpandingDefectAt,
      postCaptureDefect,
      postCaptureWord,
      postCaptureStart,
      postCriticalDefect,
      postCriticalWord,
      postCriticalStart
    ] using hLarge
  exact R.deepLowerReplayTerminalOfLargeDefect
    j k hq (by omega)
    (by
      intro u hu
      simpa [k, postCaptureStart, postCriticalStart] using
        R.expanding_after_firstCritical j u hu)
    hLargePost

/-- terminalより前に存在する最後のcapture。 -/
private theorem exists_lastCapture
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) :
    ∃ k : ℕ,
      R.firstCriticalTime j ≤ k ∧
      k < R.terminalTime j ∧
      Nonempty
        (O.CapturedWindowAt (R.start j + k) (R.windowLength j)) ∧
      ∀ t : ℕ,
        k < t → t < R.terminalTime j →
        ¬ Nonempty
          (O.CapturedWindowAt (R.start j + t) (R.windowLength j)) := by
  classical
  let S :=
    O.windowCaptureTimesBefore
      (R.start j) (R.windowLength j) (R.terminalTime j)
  have hcritical :
      R.firstCriticalTime j = (R.firstCritical j).time :=
    (R.firstCritical_time_eq j).symm
  have hterminal :
      R.terminalTime j =
        (R.firstDeferred.data (R.select j)).terminalTime := by
    rfl
  have hfirstTime : R.firstCriticalTime j < R.terminalTime j := by
    rw [hcritical, hterminal]
    exact (R.firstCritical j).time_lt_terminal
  have hfirstCaptured :
      Nonempty
        (O.CapturedWindowAt
          (R.start j + R.firstCriticalTime j)
          (R.windowLength j)) := by
    rw [← R.firstCritical_time_eq j]
    exact ⟨(R.firstCritical j).captured⟩
  have hfirstMem : R.firstCriticalTime j ∈ S := by
    simp [S, OddOrbit.windowCaptureTimesBefore,
      hfirstTime, hfirstCaptured]
  have hne : S.Nonempty := ⟨R.firstCriticalTime j, hfirstMem⟩
  let k := S.max' hne
  have hkmem : k ∈ S := by
    dsimp [k]
    exact Finset.max'_mem S hne
  have hkSpec :
      k < R.terminalTime j ∧
      Nonempty
        (O.CapturedWindowAt (R.start j + k) (R.windowLength j)) := by
    simpa [S, OddOrbit.windowCaptureTimesBefore] using hkmem
  have hkFirst : R.firstCriticalTime j ≤ k := by
    dsimp [k]
    exact Finset.le_max' S _ hfirstMem
  refine ⟨k, hkFirst, hkSpec.1, hkSpec.2, ?_⟩
  intro t hkt ht hcap
  have htmem : t ∈ S := by
    simp [S, OddOrbit.windowCaptureTimesBefore, ht, hcap]
  have hle : t ≤ k := by
    dsimp [k]
    exact Finset.le_max' S _ htmem
  omega

/-- 最後のcapture直後からterminalまで全q-windowはexpanding。 -/
theorem expanding_after_time_ge_firstCritical
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j k : ℕ)
    (hfirst : R.firstCriticalTime j ≤ k) :
    ∀ u : ℕ,
      k + 1 + u ≤ R.terminalTime j →
      Expanding
        (O.segmentWord
          (R.postCaptureStart j k + u)
          (R.windowLength j)) := by
  intro u hu
  let v := k - R.firstCriticalTime j + u
  have hindex :
      R.postCriticalStart j + v = R.postCaptureStart j k + u := by
    dsimp [v, postCriticalStart, postCaptureStart]
    omega
  have hv :
      R.firstCriticalTime j + 1 + v ≤ R.terminalTime j := by
    dsimp [v]
    omega
  simpa [hindex] using R.expanding_after_firstCritical j v hv

/--
有限capture descentの終点：最後のcaptureからterminalがshortか、
そのpost-capture wordがlarge defectを持つ。
-/
theorem postCriticalFiniteDescent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ) :
    ∃ k : ℕ,
      R.firstCriticalTime j ≤ k ∧
      k < R.terminalTime j ∧
      Nonempty
        (O.CapturedWindowAt (R.start j + k) (R.windowLength j)) ∧
      (R.terminalTime j < k + 1 + R.windowLength j * R.windowLength j ∨
        R.LargePostCaptureDefectAt j k) := by
  classical
  obtain ⟨k, hfirst, hkterminal, hkcap, hlast⟩ :=
    exists_lastCapture R j
  refine ⟨k, hfirst, hkterminal, hkcap, ?_⟩
  by_cases hshort :
      R.terminalTime j < k + 1 + R.windowLength j * R.windowLength j
  · exact Or.inl hshort
  · right
    have hinside :
        k + 1 + R.windowLength j * R.windowLength j ≤ R.terminalTime j :=
      Nat.le_of_not_gt hshort
    have hNoCapture :
        ∀ t : ℕ,
          k + 1 ≤ t →
          t < k + 1 + R.windowLength j * R.windowLength j →
          ¬ Nonempty
            (O.CapturedWindowAt (R.start j + t) (R.windowLength j)) := by
      intro t htleft htright
      apply hlast t
      · omega
      · exact lt_of_lt_of_le htright hinside
    exact
      R.largePostCaptureDefectAt_of_noCaptureBeforeSquare
        j k
        (R.expanding_after_time_ge_firstCritical j k hfirst 0 (by omega))
        hinside
        hNoCapture

end FirstCriticalTransitionTowerData

namespace FirstCriticalTransitionTowerData

/-- lower terminal outcomeからdeep lower-replay枝を構成。 -/
noncomputable def deepLowerReplayTerminalOfOutcome
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ)
    (L : LowerNaturalRunReplayData
      (R.terminalWord j)
      (O.value (R.terminalStart j))
      (O.value (R.terminalStart j + R.windowLength j))) :
    DeepLowerReplayTerminalAt R j := by
  classical
  let P := R.terminalPacket j
  let C := P.replayCoordinate
  have hqpos : 0 < C.quotient := by
    by_contra hnot
    have hzero : C.quotient = 0 := Nat.eq_zero_of_not_pos hnot
    have hcanonical0 := C.start_eq_canonical_of_quotient_eq_zero hzero
    have hcanonical :
        O.value (R.terminalStart j) = canonicalStart (R.terminalWord j) := by
      simpa [terminalWord] using hcanonical0
    have hmodle : residueModulus (R.terminalWord j) ≤
        O.value (R.terminalStart j) := by
      rw [L.start_step]
      omega
    have hlt : O.value (R.terminalStart j) <
        residueModulus (R.terminalWord j) := by
      rw [hcanonical]
      exact canonicalStart_lt_modulus _
    omega
  let CLower := CanonicalReplayCoordinate.lowerRunReplayCoordinate C L hqpos
  refine
    { lowerReplay := L
      lowerCoordinate := CLower
      quotient_pos := ?_
      quotient_decrement := ?_
      modulus_deep := R.terminalReplayModulus_deep j }
  · simpa [C, P, terminalReplayQuotient] using hqpos
  · have hqone : 1 ≤ C.quotient := by
      exact hqpos
    calc
      CLower.quotient + 1
          = (C.quotient - 1) + 1 := by
              rw [
                CanonicalReplayCoordinate.lowerRunReplayCoordinate_quotient
              ]
      _ = C.quotient := Nat.sub_add_cancel hqone
      _ = R.terminalReplayQuotient j := by
              simp [C, P, terminalReplayQuotient]

/-- positive terminal outcomeは最後のcaptureからshort。 -/
noncomputable def shortPositiveShadowTerminalOfOutcome
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ)
    (hq : 5 ≤ R.windowLength j)
    (hzero : R.terminalReplayQuotient j = 0)
    (hshadow : 0 < R.terminalPredecessorShadow j) :
    ShortPositiveShadowTerminalAt R j := by
  classical
  exact Classical.choice (by
    obtain ⟨k, hfirst, hkterminal, hkcap, hshort | hlarge⟩ :=
      R.postCriticalFiniteDescent j
    · exact
        ⟨{
          anchorTime := k
          firstCritical_le := hfirst
          anchor_lt_terminal := hkterminal
          anchorCaptured := Classical.choice hkcap
          short := hshort
          canonicalBoundary := hzero
          positiveShadow := hshadow
        }⟩
    · have hanchor : k + 1 ≤ R.terminalTime j := by
        omega
      have hqpos :
          0 < R.terminalReplayQuotient j :=
        R.largeDefectTerminalBridge_quotient_pos
          j
          k
          hq
          hanchor
          (R.expanding_after_time_ge_firstCritical
            j k hfirst)
          hlarge
      exfalso
      omega)

/-- q>=5の各first-critical項は目的の三局所枝のどれか。 -/
theorem terminal_trichotomy_at
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (j : ℕ)
    (hq : 5 ≤ R.windowLength j) :
    Nonempty (DeepLowerReplayTerminalAt R j) ∨
      Nonempty (ShortPositiveShadowTerminalAt R j) ∨
      R.TerminalSpecialC3At j := by
  classical
  cases R.terminalOutcome j with
  | lowerNaturalReplay L =>
      exact Or.inl ⟨R.deepLowerReplayTerminalOfOutcome j L⟩
  | positivePredecessorShadow hboundary hpositive =>
      have hzero : R.terminalReplayQuotient j = 0 := by
        simpa [terminalReplayQuotient] using hboundary
      have hshadow : 0 < R.terminalPredecessorShadow j := by
        simpa [terminalPredecessorShadow, terminalWord] using hpositive
      exact Or.inr (Or.inl
        ⟨R.shortPositiveShadowTerminalOfOutcome j hq hzero hshadow⟩)
  | special S =>
      exact Or.inr (Or.inr ⟨by
        simpa [TerminalSpecialC3At, terminalStart, terminalTime,
          FirstCriticalTransitionTowerData.start,
          FirstCriticalTransitionTowerData.windowLength,
          FirstDeferredNormalizationTowerData.start,
          FirstDeferredNormalizationTowerData.windowLength,
          FirstDeferredNormalizationTowerData.terminalTime,
          Nat.add_assoc] using S⟩)

end FirstCriticalTransitionTowerData

/-- deep lower-replay terminalの部分tower。 -/
structure DeepLowerReplayTerminalTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) where
  source : FirstCriticalTransitionTowerData hGap O
  select : ℕ → ℕ
  select_strict : StrictMono select
  deep : ∀ j : ℕ, DeepLowerReplayTerminalAt source (select j)

/-- short positive-shadow terminalの部分tower。 -/
structure ShortPositiveShadowTerminalTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) where
  source : FirstCriticalTransitionTowerData hGap O
  select : ℕ → ℕ
  select_strict : StrictMono select
  shortPositive : ∀ j : ℕ,
    ShortPositiveShadowTerminalAt source (select j)

/-- first-critical枝をterminal三枝へまとめるoutcome。 -/
inductive FirstCriticalTerminalOutcomeTowerData
    (hGap : TwoThreeGapPolynomialBound) (O : OddOrbit) : Type
  | deepLowerReplay
      (data : DeepLowerReplayTerminalTowerData hGap O)
  | shortPositiveShadow
      (data : ShortPositiveShadowTerminalTowerData hGap O)
  | terminalSpecialC3
      (data : TerminalSpecialC3TransitionTowerData hGap O)

/-- persistent deep枝から部分towerを構成。 -/
noncomputable def deepLowerReplayTowerOfPersistent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (h : Persistently (fun j => Nonempty (DeepLowerReplayTerminalAt R j))) :
    DeepLowerReplayTerminalTowerData hGap O where
  source := R
  select := Persistently.select
    (fun j => Nonempty (DeepLowerReplayTerminalAt R j)) h
  select_strict := Persistently.select_strict
    (fun j => Nonempty (DeepLowerReplayTerminalAt R j)) h
  deep := fun j => Classical.choice
    (Persistently.select_spec
      (fun n => Nonempty (DeepLowerReplayTerminalAt R n)) h j)

/-- persistent short-positive枝から部分towerを構成。 -/
noncomputable def shortPositiveShadowTowerOfPersistent
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O)
    (h : Persistently (fun j =>
      Nonempty (ShortPositiveShadowTerminalAt R j))) :
    ShortPositiveShadowTerminalTowerData hGap O where
  source := R
  select := Persistently.select
    (fun j => Nonempty (ShortPositiveShadowTerminalAt R j)) h
  select_strict := Persistently.select_strict
    (fun j => Nonempty (ShortPositiveShadowTerminalAt R j)) h
  shortPositive := fun j => Classical.choice
    (Persistently.select_spec
      (fun n => Nonempty (ShortPositiveShadowTerminalAt R n)) h j)

/-- first-critical towerの目的のterminal三分岐。 -/
theorem firstCriticalTerminal_classification
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) :
    Nonempty (DeepLowerReplayTerminalTowerData hGap O) ∨
      Nonempty (ShortPositiveShadowTerminalTowerData hGap O) ∨
      Nonempty (TerminalSpecialC3TransitionTowerData hGap O) := by
  classical
  let Pdeep : ℕ → Prop := fun j =>
    Nonempty (DeepLowerReplayTerminalAt R j)
  let Pshort : ℕ → Prop := fun j =>
    Nonempty (ShortPositiveShadowTerminalAt R j)
  by_cases hDeep : Persistently Pdeep
  · exact Or.inl ⟨deepLowerReplayTowerOfPersistent R hDeep⟩
  · by_cases hShort : Persistently Pshort
    · exact Or.inr (Or.inl
        ⟨shortPositiveShadowTowerOfPersistent R hShort⟩)
    · obtain ⟨Nd, hNd⟩ := Persistently.eventually_not_of_not Pdeep hDeep
      obtain ⟨Ns, hNs⟩ := Persistently.eventually_not_of_not Pshort hShort
      obtain ⟨Nq, hNq⟩ := R.firstDeferred.lengths_tend_to_infinity 4
      let N := max (max Nd Ns) Nq
      let select : ℕ → ℕ := fun j => N + j
      refine Or.inr (Or.inr ⟨{
        source := R
        select := select
        select_strict := by
          intro a b hab
          exact Nat.add_lt_add_left hab N
        special := ?_
      }⟩)
      intro j
      let n := select j
      have hnD : Nd ≤ n := by
        dsimp [n, select, N]
        omega
      have hnS : Ns ≤ n := by
        dsimp [n, select, N]
        omega
      have hNqn : Nq ≤ n := by
        dsimp [n, select, N]
        omega
      have hindex : n ≤ R.select n :=
        nat_le_strictMono_apply R.select R.select_strict n
      have hnQ : Nq ≤ R.select n :=
        hNqn.trans hindex
      have hq : 5 ≤ R.windowLength n := by
        have h :=
          hNq (R.select n) hnQ
        change
          5 ≤
            R.source.windowLength
              (R.firstDeferred.select (R.select n))
        omega
      rcases R.terminal_trichotomy_at n hq with hD | hS | hT
      · exact False.elim (hNd n hnD hD)
      · exact False.elim (hNs n hnS hS)
      · exact hT

/-- first-critical terminal三分岐をconstructor outcomeへまとめる。 -/
theorem firstCriticalTerminal_outcome
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (R : FirstCriticalTransitionTowerData hGap O) :
    Nonempty (FirstCriticalTerminalOutcomeTowerData hGap O) := by
  rcases firstCriticalTerminal_classification R with hD | hP | hS
  · exact ⟨.deepLowerReplay (Classical.choice hD)⟩
  · exact ⟨.shortPositiveShadow (Classical.choice hP)⟩
  · exact ⟨.terminalSpecialC3 (Classical.choice hS)⟩

end CollatzSecondLayer2
