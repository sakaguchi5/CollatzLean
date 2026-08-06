import CollatzLean.CollatzSecondLayer3.NormalizationRefinementSource

/-!
# normalization refinementの局所算術

標準preparationの由来から、prepared q-windowが元first-crossing windowの総2除算数を
保存すること、first-crossing総指数がcritical shellに入ること、captureによる
window総指数の下降量がcapture gapとexactに一致することを証明する。

さらにfinite normalizationのterminal deferred windowを、lower replay・positive shadow・
Special C3の三枝へ直接分類する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

@[simp] theorem polynomialPreparedFullWindowFamily_offset
    (hGap : TwoThreeGapPolynomialBound)
    {O : OddOrbit} (F : MovingFirstCrossingData O) (j : ℕ) :
    (polynomialPreparedFullWindowFamily hGap F).offset j =
      (movingFullWindowPreparation F j).boundaryLength := by
  rfl

@[simp] theorem polynomialPreparedFullWindowFamily_packet
    (hGap : TwoThreeGapPolynomialBound)
    {O : OddOrbit} (F : MovingFirstCrossingData O) (j : ℕ) :
    (polynomialPreparedFullWindowFamily hGap F).packet j =
      (movingFullWindowPreparation F j).packet := by
  rfl

/--
標準同期準備でwindowをboundary長だけ平行移動しても、q-window総指数は保存される。
-/
theorem movingFullWindowPreparation_windowTwoSteps_eq
    {O : OddOrbit} (F : MovingFirstCrossingData O) (j : ℕ) :
    O.windowTwoSteps
        (F.minima.index j +
          (movingFullWindowPreparation F j).boundaryLength)
        (F.crossingLength j) =
      O.windowTwoSteps (F.minima.index j) (F.crossingLength j) := by
  let n := F.minima.index j
  let q := F.crossingLength j
  let S := movingFullWindowPreparation F j
  let k := S.boundaryLength
  have hword :
      O.segmentWord n k = O.segmentWord (n + q) k := by
    exact S.lowerWord_eq.symm.trans S.upperWord_eq
  have hconcat :
      O.segmentWord n k ++ O.segmentWord (n + k) q =
        O.segmentWord n q ++ O.segmentWord (n + q) k := by
    calc
      O.segmentWord n k ++ O.segmentWord (n + k) q
          = O.segmentWord n (k + q) :=
            (O.segmentWord_add n k q).symm
      _ = O.segmentWord n (q + k) := by
            rw [Nat.add_comm]
      _ = O.segmentWord n q ++ O.segmentWord (n + q) k :=
            O.segmentWord_add n q k
  have hsteps := congrArg twoSteps hconcat
  rw [twoSteps_append, twoSteps_append, hword] at hsteps
  change
    (O.segmentWord (n + k) q).twoSteps =
      (O.segmentWord n q).twoSteps
  omega

/-- first-crossing windowは終端で収縮側にある。 -/
theorem firstCrossing_threePow_lt_twoPow
    {O : OddOrbit} {n q : ℕ}
    (hC : FirstCrossingAt O n q) :
    3 ^ q < 2 ^ O.windowTwoSteps n q := by
  simpa [FirstCrossingAt, Contracting, OddOrbit.windowTwoSteps, oddSteps]
    using hC.terminalContracting

/--
future-minimumから始まるfirst-crossing windowの総指数はcritical shell
`3^q < 2^H ≤ (q+1)3^q`の上端以下にある。
-/
theorem firstCrossing_twoPow_le_succ_mul_threePow
    {O : OddOrbit} {n q : ℕ}
    (hmin : O.FutureMinimumAt n)
    (hC : FirstCrossingAt O n q) :
    2 ^ O.windowTwoSteps n q ≤ (q + 1) * 3 ^ q := by
  let w := O.segmentWord n q
  have hrun : Realizes w (O.value n) (O.value (n + q)) :=
    O.realizes_segment n q
  have hend : O.value n ≤ O.value (n + q) :=
    O.futureMinimum_le_segment_end hmin q
  have hscaled :
      2 ^ twoSteps w * O.value n ≤
        3 ^ oddSteps w * O.value n + affineConst w := by
    calc
      2 ^ twoSteps w * O.value n
          ≤ 2 ^ twoSteps w * O.value (n + q) :=
            Nat.mul_le_mul_left _ hend
      _ = 3 ^ oddSteps w * O.value n + affineConst w := hrun
  have hcontract : 3 ^ oddSteps w < 2 ^ twoSteps w := by
    change w.Contracting
    exact hC.terminalContracting
  have hgapPos :
      0 < 2 ^ twoSteps w - 3 ^ oddSteps w :=
    Nat.sub_pos_of_lt hcontract
  have hgap :
      (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n ≤
        affineConst w := by
    have hdecomp :
        2 ^ twoSteps w =
          3 ^ oddSteps w +
            (2 ^ twoSteps w - 3 ^ oddSteps w) :=
      (Nat.add_sub_of_le hcontract.le).symm
    have hcancel :
        3 ^ oddSteps w * O.value n +
            (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n
          ≤
        3 ^ oddSteps w * O.value n + affineConst w := by
      calc
        3 ^ oddSteps w * O.value n +
            (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n
            = 2 ^ twoSteps w * O.value n := by
                calc
                  3 ^ oddSteps w * O.value n +
                      (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n
                      =
                    (3 ^ oddSteps w +
                        (2 ^ twoSteps w - 3 ^ oddSteps w)) *
                      O.value n := by rw [Nat.add_mul]
                  _ = 2 ^ twoSteps w * O.value n := by
                        rw [← hdecomp]
        _ ≤ 3 ^ oddSteps w * O.value n + affineConst w := hscaled
    exact Nat.le_of_add_le_add_left hcancel
  have hvaluePos : 0 < O.value n := by
    rcases O.value_odd n with ⟨a, ha⟩
    omega
  have hgapLe :
      2 ^ twoSteps w - 3 ^ oddSteps w ≤ affineConst w := by
    calc
      2 ^ twoSteps w - 3 ^ oddSteps w
          = (2 ^ twoSteps w - 3 ^ oddSteps w) * 1 := by simp
      _ ≤ (2 ^ twoSteps w - 3 ^ oddSteps w) * O.value n := by
            exact Nat.mul_le_mul_left _ hvaluePos
      _ ≤ affineConst w := hgap
  have haffine : affineConst w ≤ q * 3 ^ q := by
    simpa [w, oddSteps] using affineConst_le_length_mul_threePow hC
  have hdecomp :
      2 ^ twoSteps w =
        3 ^ oddSteps w +
          (2 ^ twoSteps w - 3 ^ oddSteps w) :=
    (Nat.add_sub_of_le hcontract.le).symm
  change 2 ^ twoSteps w ≤ (q + 1) * 3 ^ q
  calc
    2 ^ twoSteps w
        = 3 ^ oddSteps w +
            (2 ^ twoSteps w - 3 ^ oddSteps w) := hdecomp
    _ ≤ 3 ^ oddSteps w + affineConst w :=
      Nat.add_le_add_left hgapLe _
    _ ≤ 3 ^ q + q * 3 ^ q := by
      simpa [w, oddSteps] using Nat.add_le_add_left haffine (3 ^ q)
    _ = (q + 1) * 3 ^ q := by ring

namespace OddOrbit.CapturedWindowAt

/-- captureによるq-window総指数下降量はcapture gapとexactに一致する。 -/
theorem windowTwoSteps_add_captureGap_eq
    {O : OddOrbit} {i q : ℕ}
    (C : O.CapturedWindowAt i q) :
    O.windowTwoSteps (i + 1) q +
        (O.exponent i - C.depth) =
      O.windowTwoSteps i q := by
  have hbalance := O.windowTwoSteps_shift_balance i q
  rw [C.upperExponent_eq_depth] at hbalance
  have hdepth :
      C.depth ≤ O.exponent i :=
    Nat.le_of_lt C.captured
  omega

end OddOrbit.CapturedWindowAt

namespace StandardNormalizationGeneratedObstructionTowerData

/-- 強化版towerの初期prepared windowは収縮側にある。 -/
theorem initial_threePow_lt_twoPow
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ) :
    3 ^ D.windowLength j <
      2 ^ O.windowTwoSteps (D.start j) (D.windowLength j) := by
  let n := D.source.select j
  have hcross :
      3 ^ D.crossing.crossingLength n <
        2 ^ O.windowTwoSteps
          (D.crossing.minima.index n)
          (D.crossing.crossingLength n) :=
    firstCrossing_threePow_lt_twoPow (D.crossing.crossing n)
  have htransport :=
    movingFullWindowPreparation_windowTwoSteps_eq D.crossing n
  simpa [start, windowLength, n,
    PolynomialPreparedFullWindowFamily.start] using
      (show
        3 ^ D.crossing.crossingLength n <
          2 ^ O.windowTwoSteps
            (D.crossing.minima.index n +
              (movingFullWindowPreparation D.crossing n).boundaryLength)
            (D.crossing.crossingLength n) by
        rwa [htransport])

/-- 強化版towerの初期prepared windowはcritical shell上端以下にある。 -/
theorem initial_twoPow_le_succ_mul_threePow
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    (D : StandardNormalizationGeneratedObstructionTowerData hGap O)
    (j : ℕ) :
    2 ^ O.windowTwoSteps (D.start j) (D.windowLength j) ≤
      (D.windowLength j + 1) * 3 ^ D.windowLength j := by
  let n := D.source.select j
  have hshell :
      2 ^ O.windowTwoSteps
          (D.crossing.minima.index n)
          (D.crossing.crossingLength n) ≤
        (D.crossing.crossingLength n + 1) *
          3 ^ D.crossing.crossingLength n :=
    firstCrossing_twoPow_le_succ_mul_threePow
      (D.crossing.minima.futureMinimum n)
      (D.crossing.crossing n)
  have htransport :=
    movingFullWindowPreparation_windowTwoSteps_eq D.crossing n
  simpa [start, windowLength, n,
    PolynomialPreparedFullWindowFamily.start] using
      (show
        2 ^ O.windowTwoSteps
            (D.crossing.minima.index n +
              (movingFullWindowPreparation D.crossing n).boundaryLength)
            (D.crossing.crossingLength n) ≤
          (D.crossing.crossingLength n + 1) *
            3 ^ D.crossing.crossingLength n by
        rwa [htransport])

end StandardNormalizationGeneratedObstructionTowerData

/-- finite normalizationのterminal deferred位置をprepared packetとして取り出す。 -/
def OddOrbit.FiniteCaptureNormalizationData.terminalPacket
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (hq : 0 < q)
    (F : O.FiniteCaptureNormalizationData D₀) :
    O.PreparedWindowPacket (start + F.terminalTime) q where
  toWindowDifferenceData := F.terminal.toWindowDifferenceData
  length_pos := hq
  depth_le_nextExponent := by
    rw [F.terminal.deferred]

/-- deferred prepared windowに残る三種類。 -/
inductive DeferredPreparedWindowOutcome
    {O : OddOrbit} {i q : ℕ}
    (P : O.PreparedWindowPacket i q) : Type
  | lowerNaturalReplay
      (data : LowerNaturalRunReplayData
        (O.segmentWord i q)
        (O.value i)
        (O.value (i + q)))
  | positivePredecessorShadow
      (canonicalBoundary : P.replayCoordinate.quotient = 0)
      (data : 0 < predecessorShadow (O.segmentWord i q))
  | special
      (data : SpecialC3At O i q)

/-- first deferred terminalをlower replay・positive shadow・Special C3へ分類する。 -/
theorem firstDeferredTerminalOutcome_nonempty
    {O : OddOrbit} {start q : ℕ}
    {D₀ : O.WindowDifferenceData start q}
    (hq : 0 < q)
    (F : O.FiniteCaptureNormalizationData D₀) :
    Nonempty
      (DeferredPreparedWindowOutcome
        (OddOrbit.FiniteCaptureNormalizationData.terminalPacket hq F)) := by
  let P := OddOrbit.FiniteCaptureNormalizationData.terminalPacket hq F
  let C := P.replayCoordinate
  by_cases hq0 : C.quotient = 0
  · have hstart :
        O.value (start + F.terminalTime) =
          canonicalStart
            (O.segmentWord (start + F.terminalTime) q) :=
      C.start_eq_canonical_of_quotient_eq_zero hq0
    have hend :
        O.value (start + F.terminalTime + q) =
          canonicalEnd
            (O.segmentWord (start + F.terminalTime) q) := by
      rw [C.finish_eq, hq0]
      simp
    rcases lt_trichotomy
        (predecessorShadow
          (O.segmentWord (start + F.terminalTime) q)) 0 with
      hneg | hzero | hpos
    · exact ⟨DeferredPreparedWindowOutcome.special
        (specialC3At_of_deferred F.terminal hq hstart hend hneg)⟩
    · exact False.elim
        ((predecessorShadow_ne_zero
          (O.segmentWord (start + F.terminalTime) q)) hzero)
    · exact ⟨DeferredPreparedWindowOutcome.positivePredecessorShadow
        hq0 hpos⟩
  · have hqpos : 0 < C.quotient := Nat.pos_of_ne_zero hq0
    exact ⟨DeferredPreparedWindowOutcome.lowerNaturalReplay
      (C.lowerNaturalRunReplay P.run hqpos)⟩

/-- terminalがSpecial C3でなければ、terminal endpointは`2*3^q`を超える。 -/
theorem DeferredPreparedWindowOutcome.endpoint_large_or_special
    {O : OddOrbit} {i q : ℕ}
    (P : O.PreparedWindowPacket i q)
    (R : DeferredPreparedWindowOutcome P) :
    2 * 3 ^ q < O.value (i + q) ∨
      Nonempty (SpecialC3At O i q) := by
  cases R with
  | lowerNaturalReplay L =>
      exact Or.inl
        (OddOrbit.PreparedWindowAlternative.endpoint_gt_two_mul_threePow_of_lowerReplay
          P L)
  | positivePredecessorShadow hq0 hshadow =>
      exact Or.inl
        (OddOrbit.PreparedWindowAlternative.endpoint_gt_two_mul_threePow_of_positiveShadow
          P hq0 hshadow)
  | special S =>
      exact Or.inr ⟨S⟩

end CollatzSecondLayer3
