import CollatzLean.CollatzSecondLayer3.NormalizationRefinementObjects

/-!
# polynomial terminalからPolynomial Special C3 towerへ

first-deferred towerのterminal endpointが一様多項式以下となる無限部分列を、
terminal deferred三分岐と指数優越によってPolynomial Special C3 towerへ送る。
指数優越はLean内定理`polynomialBelowTwoPower`から自動的に使用する。
-/

namespace CollatzSecondLayer3

open CollatzSupport
open CollatzExternal
open CollatzCore

open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 狭義単調な自然数列は各添字以上に進む。 -/
theorem nat_le_strictMono_apply
    (f : ℕ → ℕ)
    (hf : StrictMono f) :
    ∀ n : ℕ, n ≤ f n := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
      have hstep : f n < f (n + 1) :=
        hf (Nat.lt_succ_self n)
      omega

namespace FirstDeferredNormalizationTowerData

/-- first-deferred towerの第`j`項が由来するcrossing添字。 -/
def crossingIndex
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ) : ℕ :=
  D.source.select (T.select j)

/-- first-deferred towerの第`j`項のnormalization開始位置。 -/
noncomputable def start
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ) : ℕ :=
  D.start (T.select j)

/-- first-deferred towerの第`j`項のwindow長。 -/
def windowLength
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ) : ℕ :=
  D.windowLength (T.select j)

/-- first-deferred towerの第`j`項のterminal時刻。 -/
noncomputable def terminalTime
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ) : ℕ :=
  (T.data j).terminalTime

/-- first-deferred towerの第`j`項のterminal上側endpoint。 -/
noncomputable def terminalEndpoint
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ) : ℕ :=
  O.value (T.start j + T.terminalTime j + T.windowLength j)

/-- 各window長は正。 -/
theorem windowLength_pos
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ) :
    0 < T.windowLength j := by
  simpa [
    windowLength,
    crossingIndex,
    StandardNormalizationGeneratedObstructionTowerData.windowLength
  ] using
    (D.crossing.crossing (T.crossingIndex j)).length_pos

/-- terminal deferred windowの三分岐を一つ選ぶ。 -/
noncomputable def terminalOutcome
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ) :
    DeferredPreparedWindowOutcome
      (OddOrbit.FiniteCaptureNormalizationData.terminalPacket
        (T.windowLength_pos j)
        (T.data j)) := by
  classical
  exact Classical.choice
    (firstDeferredTerminalOutcome_nonempty
      (T.windowLength_pos j)
      (T.data j))

/-- polynomial準備familyの開始位置はcrossing開始位置とoffsetの和。 -/
theorem polynomialPreparedFullWindowFamily_start
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    (F : MovingFirstCrossingData O)
    (j : ℕ) :
    (polynomialPreparedFullWindowFamily hGap F).start j =
      F.minima.index j +
        (polynomialPreparedFullWindowFamily hGap F).offset j := by
  rfl

/-- terminal outcomeはlarge endpointまたはSpecial C3。 -/
theorem terminalEndpoint_large_or_special
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (j : ℕ) :
    2 * 3 ^ T.windowLength j < T.terminalEndpoint j ∨
      Nonempty
        (SpecialC3At O
          (T.start j + T.terminalTime j)
          (T.windowLength j)) := by
  have h :=
    DeferredPreparedWindowOutcome.endpoint_large_or_special
      (OddOrbit.FiniteCaptureNormalizationData.terminalPacket
        (T.windowLength_pos j)
        (T.data j))
      (T.terminalOutcome j)
  simpa [
    terminalEndpoint,
    start,
    terminalTime,
    windowLength,
    StandardNormalizationGeneratedObstructionTowerData.start,
    StandardNormalizationGeneratedObstructionTowerData.windowLength,
    polynomialPreparedFullWindowFamily_start,
    Nat.add_assoc
  ] using h

/-- 選択後もwindow長は無限大へ進む。 -/
theorem selected_lengths_tend_to_infinity
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D)
    (select : ℕ → ℕ)
    (hselect : StrictMono select) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M < T.windowLength (select j) := by
  intro M
  obtain ⟨J, hJ⟩ := T.lengths_tend_to_infinity M
  refine ⟨J, ?_⟩
  intro j hj
  apply hJ (select j)
  exact le_trans hj
    (nat_le_strictMono_apply select hselect j)

end FirstDeferredNormalizationTowerData

/-- terminal endpointが固定多項式以下となるfirst-deferred部分tower。 -/
structure PolynomialTerminalFirstDeferredTowerData
    {hGap : TwoThreeGapPolynomialBound} {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    (T : FirstDeferredNormalizationTowerData D) where
  select : ℕ → ℕ
  select_strict : StrictMono select
  K : ℕ
  A : ℕ
  endpointBound : ∀ j : ℕ,
    T.terminalEndpoint (select j) ≤
      K * (T.windowLength (select j) + 1) ^ A

namespace PolynomialTerminalFirstDeferredTowerData

/--
terminal endpointの固定多項式が`2 * 3^q`より小さくなる長さ閾値。
`Exists`をType値へ直接casesせず、古典選択で固定する。
-/
noncomputable def polynomialCutoff
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T) : ℕ :=
  Classical.choose
    (polynomialBelowTwoMulThreePower R.K R.A)

/-- `polynomialCutoff`以後では固定多項式が指数項より小さい。 -/
theorem polynomialCutoff_spec
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T) :
    ∀ q : ℕ,
      R.polynomialCutoff ≤ q →
        R.K * (q + 1) ^ R.A < 2 * 3 ^ q :=
  Classical.choose_spec
    (polynomialBelowTwoMulThreePower R.K R.A)

/--
選択towerのwindow長が`polynomialCutoff`を超えるtail開始位置。
-/
noncomputable def tailCutoff
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T) : ℕ :=
  Classical.choose
    (T.selected_lengths_tend_to_infinity
      R.select R.select_strict
      R.polynomialCutoff)

/-- `tailCutoff`以後の選択項は必要なwindow長を持つ。 -/
theorem tailCutoff_spec
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T) :
    ∀ j : ℕ,
      R.tailCutoff ≤ j →
        R.polynomialCutoff <
          T.windowLength (R.select j) :=
  Classical.choose_spec
    (T.selected_lengths_tend_to_infinity
      R.select R.select_strict
      R.polynomialCutoff)

/-- 必要な長さ閾値を超えたtail部分列。 -/
noncomputable def tailSelect
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T)
    (j : ℕ) : ℕ :=
  R.select (R.tailCutoff + j)

/-- tail部分列に対応する元first-crossing添字。 -/
noncomputable def tailCrossingSelect
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T)
    (j : ℕ) : ℕ :=
  T.crossingIndex (R.tailSelect j)

/-- terminal Special C3の元first-crossing内offset。 -/
noncomputable def tailOffset
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T)
    (j : ℕ) : ℕ :=
  (polynomialPreparedFullWindowFamily hGap D.crossing).offset
      (R.tailCrossingSelect j) +
    T.terminalTime (R.tailSelect j)

/-- tail選択列は狭義単調。 -/
theorem tailSelect_strict
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T) :
    StrictMono R.tailSelect := by
  intro a b hab
  simpa [tailSelect] using
    R.select_strict
      (Nat.add_lt_add_left hab R.tailCutoff)

/-- 元first-crossing添字列も狭義単調。 -/
theorem tailCrossingSelect_strict
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T) :
    StrictMono R.tailCrossingSelect := by
  intro i j hij
  change
    D.source.select
        (T.select (R.tailSelect i)) <
      D.source.select
        (T.select (R.tailSelect j))
  exact
    D.source.select_strict
      (T.select_strict
        (R.tailSelect_strict hij))

/-- tail上の各window長は指数優越閾値以上。 -/
theorem polynomialCutoff_le_tailWindowLength
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T)
    (j : ℕ) :
    R.polynomialCutoff ≤
      T.windowLength (R.tailSelect j) := by
  have h :=
    R.tailCutoff_spec
      (R.tailCutoff + j)
      (by omega)
  simpa [tailSelect] using h.le

/-- tail上でも元のterminal endpoint多項式上界を保持する。 -/
theorem tailTerminalEndpoint_bound
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T)
    (j : ℕ) :
    T.terminalEndpoint (R.tailSelect j) ≤
      R.K *
        (T.windowLength (R.tailSelect j) + 1) ^ R.A := by
  simpa [tailSelect] using
    R.endpointBound (R.tailCutoff + j)

/--
tail上ではlarge terminal枝が多項式上界と矛盾するため、
terminal deferred windowは必ずSpecial C3。
-/
noncomputable def tailSpecial
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T)
    (j : ℕ) :
    SpecialC3At O
      (D.crossing.minima.index (R.tailCrossingSelect j) +
        R.tailOffset j)
      (D.crossing.crossingLength
        (R.tailCrossingSelect j)) := by
  classical
  have hNonempty :
      Nonempty
        (SpecialC3At O
          (D.crossing.minima.index (R.tailCrossingSelect j) +
            R.tailOffset j)
          (D.crossing.crossingLength
            (R.tailCrossingSelect j))) := by
    rcases
        T.terminalEndpoint_large_or_special
          (R.tailSelect j) with
      hlarge | hSpecial
    · have hsmall :
          T.terminalEndpoint (R.tailSelect j) <
            2 * 3 ^ T.windowLength (R.tailSelect j) := by
        exact lt_of_le_of_lt
          (R.tailTerminalEndpoint_bound j)
          (R.polynomialCutoff_spec
            (T.windowLength (R.tailSelect j))
            (R.polynomialCutoff_le_tailWindowLength j))
      exfalso
      omega
    · simpa [
        tailSelect,
        tailCrossingSelect,
        tailOffset,
        FirstDeferredNormalizationTowerData.start,
        FirstDeferredNormalizationTowerData.windowLength,
        FirstDeferredNormalizationTowerData.crossingIndex,
        StandardNormalizationGeneratedObstructionTowerData.start,
        StandardNormalizationGeneratedObstructionTowerData.windowLength,
        PolynomialPreparedFullWindowFamily.start,
        Nat.add_assoc
      ] using hSpecial
  exact Classical.choice hNonempty

/--
tail上のterminal endpoint多項式上界を、
Polynomial Special C3 towerの出力位置表示へ移す。
-/
theorem tailOutput_endpointBound
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T) :
    ∀ j : ℕ,
      O.value
          (D.crossing.minima.index
                (R.tailCrossingSelect j) +
            R.tailOffset j +
            D.crossing.crossingLength
              (R.tailCrossingSelect j)) ≤
        R.K *
          (D.crossing.crossingLength
                (R.tailCrossingSelect j) + 1) ^ R.A := by
  intro j
  simpa [
    tailCrossingSelect,
    tailOffset,
    FirstDeferredNormalizationTowerData.crossingIndex,
    FirstDeferredNormalizationTowerData.start,
    FirstDeferredNormalizationTowerData.terminalTime,
    FirstDeferredNormalizationTowerData.terminalEndpoint,
    FirstDeferredNormalizationTowerData.windowLength,
    StandardNormalizationGeneratedObstructionTowerData.start,
    StandardNormalizationGeneratedObstructionTowerData.windowLength,
    PolynomialPreparedFullWindowFamily.start,
    Nat.add_assoc
  ] using
    (R.tailTerminalEndpoint_bound j)

/--
tailで選び直した元first-crossing window長も無限大へ進む。
-/
theorem tailLengths_tend_to_infinity
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T) :
    ∀ M : ℕ, ∃ J : ℕ, ∀ j : ℕ, J ≤ j →
      M <
        D.crossing.crossingLength
          (R.tailCrossingSelect j) := by
  intro M
  obtain ⟨J, hJ⟩ :=
    T.selected_lengths_tend_to_infinity
      R.tailSelect
      R.tailSelect_strict
      M
  refine ⟨J, ?_⟩
  intro j hj
  have hlength :
      M < T.windowLength (R.tailSelect j) :=
    hJ j hj
  simpa [
    tailCrossingSelect,
    FirstDeferredNormalizationTowerData.crossingIndex,
    FirstDeferredNormalizationTowerData.windowLength,
    StandardNormalizationGeneratedObstructionTowerData.windowLength
  ] using hlength

/--
多項式terminal部分towerは、十分後にlarge terminal二枝を排除できるため、
Polynomial Special C3 towerを与える。
-/
noncomputable def toPolynomialSpecialC3Tower
    {hGap : TwoThreeGapPolynomialBound}
    {O : OddOrbit}
    {D : StandardNormalizationGeneratedObstructionTowerData hGap O}
    {T : FirstDeferredNormalizationTowerData D}
    (R : PolynomialTerminalFirstDeferredTowerData T) :
    PolynomialSpecialC3TowerData O where
  crossing := D.crossing
  select := R.tailCrossingSelect
  select_strict := R.tailCrossingSelect_strict
  offset := R.tailOffset
  special := R.tailSpecial
  K := R.K
  A := R.A
  endpointBound := R.tailOutput_endpointBound
  lengths_tend_to_infinity := R.tailLengths_tend_to_infinity

end PolynomialTerminalFirstDeferredTowerData

end CollatzSecondLayer3
