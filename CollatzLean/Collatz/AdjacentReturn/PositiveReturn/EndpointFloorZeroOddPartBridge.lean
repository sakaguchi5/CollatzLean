import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroPacket
import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.Valuation

/-!
# bounded-gap odd part から endpoint-floor coordinate への bridge

weighted packing / anchored cancellation が作る巨大 local `gapOddPart` を、
source-preserving endpoint-floor extraction 後の arithmetic coordinate `q=n+d` へ
直接送る。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn

namespace FirstCrossingData.NaturalZeroReplaySignChangeData

/-- segment の先頭 `k` 文字。source-preserving extraction 用の局所版。 -/
private theorem segment_take_of_le_source
    (O : OddOrbit) {i m k : ℕ}
    (hk : k ≤ m) :
    (O.segment i m).take k = O.segment i k := by
  induction k generalizing i m with
  | zero => simp
  | succ k ih =>
      cases m with
      | zero => omega
      | succ m =>
          have hk' : k ≤ m := by omega
          simp only [OddOrbit.segment_succ, List.take_succ_cons]
          simpa using ih (i := i + 1) (m := m) hk'

theorem exists_endpointFloorZeroPacket_with_sourceStart
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    (hGap : External.TwoThreeEffectiveGapInput) :
    ∃ v : Collatz.Word,
    ∃ boundary : ℕ,
      EndpointFloorZero.Packet v boundary ∧
        O.value R.startIndex ≤ Word.canonicalStart (1 :: v) := by
  classical
  let C := D.minimalPositiveCandidate
  have hFirst : Word.FirstCrossing C.word :=
    D.minimalPositiveCandidate_firstCrossing
  have hCanonicalPositive :
      Word.canonicalStart C.word < Word.canonicalEnd C.word :=
    hFirst.terminalContracting.canonicalStart_lt_canonicalEnd_of_runs_positive
      C.word_nonempty C.runs C.positive
  have hObs :
      Word.SmallestFirstParadoxicalExactObstruction C.word :=
    hFirst.to_smallestFirstParadoxicalExactObstruction_of_positive
      C.valid hCanonicalPositive
  let Q :
      Word.ReplayCoordinate
        C.word
        (O.value (R.startIndex + C.startCut))
        (O.value (R.startIndex + C.endCut)) :=
    Word.ReplayCoordinate.ofRuns C.runs C.word_nonempty
  have hQzero : Q.quotient = 0 := by
    simpa [Q] using
      hObs.replayQuotient_eq_zero_of_runs_positive hGap C.runs C.positive
  have hStartCanonical :
      O.value (R.startIndex + C.startCut) =
        Word.canonicalStart C.word :=
    Q.start_eq_canonical_of_quotient_eq_zero hQzero
  have hSourceStartLeActual :
      O.value R.startIndex ≤
        O.value (R.startIndex + C.startCut) := by
    exact R.startFutureMinimum.le_segment_end C.startCut
  have hSourceStartLeCanonical :
      O.value R.startIndex ≤ Word.canonicalStart C.word := by
    rw [← hStartCanonical]
    exact hSourceStartLeActual
  have hEndCanonical :
      O.value (R.startIndex + C.endCut) =
        Word.canonicalEnd C.word := by
    have h := Q.finish_eq
    rw [hQzero] at h
    simpa using h
  have hPureFloor :
      ∀ (m y : ℕ),
        0 < m →
        m < C.word.length →
        Word.Runs (C.word.take m) C.word.canonicalStart y →
        C.word.canonicalEnd < y := by
    intro m y hmPos hmLt hprefix
    have hmLe : m ≤ C.length := by
      have hmLt' : m < C.length := by simpa using hmLt
      omega
    have hactual :=
      O.runsSegment (R.startIndex + C.startCut) m
    have htake :=
      segment_take_of_le_source O
        (i := R.startIndex + C.startCut)
        (m := C.length)
        (k := m) hmLe
    have hactual' :
        Word.Runs (C.word.take m)
          (Word.canonicalStart C.word)
          (O.value ((R.startIndex + C.startCut) + m)) := by
      rw [← hStartCanonical]
      have hwordTake :
          C.word.take m =
            O.segment (R.startIndex + C.startCut) m := by
        dsimp [PositiveSubsegmentCandidate.word]
        exact htake
      rw [hwordTake]
      exact hactual
    have hy :
        y = O.value ((R.startIndex + C.startCut) + m) :=
      hprefix.end_unique_of_same_start_same_length hactual' rfl
    have hfloor :=
      D.minimalPositiveCandidate_endpointFloor_actual
        (k := m) hmPos (by simpa using hmLt)
    have hendCut := C.endCut_eq_startCut_add_length
    have hEndCanonical' :
        O.value (R.startIndex + (C.startCut + C.length)) =
          Word.canonicalEnd C.word := by
      rw [← hendCut]
      exact hEndCanonical
    rw [hEndCanonical'] at hfloor
    rw [hy]
    simpa [C, Nat.add_assoc] using hfloor
  obtain ⟨v, hvNe, hCv⟩ := hObs.exists_prependOne_form
  rw [hCv] at hObs hPureFloor hSourceStartLeCanonical
  have hPureFloor' :
      ∀ (m y : ℕ),
        0 < m →
        m < (1 :: v).length →
        Word.Runs ((1 :: v).take m)
          (Word.canonicalStart (1 :: v)) y →
        Word.canonicalEnd (1 :: v) < y :=
    hPureFloor
  obtain ⟨boundary, quotient, hReplay⟩ :=
    Word.exists_prependOneReplayData hObs.valid hvNe
  have hTailAll : Word.AllSuffixesContracting v := by
    have hAll := hObs.allSuffixesContracting
    change
      Word.Contracting (1 :: v) ∧
        Word.AllSuffixesContracting v at hAll
    exact hAll.2
  have hQuotientZero : quotient = 0 := by
    by_contra hq0
    have hqPos : 0 < quotient := Nat.pos_of_ne_zero hq0
    have hCore :=
      Word.prependOneCore_positive
        hGap hvNe hObs.firstCrossing.terminalContracting
        hTailAll hqPos
    have hdesc :=
      Word.canonicalEnd_le_canonicalStart_of_prependOneCore
        hObs.firstCrossing.terminalContracting hReplay hCore
    exact (Nat.not_le_of_gt hObs.positiveReturn) hdesc
  subst quotient
  exact
    ⟨v, boundary,
      {
        tail_nonempty := hvNe
        replay := hReplay
        paradoxical := hObs
        endpointFloor := hPureFloor'
      },
      hSourceStartLeCanonical⟩

end FirstCrossingData.NaturalZeroReplaySignChangeData

namespace CanonicalChain

/-- adjacent gap の odd part はその gap 自身以下。 -/
theorem gapOddPart_le_valueGap
    {O : OddOrbit} (C : CanonicalChain O) (k : ℕ) :
    (C.core.valuationData k).gapOddPart ≤
      (C.state k).valueGap := by
  let V := C.core.valuationData k
  have hfactor :
      (C.state k).valueGap =
        2 ^ V.gapDepth * V.gapOddPart :=
    V.gapFactor.1
  have hpowPos : 0 < 2 ^ V.gapDepth :=
    Nat.pow_pos (by omega)
  have hpowOne : 1 ≤ 2 ^ V.gapDepth := by omega
  have hmul :
      V.gapOddPart ≤ 2 ^ V.gapDepth * V.gapOddPart := by
    have h := Nat.mul_le_mul_right V.gapOddPart hpowOne
    simpa using h
  rw [hfactor]
  simpa [V] using hmul

/-- adjacent gap odd part は次の future-minimum start value より真に小さい。 -/
theorem gapOddPart_lt_nextStartValue
    {O : OddOrbit} (C : CanonicalChain O) (k : ℕ) :
    (C.core.valuationData k).gapOddPart <
      (C.state (k + 1)).startValue := by
  have hOddLe := C.gapOddPart_le_valueGap k
  have hStartPos : 0 < (C.state k).startValue := by
    exact O.value_pos (C.state k).startIndex
  have hnext :
      (C.state k).nextValue =
        (C.state k).startValue + (C.state k).valueGap :=
    (C.state k).nextValue_eq_startValue_add_valueGap
  have hGapLtNext :
      (C.state k).valueGap < (C.state k).nextValue := by
    omega
  have hcoherent :
      (C.state k).nextValue =
        (C.state (k + 1)).startValue := by
    simpa [CanonicalChain.state] using
      C.core.nextValue_eq_next_startValue k
  rw [← hcoherent]
  exact lt_of_le_of_lt hOddLe hGapLtNext

/--
source-preserving endpoint-floor coordinate `q=n+d` は、
直前 adjacent gap の odd part を `4*q` より真に大きく包む。
-/
theorem gapOddPart_lt_four_mul_endpointFloorCoordinateSum
    {O : OddOrbit} (C : CanonicalChain O) (k : ℕ)
    {v : Collatz.Word} {n d : ℕ}
    (A : EndpointFloorZero.CoordinateData v n d)
    (hSource :
      (C.state (k + 1)).startValue ≤
        Word.canonicalStart (1 :: v)) :
    (C.core.valuationData k).gapOddPart < 4 * (n + d) := by
  have hOdd := C.gapOddPart_lt_nextStartValue k
  calc
    (C.core.valuationData k).gapOddPart
        < (C.state (k + 1)).startValue := hOdd
    _ ≤ Word.canonicalStart (1 :: v) := hSource
    _ < Word.canonicalStart (1 :: v) + 1 := Nat.lt_succ_self _
    _ = 4 * (n + d) := A.fullStart_add_one

/--
次 state の natural `j=0` packet から、直前 gap odd part を支配する
endpoint-floor coordinate を実際に構成する。
-/
theorem exists_endpointFloorZeroPacket_with_previousGapOddPart_bound
    {O : OddOrbit} (C : CanonicalChain O) (k : ℕ)
    (D :
      FirstCrossingData.NaturalZeroReplaySignChangeData
        (C.firstCrossing (k + 1)))
    (hGap : External.TwoThreeEffectiveGapInput) :
    ∃ v : Collatz.Word,
    ∃ boundary n d : ℕ,
      EndpointFloorZero.Packet v boundary ∧
      EndpointFloorZero.CoordinateData v n d ∧
      (C.core.valuationData k).gapOddPart < 4 * (n + d) := by
  obtain ⟨v, boundary, P, hSourceRaw⟩ :=
    D.exists_endpointFloorZeroPacket_with_sourceStart hGap
  have hSource :
      (C.state (k + 1)).startValue ≤
        Word.canonicalStart (1 :: v) := by
    simpa [State.startValue] using hSourceRaw
  obtain ⟨n, d, A⟩ := P.exists_coordinateData
  have hOdd :
      (C.core.valuationData k).gapOddPart < 4 * (n + d) :=
    C.gapOddPart_lt_four_mul_endpointFloorCoordinateSum
      k A hSource
  exact ⟨v, boundary, n, d, P, A, hOdd⟩

end CanonicalChain
end PositiveReturn
end AdjacentReturn
end Collatz
