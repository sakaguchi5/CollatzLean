import CollatzLean.Collatz.AdjacentReturn.CanonicalLate
import CollatzLean.Collatz.Canonical.CylinderDynamics

/-!
# canonical Late packetとactual continuation

十分長いLate adjacent returnをOddOrbitから切り離した有限語packetへ射影する。
packetから先のactual odd continuationは同じ自然数sourceをcanonical sourceとして保つ。
さらにsource未満へのfirst descentを有限prefix witnessとして観測する。
-/

namespace Collatz
namespace AdjacentReturn

open Word

/--
canonical化されたLate returnの純有限語データ。
`A`がfirst crossing、`C`がその後next future minimumまでのsuffix。
-/
structure CanonicalLatePacket (A C : Collatz.Word) : Prop where
  valid : (A ++ C).Valid
  crossing : A.FirstCrossing
  suffix_nonempty : C ≠ []
  suffix_allSuffixesContracting : C.AllSuffixesContracting
  zeroDigit : A.extensionDigit C = 0
  source_lt_endpoint :
    A.canonicalStart < (A ++ C).canonicalEnd
  endpoint_lt_peak :
    (A ++ C).canonicalEnd < A.canonicalEnd

namespace CanonicalLatePacket

/-- packetの全語。 -/
def fullWord {A C : Collatz.Word} (_P : CanonicalLatePacket A C) :
    Collatz.Word := A ++ C

/-- packetのsource。 -/
def source {A C : Collatz.Word} (_P : CanonicalLatePacket A C) : ℕ :=
  A.canonicalStart

/-- first crossing peak。 -/
def peak {A C : Collatz.Word} (_P : CanonicalLatePacket A C) : ℕ :=
  A.canonicalEnd

/-- Late suffix終端。 -/
def endpoint {A C : Collatz.Word} (_P : CanonicalLatePacket A C) : ℕ :=
  (A ++ C).canonicalEnd

/-- crossing wordはvalid。 -/
theorem crossing_valid
    {A C : Collatz.Word} (P : CanonicalLatePacket A C) :
    A.Valid :=
  P.valid.prefix

/-- packet全語のcanonical startはcrossing sourceと同じ。 -/
theorem full_canonicalStart_eq_source
    {A C : Collatz.Word} (P : CanonicalLatePacket A C) :
    P.fullWord.canonicalStart = P.source := by
  unfold fullWord source
  have h :=
    canonicalStart_append_eq
      (u := A) (v := C) P.valid P.crossing.nonempty
  rw [P.zeroDigit] at h
  simpa using h

/-- packetのfirst crossingはcanonical actual run。 -/
theorem crossingRuns
    {A C : Collatz.Word} (P : CanonicalLatePacket A C) :
    Runs A P.source P.peak := by
  unfold source peak
  exact P.crossing_valid.canonicalRuns

/-- packet全体は同じsourceからendpointへのactual run。 -/
theorem fullRuns
    {A C : Collatz.Word} (P : CanonicalLatePacket A C) :
    Runs P.fullWord P.source P.endpoint := by
  have h :
      Runs
        P.fullWord
        (Word.canonicalStart P.fullWord)
        P.endpoint := by
    simpa [fullWord, endpoint] using P.valid.canonicalRuns
  rw [P.full_canonicalStart_eq_source] at h
  exact h

/-- packet suffix内部の全一文字extension digitも0。 -/
theorem allExtensionDigitsZero
    {A C : Collatz.Word} (P : CanonicalLatePacket A C) :
    A.AllExtensionDigitsZero C := by
  exact
    allExtensionDigitsZero_of_extensionDigit_eq_zero
      P.valid P.crossing.nonempty P.zeroDigit

/-- packet endpointはsourceより上。 -/
theorem source_lt_endpoint'
    {A C : Collatz.Word} (P : CanonicalLatePacket A C) :
    P.source < P.endpoint := by
  simpa [source, endpoint] using P.source_lt_endpoint

/-- packet peakはendpointより上。 -/
theorem endpoint_lt_peak'
    {A C : Collatz.Word} (P : CanonicalLatePacket A C) :
    P.endpoint < P.peak := by
  simpa [endpoint, peak] using P.endpoint_lt_peak

end CanonicalLatePacket

namespace FirstCrossingData

/--
Baker型gap下界のもと、十分長いLate項はcanonical finite packetへ射影できる。
-/
theorem canonicalLatePacket_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
      ∀ F : FirstCrossingData R,
        F.IsLate →
        N ≤ F.length →
          CanonicalLatePacket
            (R.word.take F.length)
            F.lateSuffixWord := by
  obtain ⟨N, hN⟩ :=
    replayQuotient_eq_zero_eventually hGap
  refine ⟨N, ?_⟩
  intro O R F hLate hlen
  let A : Collatz.Word := R.word.take F.length
  let C : Collatz.Word := F.lateSuffixWord
  have hq : F.replayCoordinate.quotient = 0 :=
    hN O R F hlen
  have hstart :
      R.startValue = A.canonicalStart := by
    simpa [A] using
      F.replayCoordinate.start_eq_canonical_of_quotient_eq_zero hq
  have hpeak :
      F.endpointValue = A.canonicalEnd := by
    have h := F.replayCoordinate.finish_eq
    rw [hq] at h
    simpa [A] using h
  have hword :
      R.word = A ++ C := by
    simpa [A, C] using F.word_eq_crossing_append_lateSuffix
  have hvalid : (A ++ C).Valid := by
    rw [← hword]
    exact R.word_valid
  have hzero : A.extensionDigit C = 0 := by
    simpa [A, C] using
      F.lateSuffix_extensionDigit_eq_zero_of_start_canonical
        hLate (by simpa [A] using hstart)
  have hAne : A ≠ [] := by
    simpa [A] using F.crossing.nonempty
  have hstartWhole :
      (A ++ C).canonicalStart = A.canonicalStart := by
    have h :=
      canonicalStart_append_eq
        (u := A) (v := C) hvalid hAne
    rw [hzero] at h
    simpa using h
  have hrealWhole :
      (A ++ C).Realizes R.startValue R.nextValue := by
    rw [← hword]
    exact R.realizes
  have hnextOdd : Odd R.nextValue := by
    unfold State.nextValue
    exact O.value_odd _
  let W : Word.ReplayCoordinate
      (A ++ C) R.startValue R.nextValue :=
    Word.ReplayCoordinate.ofRealization hrealWhole hnextOdd
  have hwholeStart :
      R.startValue = (A ++ C).canonicalStart := by
    calc
      R.startValue = A.canonicalStart := hstart
      _ = (A ++ C).canonicalStart := hstartWhole.symm
  have hWzero : W.quotient = 0 :=
    W.quotient_eq_zero_of_start_eq_canonical hwholeStart
  have hendpoint :
      R.nextValue = (A ++ C).canonicalEnd := by
    have h := W.finish_eq
    rw [hWzero] at h
    simpa using h
  have hFLt :
      F.length < R.length := by
    exact hLate
  have hCnonempty : C ≠ [] := by
    apply List.ne_nil_of_length_pos
    have hClength :
        C.length = R.length - F.length := by
      simp [C, lateSuffixWord]
    rw [hClength]
    exact Nat.sub_pos_of_lt hFLt
  have hCall : C.AllSuffixesContracting := by
    change
      (O.segment
        (R.startIndex + F.length)
        (R.length - F.length)).AllSuffixesContracting
    exact
      R.properSuffix_allSuffixesContracting
        F.length_pos hFLt
  have hsourceEndpoint :
      Word.canonicalStart A <
        Word.canonicalEnd (A ++ C) := by
    calc
      Word.canonicalStart A
          = R.startValue := hstart.symm
      _ < R.nextValue := R.startValue_lt_nextValue
      _ = Word.canonicalEnd (A ++ C) := hendpoint
  have hnextLePeak :
      R.nextValue ≤ F.endpointValue := by
    simpa [endpointValue] using
      R.nextValue_le_positiveEndpoint
        F.length F.length_pos
  have hindexLt :
      R.startIndex + F.length < R.nextIndex := by
    rw [R.nextIndex_eq_startIndex_add_length]
    exact Nat.add_lt_add_left hFLt R.startIndex
  have hnePeak :
      F.endpointValue ≠ R.nextValue := by
    unfold endpointValue State.nextValue
    exact O.value_ne_of_lt_of_unbounded R.unbounded hindexLt
  have hendpointPeak :
      (A ++ C).canonicalEnd < A.canonicalEnd := by
    rw [← hendpoint, ← hpeak]
    omega
  exact
    ⟨hvalid,
      by simpa [A] using F.crossing,
      hCnonempty,
      hCall,
      hzero,
      hsourceEndpoint,
      hendpointPeak⟩

end FirstCrossingData

/-- packet endpointからさらにactual odd wordを走らせる有限continuation。 -/
structure CanonicalLateContinuation
    {A C : Collatz.Word} (P : CanonicalLatePacket A C) where
  word : Collatz.Word
  finish : ℕ
  runs : Runs word P.endpoint finish

namespace CanonicalLateContinuation

/-- continuationをpacket全体へ連結したword。 -/
def extendedWord
    {A C : Collatz.Word} {P : CanonicalLatePacket A C}
    (K : CanonicalLateContinuation P) : Collatz.Word :=
  P.fullWord ++ K.word

/-- packetとcontinuationを連結したactual run。 -/
theorem fullRuns
    {A C : Collatz.Word} {P : CanonicalLatePacket A C}
    (K : CanonicalLateContinuation P) :
    Runs K.extendedWord P.source K.finish := by
  unfold extendedWord
  exact P.fullRuns.append K.runs

/-- packet全語は非空。 -/
theorem packetWord_nonempty
    {A C : Collatz.Word} (P : CanonicalLatePacket A C) :
    P.fullWord ≠ [] := by
  unfold CanonicalLatePacket.fullWord
  intro h
  apply P.crossing.nonempty
  cases A with
  | nil =>
      rfl
  | cons a A =>
      simp at h

/-- continuationをどれだけ伸ばしてもcanonical startは同じ自然数source。 -/
theorem extended_canonicalStart_eq_source
    {A C : Collatz.Word} {P : CanonicalLatePacket A C}
    (K : CanonicalLateContinuation P) :
    K.extendedWord.canonicalStart = P.source := by
  have hrun := K.fullRuns
  have hnonempty : K.extendedWord ≠ [] := by
    unfold extendedWord
    cases hfull : P.fullWord with
    | nil =>
        exfalso
        exact packetWord_nonempty P hfull
    | cons a w =>
        simp
  have hfinishOdd : Odd K.finish :=
    hrun.end_odd_of_ne_nil hnonempty
  have hmodulus :
      K.extendedWord.residueModulus =
        P.fullWord.residueModulus * 2 ^ K.word.twoSteps := by
    simp [extendedWord, residueModulus, twoSteps_append, pow_add]
    ac_rfl
  have hpowOne : 1 ≤ 2 ^ K.word.twoSteps := by
    have hpos : 0 < 2 ^ K.word.twoSteps :=
      Nat.pow_pos (by omega)
    omega
  have hmodLe :
      P.fullWord.residueModulus ≤
        K.extendedWord.residueModulus := by
    rw [hmodulus]
    have h :=
      Nat.mul_le_mul_left P.fullWord.residueModulus hpowOne
    simpa using h
  have hsourceLtBase :
      P.source < P.fullWord.residueModulus := by
    rw [← P.full_canonicalStart_eq_source]
    exact canonicalStart_lt_modulus P.fullWord
  have hsourceLt :
      P.source < K.extendedWord.residueModulus :=
    lt_of_lt_of_le hsourceLtBase hmodLe
  have h :=
    hrun.realizes.eq_canonicalStart_of_lt_modulus
      hfinishOdd hsourceLt
  exact h.symm

/-- actual continuation全体もpacket full wordから見たzero cylinder。 -/
theorem extensionDigit_eq_zero
    {A C : Collatz.Word} {P : CanonicalLatePacket A C}
    (K : CanonicalLateContinuation P) :
    Word.extensionDigit P.fullWord K.word = 0 := by
  unfold Word.extensionDigit
  change
    Word.canonicalStart K.extendedWord /
        Word.residueModulus P.fullWord = 0
  rw [K.extended_canonicalStart_eq_source]
  rw [← P.full_canonicalStart_eq_source]
  exact
    Nat.div_eq_of_lt
      (Word.canonicalStart_lt_modulus P.fullWord)

/-- continuationの長さ`n`でsource未満へ降りること。 -/
def DescentAt
    {A C : Collatz.Word} {P : CanonicalLatePacket A C}
    (K : CanonicalLateContinuation P) (n : ℕ) : Prop :=
  0 < n ∧
  n ≤ K.word.length ∧
  ∃ y : ℕ,
    Runs (K.word.take n) P.endpoint y ∧
    y < P.source

/-- continuation内のどこかでsource未満へ降りること。 -/
def HasDescentBelowSource
    {A C : Collatz.Word} {P : CanonicalLatePacket A C}
    (K : CanonicalLateContinuation P) : Prop :=
  ∃ n : ℕ, K.DescentAt n

/-- source未満への最初の有限prefix descent。 -/
structure FirstDescentData
    {A C : Collatz.Word} {P : CanonicalLatePacket A C}
    (K : CanonicalLateContinuation P) where
  length : ℕ
  length_pos : 0 < length
  le_continuation : length ≤ K.word.length
  value : ℕ
  runs : Runs (K.word.take length) P.endpoint value
  below : value < P.source
  minimal :
    ∀ m : ℕ,
      0 < m →
      m < length →
      ∀ y : ℕ,
        Runs (K.word.take m) P.endpoint y →
        P.source ≤ y

/-- descentが存在すれば最初のdescent witnessを取れる。 -/
theorem existsFirstDescentData
    {A C : Collatz.Word} {P : CanonicalLatePacket A C}
    (K : CanonicalLateContinuation P)
    (h : K.HasDescentBelowSource) :
    Nonempty (FirstDescentData K) := by
  classical
  let Bad : ℕ → Prop :=
    fun n => K.DescentAt n
  have hbad : ∃ n : ℕ, Bad n := by
    simpa [Bad, HasDescentBelowSource] using h
  let n := Nat.find hbad
  have hnBad : Bad n := by
    dsimp [n]
    exact Nat.find_spec hbad
  rcases hnBad with ⟨hnPos, hnLe, y, hrun, hy⟩
  refine ⟨⟨n, hnPos, hnLe, y, hrun, hy, ?_⟩⟩
  intro m hmPos hmLt z hz
  by_contra hnot
  have hzBelow : z < P.source := Nat.lt_of_not_ge hnot
  have hmBad : Bad m := by
    exact ⟨hmPos, by omega, z, hz, hzBelow⟩
  have hmin : n ≤ m := by
    dsimp [n]
    exact Nat.find_min' hbad hmBad
  omega

end CanonicalLateContinuation

end AdjacentReturn
end Collatz
