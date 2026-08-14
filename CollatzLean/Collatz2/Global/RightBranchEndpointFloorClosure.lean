import CollatzLean.Collatz2.Global.CanonicalEndpointFloorContractingReturn
import CollatzLean.Collatz2.Global.RightBranchZeroReplay

set_option linter.style.longLine false
/-!
# Collatz2 Global: right branch endpoint-floor closure

right branch の endpoint-floor handoff を仮定ではなく最小性から構成する。

重要な点は、global minimum 起点の FirstCrossing 自身に endpoint floor を要求しないこと。
一般には FirstCrossing だけから

  terminal endpoint < every proper interior boundary

は従わない。

代わりに、その actual positive FirstCrossing の内部で

* actual positive
* all nonempty suffixes contracting

を同時に満たす subsegment を長さ最小で選ぶ。

最小性から

1. subsegment 全体が FirstCrossing
2. proper interior から terminal への positive suffix は存在しない
3. unbounded orbit の value injectivity により equality も存在しない

ので endpoint floor が得られる。

最後に `TwoThreeSmallGapExclusion` をその最小 FirstCrossing 自身へ適用し、
actual start/end = canonical start/end、すなわち q=0 を得る。

従って right branch は仮定なしで

  CanonicalEndpointFloorContractingReturn

へ落ちる。
-/

namespace Collatz2

namespace Word

/--
全 suffix contracting は arbitrary drop に保存される。
-/
theorem AllSuffixesContracting.drop
    {w : Word}
    (hAll : AllSuffixesContracting w)
    (k : ℕ) :
    AllSuffixesContracting (w.drop k) := by
  induction k generalizing w with
  | zero =>
      simpa
  | succ k ih =>
      cases w with
      | nil =>
          simp [AllSuffixesContracting,
            AllSuffixesNegativeDeterminant]
      | cons e w =>
          have hTail :
              AllSuffixesNegativeDeterminant w :=
            AllSuffixesNegativeDeterminant.tail hAll
          simpa using ih hTail

end Word

namespace OddOrbit

namespace EndpointFloorReduction


/-- segment を `k` step drop すると対応する後半 segment。 -/
private theorem segment_drop_of_le_local
    (O : OddOrbit)
    {i n k : ℕ}
    (hk : k ≤ n) :
    (O.segment i n).drop k =
      O.segment (i + k) (n - k) := by
  have hsum : k + (n - k) = n := by
    omega
  have h := O.segment_add i k (n - k)
  rw [hsum] at h
  rw [h]
  simp

/--
right branch から最初に得る、global-minimum 起点の actual positive FirstCrossing。
endpoint floor はまだ要求しない。
-/
structure PositiveFirstCrossingSource (O : OddOrbit) where
  unbounded : O.Unbounded
  length : ℕ
  length_pos : 0 < length

  firstCrossing :
    Word.FirstCrossing
      (O.segment O.globalMinimumIndex length)

  positive :
    O.globalMinimumValue <
      O.value (O.globalMinimumIndex + length)

/--
`¬ ForeverExpanding` から source FirstCrossing を segment index を失わず構成する。
-/
theorem exists_positiveFirstCrossingSource_of_not_foreverExpanding
    (O : OddOrbit)
    (hU : O.Unbounded)
    (hNot :
      ¬ Word.NestedSurvivalChain.ForeverExpanding
          O.toNestedSurvivalChain) :
    ∃ _S : PositiveFirstCrossingSource O, True := by
  classical
  have hNot' :
      ¬ ∀ n : ℕ,
        Word.Expanding (O.minimumTailWord n) := by
    simpa [
      Word.NestedSurvivalChain.ForeverExpanding,
      OddOrbit.toNestedSurvivalChain
    ] using hNot
  have hex :
      ∃ m : ℕ,
        ¬ Word.Expanding (O.minimumTailWord m) := by
    simpa using hNot'
  obtain ⟨m, hmNotExpanding⟩ := hex
  have hmContracting :
      Word.Contracting (O.minimumTailWord m) := by
    rcases
        Word.expanding_or_contracting_of_valid_nonempty
          (O.minimumTailWord_valid m)
          (O.minimumTailWord_nonempty m) with hE | hC
    · exact False.elim (hmNotExpanding hE)
    · exact hC
  obtain ⟨p, hpLe, hFirstRaw⟩ :=
    Word.exists_firstCrossing_of_contracting
      (O.minimumTailWord_valid m)
      (O.minimumTailWord_nonempty m)
      hmContracting
  have hlen :
      (O.minimumTailWord m).length = m + 1 := by
    unfold OddOrbit.minimumTailWord
    exact O.segment_length O.globalMinimumIndex (m + 1)
  have hpLeSegment : p ≤ m + 1 := by
    rw [hlen] at hpLe
    exact hpLe
  have hwordSegment :
      (O.minimumTailWord m).take p =
        O.segment O.globalMinimumIndex p := by
    unfold OddOrbit.minimumTailWord
    exact O.segment_take_of_le hpLeSegment
  have hFirst :
      Word.FirstCrossing
        (O.segment O.globalMinimumIndex p) := by
    rw [hwordSegment] at hFirstRaw
    exact hFirstRaw
  have hpPos : 0 < p := by
    have hlenPos :
        0 <
          (O.segment O.globalMinimumIndex p).length :=
      List.length_pos_iff.mpr hFirst.nonempty
    simpa using hlenPos
  have hle :
      O.globalMinimumValue ≤
        O.value (O.globalMinimumIndex + p) :=
    O.globalMinimumValue_le_value _
  have hne :
      O.globalMinimumValue ≠
        O.value (O.globalMinimumIndex + p) := by
    rw [← O.value_globalMinimumIndex]
    intro hEq
    have hIndex :=
      O.value_injective_of_unbounded hU hEq
    omega
  have hpos :
      O.globalMinimumValue <
        O.value (O.globalMinimumIndex + p) := by
    omega
  exact
    ⟨{
      unbounded := hU
      length := p
      length_pos := hpPos
      firstCrossing := hFirst
      positive := hpos
    }, trivial⟩

/--
source FirstCrossing 内の positive / all-suffix-contracting subsegment。
-/
structure PositiveSubsegmentCandidate
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O) where
  startCut : ℕ
  length : ℕ
  length_pos : 0 < length
  end_le_source : startCut + length ≤ S.length

  allSuffixesContracting :
    Word.AllSuffixesContracting
      (O.segment
        (O.globalMinimumIndex + startCut)
        length)

  positive :
    O.value
        (O.globalMinimumIndex + startCut) <
      O.value
        (O.globalMinimumIndex + (startCut + length))

namespace PositiveSubsegmentCandidate

/-- candidate word。 -/
noncomputable def word
    {O : OddOrbit}
    {S : PositiveFirstCrossingSource O}
    (C : PositiveSubsegmentCandidate S) : Word :=
  O.segment
    (O.globalMinimumIndex + C.startCut)
    C.length

@[simp] theorem word_length
    {O : OddOrbit}
    {S : PositiveFirstCrossingSource O}
    (C : PositiveSubsegmentCandidate S) :
    C.word.length = C.length := by
  simp [word]

/-- candidate word は nonempty。 -/
theorem word_nonempty
    {O : OddOrbit}
    {S : PositiveFirstCrossingSource O}
    (C : PositiveSubsegmentCandidate S) :
    C.word ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [C.word_length]
  exact C.length_pos

/-- candidate の actual normalized run。 -/
theorem runs
    {O : OddOrbit}
    {S : PositiveFirstCrossingSource O}
    (C : PositiveSubsegmentCandidate S) :
    Runs C.word
      (O.value
        (O.globalMinimumIndex + C.startCut))
      (O.value
        (O.globalMinimumIndex +
          (C.startCut + C.length))) := by
  have h :=
    O.runsSegment
      (O.globalMinimumIndex + C.startCut)
      C.length
  simpa [word, Nat.add_assoc] using h

/-- candidate は valid。 -/
theorem valid
    {O : OddOrbit}
    {S : PositiveFirstCrossingSource O}
    (C : PositiveSubsegmentCandidate S) :
    Word.Valid C.word :=
  C.runs.valid

/-- candidate 自身は contracting。 -/
theorem contracting
    {O : OddOrbit}
    {S : PositiveFirstCrossingSource O}
    (C : PositiveSubsegmentCandidate S) :
    Word.Contracting C.word := by
  have hAll :
      Word.AllSuffixesContracting C.word := by
    simpa [word] using C.allSuffixesContracting
  exact hAll.whole_contracting C.word_nonempty

/--
FirstCrossing prefix が actual-positive なら、その prefix 自身が candidate。
-/
theorem exists_prefix_candidate_of_firstCrossing_positive
    {O : OddOrbit}
    {S : PositiveFirstCrossingSource O}
    (C : PositiveSubsegmentCandidate S)
    {p : ℕ}
    (hpPos : 0 < p)
    (hpLe : p ≤ C.length)
    (hFirst : Word.FirstCrossing (C.word.take p))
    (hPositive :
      O.value
          (O.globalMinimumIndex + C.startCut) <
        O.value
          (O.globalMinimumIndex + (C.startCut + p))) :
    ∃ P : PositiveSubsegmentCandidate S,
      P.length = p := by
  have htake :
      C.word.take p =
        O.segment
          (O.globalMinimumIndex + C.startCut)
          p := by
    unfold word
    exact O.segment_take_of_le hpLe
  have hAll := hFirst.allSuffixesContracting
  rw [htake] at hAll
  let P : PositiveSubsegmentCandidate S := {
    startCut := C.startCut
    length := p
    length_pos := hpPos
    end_le_source := by
      have hbase := C.end_le_source
      omega
    allSuffixesContracting := hAll
    positive := hPositive
  }
  exact ⟨P, rfl⟩

/--
interior boundary が candidate start 以下なら、
そこから terminal までが shorter positive candidate。
-/
theorem exists_suffix_candidate_of_middle_le_start
    {O : OddOrbit}
    {S : PositiveFirstCrossingSource O}
    (C : PositiveSubsegmentCandidate S)
    {p : ℕ}
    (hpLt : p < C.length)
    (hMiddleLe :
      O.value
          (O.globalMinimumIndex + (C.startCut + p)) ≤
        O.value
          (O.globalMinimumIndex + C.startCut)) :
    ∃ P : PositiveSubsegmentCandidate S,
      P.length = C.length - p := by
  have hpLe : p ≤ C.length :=
    Nat.le_of_lt hpLt
  have hAllBase :
      Word.AllSuffixesContracting C.word := by
    simpa [word] using C.allSuffixesContracting
  have hAllDrop :=
    hAllBase.drop p
  have hdrop :
      C.word.drop p =
        O.segment
          ((O.globalMinimumIndex + C.startCut) + p)
          (C.length - p) := by
    unfold word
    have h :=
      segment_drop_of_le_local O
        (i := O.globalMinimumIndex + C.startCut)
        (n := C.length)
        (k := p)
        hpLe
    exact h
  rw [hdrop] at hAllDrop
  let P : PositiveSubsegmentCandidate S := {
    startCut := C.startCut + p
    length := C.length - p
    length_pos := Nat.sub_pos_of_lt hpLt
    end_le_source := by
      have hbase := C.end_le_source
      omega
    allSuffixesContracting := by
      simpa [Nat.add_assoc] using hAllDrop
    positive := by
      have hCEnd := C.positive
      have hEndIndex :
          C.startCut + p + (C.length - p) =
            C.startCut + C.length := by
        omega
      rw [hEndIndex]
      exact lt_of_le_of_lt hMiddleLe hCEnd
  }
  refine ⟨P, ?_⟩
  rfl

/--
proper interior boundary から terminal endpoint への suffix が positive なら、
その suffix 自身が shorter candidate。
-/
theorem exists_terminalSuffixCandidate_of_value_lt_endpoint
    {O : OddOrbit}
    {S : PositiveFirstCrossingSource O}
    (C : PositiveSubsegmentCandidate S)
    {k : ℕ}
    (hkLt : k < C.length)
    (hPositive :
      O.value
          (O.globalMinimumIndex + (C.startCut + k)) <
        O.value
          (O.globalMinimumIndex +
            (C.startCut + C.length))) :
    ∃ P : PositiveSubsegmentCandidate S,
      P.length = C.length - k := by
  have hkLe : k ≤ C.length :=
    Nat.le_of_lt hkLt
  have hAllBase :
      Word.AllSuffixesContracting C.word := by
    simpa [word] using C.allSuffixesContracting
  have hAllDrop :=
    hAllBase.drop k
  have hdrop :
      C.word.drop k =
        O.segment
          ((O.globalMinimumIndex + C.startCut) + k)
          (C.length - k) := by
    unfold word
    exact
      segment_drop_of_le_local O
        (i := O.globalMinimumIndex + C.startCut)
        (n := C.length)
        (k := k)
        hkLe
  rw [hdrop] at hAllDrop
  let P : PositiveSubsegmentCandidate S := {
    startCut := C.startCut + k
    length := C.length - k
    length_pos := Nat.sub_pos_of_lt hkLt
    end_le_source := by
      have hbase := C.end_le_source
      omega
    allSuffixesContracting := by
      simpa [Nat.add_assoc] using hAllDrop
    positive := by
      have hEndIndex :
          C.startCut + k + (C.length - k) =
            C.startCut + C.length := by
        omega
      rw [hEndIndex]
      exact hPositive
  }
  exact ⟨P, rfl⟩

end PositiveSubsegmentCandidate

/-- source 全体が candidate。 -/
def PositiveFirstCrossingSource.initialCandidate
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O) :
    PositiveSubsegmentCandidate S := {
  startCut := 0
  length := S.length
  length_pos := S.length_pos
  end_le_source := by simp
  allSuffixesContracting := by
    simpa using S.firstCrossing.allSuffixesContracting
  positive := by
    simpa [O.value_globalMinimumIndex] using S.positive
}

/-- candidate length の inhabitedness。 -/
theorem PositiveFirstCrossingSource.exists_candidate_length
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O) :
    ∃ m : ℕ,
      ∃ C : PositiveSubsegmentCandidate S,
        C.length = m := by
  exact ⟨S.length, S.initialCandidate, rfl⟩

/-- 最小 positive candidate length。 -/
noncomputable def PositiveFirstCrossingSource.minimalPositiveLength
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O) : ℕ := by
  classical
  exact Nat.find S.exists_candidate_length

/-- 最小 positive candidate。 -/
noncomputable def PositiveFirstCrossingSource.minimalPositiveCandidate
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O) :
    PositiveSubsegmentCandidate S := by
  classical
  exact Classical.choose
    (Nat.find_spec S.exists_candidate_length)

/-- 最小 candidate の length。 -/
theorem PositiveFirstCrossingSource.minimalPositiveCandidate_length
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O) :
    S.minimalPositiveCandidate.length =
      S.minimalPositiveLength := by
  classical
  simpa [
    PositiveFirstCrossingSource.minimalPositiveCandidate,
    PositiveFirstCrossingSource.minimalPositiveLength
  ] using
    (Classical.choose_spec
      (Nat.find_spec S.exists_candidate_length))

/-- 最小 length は任意 candidate 以下。 -/
theorem PositiveFirstCrossingSource.minimalPositiveLength_le
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O)
    (C : PositiveSubsegmentCandidate S) :
    S.minimalPositiveLength ≤ C.length := by
  classical
  simpa [PositiveFirstCrossingSource.minimalPositiveLength] using
    (Nat.find_min'
      S.exists_candidate_length
      ⟨C, rfl⟩)

namespace PositiveSubsegmentCandidate

/--
長さ最小 candidate の FirstCrossing prefix は whole word でなければならない。
-/
theorem firstCrossing_take_length_eq_of_minimal
    {O : OddOrbit}
    {S : PositiveFirstCrossingSource O}
    (C : PositiveSubsegmentCandidate S)
    (hMinimal :
      C.length = S.minimalPositiveLength)
    {p : ℕ}
    (hpLe : p ≤ C.length)
    (hFirst : Word.FirstCrossing (C.word.take p)) :
    p = C.length := by
  have hpPos : 0 < p := by
    have hne := hFirst.nonempty
    by_contra hnot
    have hp0 : p = 0 := by omega
    subst p
    simp at hne
  by_contra hpNe
  have hpLt : p < C.length := by
    omega
  by_cases hPrefixPositive :
      O.value
          (O.globalMinimumIndex + C.startCut) <
        O.value
          (O.globalMinimumIndex + (C.startCut + p))
  · obtain ⟨P, hPLen⟩ :=
      C.exists_prefix_candidate_of_firstCrossing_positive
        hpPos hpLe hFirst hPrefixPositive
    have hmin :=
      S.minimalPositiveLength_le P
    rw [← hMinimal, hPLen] at hmin
    omega
  · have hMiddleLe :
        O.value
            (O.globalMinimumIndex + (C.startCut + p)) ≤
          O.value
            (O.globalMinimumIndex + C.startCut) :=
      Nat.le_of_not_gt hPrefixPositive
    obtain ⟨P, hPLen⟩ :=
      C.exists_suffix_candidate_of_middle_le_start
        hpLt hMiddleLe
    have hmin :=
      S.minimalPositiveLength_le P
    rw [← hMinimal, hPLen] at hmin
    omega

end PositiveSubsegmentCandidate

/-- 最小 candidate 自身が FirstCrossing。 -/
theorem PositiveFirstCrossingSource.minimalPositiveCandidate_firstCrossing
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O) :
    Word.FirstCrossing
      S.minimalPositiveCandidate.word := by
  classical
  let C := S.minimalPositiveCandidate
  have hCValid : Word.Valid C.word :=
    C.valid
  have hCNe : C.word ≠ [] :=
    C.word_nonempty
  have hCC : Word.Contracting C.word :=
    C.contracting
  obtain ⟨p, hpLeWord, hFirstRaw⟩ :=
    Word.exists_firstCrossing_of_contracting
      hCValid hCNe hCC
  have hpLe : p ≤ C.length := by
    simpa using hpLeWord
  have hMinimal :
      C.length = S.minimalPositiveLength := by
    simpa [C] using
      S.minimalPositiveCandidate_length
  have hpEq :
      p = C.length :=
    C.firstCrossing_take_length_eq_of_minimal
      hMinimal hpLe hFirstRaw
  subst p
  have hTake :
      List.take C.length C.word = C.word := by
    rw [← C.word_length]
    exact List.take_length
  rw [hTake] at hFirstRaw
  simpa [C] using hFirstRaw
/--
最小 candidate の proper interior boundary は terminal endpoint 未満ではない。
-/
theorem PositiveFirstCrossingSource.minimalPositiveCandidate_not_interior_below_endpoint
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < S.minimalPositiveCandidate.length) :
    ¬
      O.value
          (O.globalMinimumIndex +
            (S.minimalPositiveCandidate.startCut + k)) <
        O.value
          (O.globalMinimumIndex +
            (S.minimalPositiveCandidate.startCut +
              S.minimalPositiveCandidate.length)) := by
  intro hPositive
  have hExists :
      ∃ P : PositiveSubsegmentCandidate S,
        P.length =
          S.minimalPositiveCandidate.length - k :=
    S.minimalPositiveCandidate.exists_terminalSuffixCandidate_of_value_lt_endpoint
        hkLt hPositive
  rcases hExists with ⟨P, hPLen⟩
  have hmin :
      S.minimalPositiveLength ≤ P.length :=
    S.minimalPositiveLength_le P
  have hCmin :
      S.minimalPositiveCandidate.length =
        S.minimalPositiveLength :=
    S.minimalPositiveCandidate_length
  have hLower :
      S.minimalPositiveCandidate.length ≤ P.length := by
    rw [hCmin]
    exact hmin
  rw [hPLen] at hLower
  omega

/--
最小 candidate の proper interior boundary と endpoint は value-injective により異なる。
-/
theorem PositiveFirstCrossingSource.minimalPositiveCandidate_interior_value_ne_endpoint
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O)
    {k : ℕ}
    (hkLt : k < S.minimalPositiveCandidate.length) :
    O.value
        (O.globalMinimumIndex +
          (S.minimalPositiveCandidate.startCut + k)) ≠
      O.value
        (O.globalMinimumIndex +
          (S.minimalPositiveCandidate.startCut +
            S.minimalPositiveCandidate.length)) := by
  intro hValue
  have hIndex :=
    O.value_injective_of_unbounded S.unbounded hValue
  omega

/--
最小 candidate の全 proper interior boundary は terminal endpoint より strict に上。
-/
theorem PositiveFirstCrossingSource.minimalPositiveCandidate_endpointFloor
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < S.minimalPositiveCandidate.length) :
    O.value
        (O.globalMinimumIndex +
          (S.minimalPositiveCandidate.startCut +
            S.minimalPositiveCandidate.length)) <
      O.value
        (O.globalMinimumIndex +
          (S.minimalPositiveCandidate.startCut + k)) := by
  have hNotBelow :=
    S.minimalPositiveCandidate_not_interior_below_endpoint
      hkPos hkLt
  have hNe :=
    S.minimalPositiveCandidate_interior_value_ne_endpoint
      hkLt
  omega

/--
source を最小化し、small-gap exclusion で最小 candidate 自身を q=0 にして
canonical endpoint-floor contracting return を得る。
-/
noncomputable def PositiveFirstCrossingSource.toCanonicalEndpointFloorContractingReturn
    {O : OddOrbit}
    (S : PositiveFirstCrossingSource O)
    (hGap : TwoThreeSmallGapExclusion) :
    CanonicalEndpointFloorContractingReturn O := by
  classical
  let C := S.minimalPositiveCandidate
  have hFirst :
      Word.FirstCrossing C.word := by
    simpa [C] using
      S.minimalPositiveCandidate_firstCrossing
  have hCanonical :=
    hFirst.actual_eq_canonical_of_twoThreeSmallGapExclusion
      hGap C.runs C.positive
  exact {
    unbounded := S.unbounded
    startIndex :=
      O.globalMinimumIndex + C.startCut
    length := C.length
    length_pos := C.length_pos
    firstCrossing := by
      simpa [PositiveSubsegmentCandidate.word]
        using hFirst
    positive := by
      simpa [Nat.add_assoc] using C.positive
    endpointFloor := by
      intro k hkPos hkLt
      have h :=
        S.minimalPositiveCandidate_endpointFloor
          (k := k) hkPos (by simpa [C] using hkLt)
      simpa [C, Nat.add_assoc] using h
    startCanonical := by
      have h := hCanonical.1
      simpa [PositiveSubsegmentCandidate.word, C]
        using h
    endCanonical := by
      have h := hCanonical.2
      simpa [
        PositiveSubsegmentCandidate.word,
        C,
        Nat.add_assoc
      ] using h
  }

/--
`¬ ForeverExpanding` right branch は endpoint-floor assumption なしで
canonical endpoint-floor contracting return を一つ含む。
-/
theorem exists_canonicalEndpointFloorContractingReturn_of_not_foreverExpanding
    (hGap : TwoThreeSmallGapExclusion)
    (O : OddOrbit)
    (hU : O.Unbounded)
    (hNot :
      ¬ Word.NestedSurvivalChain.ForeverExpanding
          O.toNestedSurvivalChain) :
    ∃ _D : CanonicalEndpointFloorContractingReturn O,
      True := by
  classical
  obtain ⟨S, _⟩ :=
    exists_positiveFirstCrossingSource_of_not_foreverExpanding
      O hU hNot
  exact
    ⟨S.toCanonicalEndpointFloorContractingReturn hGap,
      trivial⟩

end EndpointFloorReduction
end OddOrbit

/--
外部 small-gap exclusion の下で、非有界 right branch は

* ForeverExpanding
* CanonicalEndpointFloorContractingReturn

の二つへ直接圧縮される。

`FirstCrossingEndpointFloorSource` はもはや仮定として不要。
-/
theorem hasUnboundedOddOrbit_to_foreverExpanding_or_canonicalEndpointFloorContractingReturn
    (hGap : TwoThreeSmallGapExclusion) :
    HasUnboundedOddOrbit →
      ∃ O : OddOrbit,
        O.Unbounded ∧
          (
            Word.NestedSurvivalChain.ForeverExpanding
              O.toNestedSurvivalChain
            ∨
            ∃ _D :
                OddOrbit.CanonicalEndpointFloorContractingReturn O,
              True
          ) := by
  classical
  rintro ⟨O, hU⟩
  refine ⟨O, hU, ?_⟩
  by_cases hE :
      Word.NestedSurvivalChain.ForeverExpanding
        O.toNestedSurvivalChain
  · exact Or.inl hE
  · exact Or.inr
      (OddOrbit.EndpointFloorReduction.exists_canonicalEndpointFloorContractingReturn_of_not_foreverExpanding
        hGap O hU hE)

end Collatz2
