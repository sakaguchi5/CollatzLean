import CollatzLean.Collatz2.Global.CanonicalAdjacentContractingReturn
import CollatzLean.Collatz2.Global.RightBranchZeroReplay
import CollatzLean.Collatz2.Native.ReplayDynamics

/-!
# Collatz2 Global: q=0 FirstCrossing から adjacent contracting return へ

1--5 の finite reduction が最終的に渡すべき handoff は、global-minimum tail 上の
FirstCrossing segment と terminal endpoint floor だけでよい。

proper interior boundary が terminal endpoint より上なら、その endpoint 以後の tail minimum
まで block を延長することで

* endpoint は future minimum
* 全 interior boundary は新 endpoint より上
* whole block は contracting
* q=0 / canonical start は append 後も保持
* actual endpoint も canonical endpoint

となる。

従って final object は FirstCrossing ではなく
`CanonicalAdjacentContractingReturn` へ圧縮される。
-/

namespace Collatz2
namespace OddOrbit

/--
1--5 側から global reduction へ渡す最小 packet。

`endpointFloor` は proper interior boundary が original FirstCrossing endpoint より
strict に上にあることを表す。
-/
structure FirstCrossingEndpointFloorSource (O : OddOrbit) where
  unbounded : O.Unbounded
  length : ℕ
  length_pos : 0 < length

  firstCrossing :
    Word.FirstCrossing
      (O.segment O.globalMinimumIndex length)

  positive :
    O.globalMinimumValue <
      O.value (O.globalMinimumIndex + length)

  endpointFloor :
    ∀ k : ℕ,
      0 < k →
      k < length →
      O.value (O.globalMinimumIndex + length) <
        O.value (O.globalMinimumIndex + k)

namespace FirstCrossingEndpointFloorSource

/-- source word。 -/
noncomputable def word
    {O : OddOrbit}
    (S : FirstCrossingEndpointFloorSource O) : Word :=
  O.segment O.globalMinimumIndex S.length

/-- source endpoint。 -/
noncomputable def endpoint
    {O : OddOrbit}
    (S : FirstCrossingEndpointFloorSource O) : ℕ :=
  O.value (O.globalMinimumIndex + S.length)

/-- source は actual run。 -/
theorem runs
    {O : OddOrbit}
    (S : FirstCrossingEndpointFloorSource O) :
    Runs S.word O.globalMinimumValue S.endpoint := by
  unfold word endpoint
  simpa [O.value_globalMinimumIndex] using
    O.runsSegment O.globalMinimumIndex S.length

/--
TwoThree small-gap exclusion の下で source FirstCrossing は exact q=0 canonical run。
-/
theorem source_eq_canonical
    {O : OddOrbit}
    (S : FirstCrossingEndpointFloorSource O)
    (hGap : TwoThreeSmallGapExclusion) :
    O.globalMinimumValue = Word.canonicalStart S.word ∧
      S.endpoint = Word.canonicalEnd S.word := by
  have hF : Word.FirstCrossing S.word := by
    simpa [word] using S.firstCrossing
  have hpos : O.globalMinimumValue < S.endpoint := by
    simpa [endpoint] using S.positive
  exact
    hF.actual_eq_canonical_of_twoThreeSmallGapExclusion
      hGap S.runs hpos

/--
source endpoint 以後の tail minimum まで延長し、
canonical adjacent contracting return を構成する。
-/
noncomputable def toCanonicalAdjacentContractingReturn
    {O : OddOrbit}
    (S : FirstCrossingEndpointFloorSource O)
    (hGap : TwoThreeSmallGapExclusion) :
    CanonicalAdjacentContractingReturn O := by
  classical
  let i := O.globalMinimumIndex
  let j := FutureMinimumSelection.tailMinIndex O (i + S.length)
  let d := j - (i + S.length)
  let v := O.segment (i + S.length) d
  let W := O.segment i (S.length + d)
  have hjge : i + S.length ≤ j := by
    dsimp [j]
    exact FutureMinimumSelection.tailMinIndex_ge O (i + S.length)
  have hjEq : i + S.length + d = j := by
    dsimp [d]
    omega
  have hEndIndex : i + (S.length + d) = j := by
    omega
  have hWappend :
      W = O.segment i S.length ++ v := by
    dsimp [W, v]
    exact O.segment_add i S.length d
  have hF :
      Word.FirstCrossing (O.segment i S.length) := by
    simpa [i] using S.firstCrossing
  have hrunU :
      Runs (O.segment i S.length)
        O.globalMinimumValue
        (O.value (i + S.length)) := by
    have h := O.runsSegment i S.length
    simpa [i, O.value_globalMinimumIndex] using h
  have hPosU :
      O.globalMinimumValue < O.value (i + S.length) := by
    simpa [i] using S.positive
  obtain ⟨hStartCanonicalU, _hEndCanonicalU⟩ :=
    hF.actual_eq_canonical_of_twoThreeSmallGapExclusion
      hGap hrunU hPosU
  have hjValue :
      O.value j =
        FutureMinimumSelection.tailMinValue O (i + S.length) := by
    dsimp [j]
    exact FutureMinimumSelection.value_tailMinIndex O (i + S.length)
  have hEndLeOriginal :
      O.value j ≤ O.value (i + S.length) := by
    rw [hjValue]
    exact
      FutureMinimumSelection.tailMinValue_le
        O (i + S.length) (i + S.length) le_rfl
  have hij : i < j := by
    have hip : i < i + S.length := by
      have hlen : 0 < S.length := S.length_pos
      omega
    exact lt_of_lt_of_le hip hjge
  have hPositiveFinal :
      O.globalMinimumValue < O.value j := by
    have hle :
        O.globalMinimumValue ≤ O.value j :=
      O.globalMinimumValue_le_value j
    have hne :
        O.globalMinimumValue ≠ O.value j := by
      rw [← O.value_globalMinimumIndex]
      simpa [i] using
        O.value_ne_of_lt_of_unbounded S.unbounded hij
    omega
  have hWholeContracting : Word.Contracting W := by
    by_cases hd : d = 0
    · simpa [W, hd] using hF.terminalContracting
    · have hdPos : 0 < d := Nat.pos_of_ne_zero hd
      have hVne : v ≠ [] := by
        apply List.ne_nil_of_length_pos
        simp only [segment_length, v]
        exact hdPos
      have hrunV :
          Runs v
            (O.value (i + S.length))
            (O.value j) := by
        have h := O.runsSegment (i + S.length) d
        rw [hjEq] at h
        simpa [v] using h
      have hTailStrict :
          O.value j < O.value (i + S.length) := by
        have hIndexStrict : i + S.length < j := by
          omega
        have hneValue :
            O.value j ≠ O.value (i + S.length) := by
          intro hEq
          have hinj := O.value_injective_of_unbounded S.unbounded
          have : j = i + S.length := hinj hEq
          omega
        omega
      have hVContracting : Word.Contracting v :=
        Word.Runs.contracting_of_end_lt_start hrunV hVne hTailStrict
      rw [hWappend]
      exact hF.terminalContracting.append hVContracting
  have hInterior :
      ∀ k : ℕ,
        0 < k →
        k < S.length + d →
        O.value (i + (S.length + d)) <
          O.value (i + k) := by
    intro k hkPos hkLt
    rw [hEndIndex]
    by_cases hkBefore : k < S.length
    · have hFloor :
          O.value (i + S.length) < O.value (i + k) := by
        simpa [i] using S.endpointFloor k hkPos hkBefore
      exact lt_of_le_of_lt hEndLeOriginal hFloor
    · have hpk : S.length ≤ k := Nat.le_of_not_gt hkBefore
      have hTailLe : O.value j ≤ O.value (i + k) := by
        calc
          O.value j
              = FutureMinimumSelection.tailMinValue O (i + S.length) :=
                hjValue
          _ ≤ O.value (i + k) :=
            FutureMinimumSelection.tailMinValue_le
              O (i + S.length) (i + k) (by omega)
      have hikj : i + k < j := by
        omega
      have hne : O.value j ≠ O.value (i + k) := by
        intro hEq
        have hinj := O.value_injective_of_unbounded S.unbounded
        have : j = i + k := hinj hEq
        omega
      omega
  have hEndFutureMinimum :
      O.FutureMinimumAt (i + (S.length + d)) := by
    rw [hEndIndex]
    dsimp [j]
    exact
      FutureMinimumSelection.futureMinimumAt_tailMinIndex
        O (i + S.length)
  have hrunW :
      Runs W O.globalMinimumValue (O.value j) := by
    have h := O.runsSegment i (S.length + d)
    rw [hEndIndex] at h
    simpa [W, i, O.value_globalMinimumIndex] using h
  have hWne : W ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [W]
    omega
  have hModLe :
      Word.residueModulus (O.segment i S.length) ≤
        Word.residueModulus W := by
    rw [hWappend, Word.residueModulus_append]
    have hpowPos : 0 < 2 ^ Word.twoSteps v :=
      Nat.pow_pos (by omega)
    have hpowOne : 1 ≤ 2 ^ Word.twoSteps v := by
      omega
    calc
      Word.residueModulus (O.segment i S.length)
          = Word.residueModulus (O.segment i S.length) * 1 := by ring
      _ ≤ Word.residueModulus (O.segment i S.length) *
            2 ^ Word.twoSteps v :=
        Nat.mul_le_mul_left _ hpowOne
  have hStartLtModulus :
      O.globalMinimumValue < Word.residueModulus W := by
    calc
      O.globalMinimumValue
          = Word.canonicalStart (O.segment i S.length) :=
            hStartCanonicalU
      _ < Word.residueModulus (O.segment i S.length) :=
        Word.canonicalStart_lt_modulus _
      _ ≤ Word.residueModulus W := hModLe
  have hStartCanonicalW :
      O.globalMinimumValue = Word.canonicalStart W := by
    exact
      hrunW.realizes.eq_canonicalStart_of_lt_modulus
        (hrunW.end_odd_of_ne_nil hWne)
        hStartLtModulus
  let R :
      Word.ReplayCoordinate W O.globalMinimumValue (O.value j) :=
    Word.ReplayCoordinate.ofRuns hrunW hWne
  have hqZero : R.quotient = 0 :=
    R.quotient_eq_zero_of_start_eq_canonical hStartCanonicalW
  have hEndCanonicalW :
      O.value j = Word.canonicalEnd W :=
    R.finish_eq_canonical_of_quotient_eq_zero hqZero
  exact
    { unbounded := S.unbounded
      length := S.length + d
      length_pos := by omega
      endFutureMinimum := by
        simpa [i] using hEndFutureMinimum
      interiorAboveEnd := by
        intro k hkPos hkLt
        simpa [i] using hInterior k hkPos hkLt
      contracting := by
        simpa [W, i] using hWholeContracting
      startCanonical := by
        simpa [W, i] using hStartCanonicalW
      endCanonical := by
        rw [show O.globalMinimumIndex + (S.length + d) = j by
          simpa [i] using hEndIndex]
        simpa [W, i] using hEndCanonicalW }

/-- source packet があれば canonical adjacent contracting return が存在する。 -/
theorem exists_canonicalAdjacentContractingReturn
    {O : OddOrbit}
    (S : FirstCrossingEndpointFloorSource O)
    (hGap : TwoThreeSmallGapExclusion) :
    ∃ _D : CanonicalAdjacentContractingReturn O, True := by
  classical
  exact ⟨S.toCanonicalAdjacentContractingReturn hGap, trivial⟩

end FirstCrossingEndpointFloorSource
end OddOrbit
end Collatz2
