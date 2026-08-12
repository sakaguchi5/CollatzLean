import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.NaturalZeroReplaySmallestFirst
import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.BidirectionalStrengthening
import CollatzLean.Collatz.Canonical.PrependOneCorePositiveElimination
import CollatzLean.Collatz.Word.SuffixGapBudgetLower
import CollatzLean.Collatz.FiniteOrbit.Determinism

/-!
# natural j=0 packet から endpoint-floor zero packet へ

今回の strong-induction bridge を actual orbit 上の位置を失わない形へ強化する。

natural predecessor 内の

* actual positive return
* all-suffix-contracting

を同時に満たす部分区間を長さ最小で選ぶ。
その最小性から

* 区間全体が FirstCrossing
* 全 proper interior boundary が terminal endpoint より真に上

を同時に得る。

さらに Ellison 型 effective gap を使うと、その最小区間の actual replay quotient は0。
したがって actual start/end は canonical start/end と一致し、
純有限語 `EndpointFloorZeroPacket` へ落ちる。
-/

namespace Collatz

namespace Word

/--
smallest-first obstruction の exact return witness `n` は `6*n < p` を満たす。
Baker bound は不要で、all-suffix sharp affine bound だけを使う。
-/
theorem SmallestFirstParadoxicalExactObstruction.six_mul_returnHalf_lt_oddSteps
    {w : Collatz.Word}
    (P : SmallestFirstParadoxicalExactObstruction w)
    {n : ℕ}
    (_hn : 0 < n)
    (_hreturn :
      w.canonicalEnd = w.canonicalStart + 2 * n)
    (hexact :
      w.affineConst =
        w.contractingGap * w.canonicalStart +
          2 ^ (w.twoSteps + 1) * n) :
    6 * n < w.oddSteps := by
  have hAffine :
      3 * w.affineConst <
        w.oddSteps * 2 ^ w.twoSteps :=
    Word.AllSuffixesContracting.three_mul_affineConst_lt_oddSteps
      P.firstCrossing.nonempty P.allSuffixesContracting
  have hAffine' := hAffine
  rw [hexact, pow_succ] at hAffine'
  have hPowPos : 0 < 2 ^ w.twoSteps :=
    Nat.pow_pos (by omega)
  have hNonneg :
      0 ≤ 3 * w.contractingGap * w.canonicalStart :=
    Nat.zero_le _
  have hScaled :
      (6 * n) * 2 ^ w.twoSteps <
        w.oddSteps * 2 ^ w.twoSteps := by
    nlinarith [hAffine', hNonneg]
  exact
    (Nat.mul_lt_mul_right hPowPos).1
      (by simpa [Nat.mul_assoc] using hScaled)

/--
smallest-first obstruction を actual に positive replay したものは、
Ellison 型 effective gap のもとでは replay quotient 0 でなければならない。

`q>0` なら actual positive gap は
`2*n - 2*contractingGap*q` だけになり、
`6*n < p <= contractingGap` と衝突する。
-/
theorem SmallestFirstParadoxicalExactObstruction.replayQuotient_eq_zero_of_runs_positive
    (hGap : External.TwoThreeEffectiveGapInput)
    {w : Collatz.Word} {x y : ℕ}
    (P : SmallestFirstParadoxicalExactObstruction w)
    (hrun : Runs w x y)
    (hxy : x < y) :
    (ReplayCoordinate.ofRuns hrun P.firstCrossing.nonempty).quotient = 0 := by
  let Q : ReplayCoordinate w x y :=
    ReplayCoordinate.ofRuns hrun P.firstCrossing.nonempty
  rcases P.exactReturn with ⟨n, hn, hreturn, hexact⟩
  have hSix : 6 * n < w.oddSteps :=
    P.six_mul_returnHalf_lt_oddSteps hn hreturn hexact
  have hContract :
      3 ^ w.oddSteps < 2 ^ w.twoSteps := by
    simpa [Word.Contracting] using
      P.firstCrossing.terminalContracting
  have hGapLower :
      w.oddSteps ≤ w.contractingGap := by
    simpa [Word.contractingGap] using
      External.twoThreeGap_ge_exponent hGap hContract
  by_contra hq0
  have hqPos : 0 < Q.quotient := Nat.pos_of_ne_zero hq0
  have hqOne : 1 ≤ Q.quotient := by omega
  have hGapEq :
      3 ^ w.oddSteps + w.contractingGap =
        2 ^ w.twoSteps := by
    unfold Word.contractingGap
    exact Nat.add_sub_of_le (Nat.le_of_lt hContract)
  have hxy' :
      w.canonicalStart +
          w.residueModulus * Q.quotient <
        w.canonicalEnd +
          2 * 3 ^ w.oddSteps * Q.quotient := by
    calc
      w.canonicalStart +
            w.residueModulus * Q.quotient
          = x := Q.start_eq.symm
      _ < y := hxy
      _ =
          w.canonicalEnd +
            2 * 3 ^ w.oddSteps * Q.quotient :=
        Q.finish_eq
  have hPosRewritten :
      w.canonicalStart +
          2 ^ (w.twoSteps + 1) * Q.quotient <
        w.canonicalStart + 2 * n +
          2 * 3 ^ w.oddSteps * Q.quotient := by
    rw [hreturn] at hxy'
    simpa [Word.residueModulus] using hxy'
  have hGapMul :
      2 ^ w.twoSteps * Q.quotient =
        3 ^ w.oddSteps * Q.quotient +
          w.contractingGap * Q.quotient := by
    calc
      2 ^ w.twoSteps * Q.quotient
          = (3 ^ w.oddSteps + w.contractingGap) * Q.quotient := by
              rw [hGapEq]
      _ = 3 ^ w.oddSteps * Q.quotient +
            w.contractingGap * Q.quotient := by ring
  have hPosScaled :
      2 * (2 ^ w.twoSteps * Q.quotient) <
        2 * n + 2 * (3 ^ w.oddSteps * Q.quotient) := by
    rw [pow_succ] at hPosRewritten
    nlinarith [hPosRewritten]
  have hSmall :
      w.contractingGap * Q.quotient < n := by
    rw [hGapMul] at hPosScaled
    nlinarith [hPosScaled]
  have hGapLeMul :
      w.contractingGap ≤
        w.contractingGap * Q.quotient := by
    have h := Nat.mul_le_mul_left w.contractingGap hqOne
    simpa using h
  omega

end Word

namespace AdjacentReturn
namespace PositiveReturn
namespace FirstCrossingData.NaturalZeroReplaySignChangeData

/-- segment の先頭 `k` 文字。 -/
private theorem segment_take_of_le
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

/-- segment を `k` 文字 drop すると対応する後半 segment。 -/
private theorem segment_drop_of_le
    (O : OddOrbit) {i m k : ℕ}
    (hk : k ≤ m) :
    (O.segment i m).drop k =
      O.segment (i + k) (m - k) := by
  induction k generalizing i m with
  | zero => simp
  | succ k ih =>
      cases m with
      | zero => omega
      | succ m =>
          have hk' : k ≤ m := by omega
          simp only [OddOrbit.segment_succ, List.drop_succ_cons]
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using
            ih (i := i + 1) (m := m) hk'

/--
natural predecessor 内の actual-positive / all-suffix-contracting 部分区間。
-/
structure PositiveSubsegmentCandidate
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) where
  startCut : ℕ
  endCut : ℕ
  pred_le_start : D.pred ≤ startCut
  start_lt_end : startCut < endCut
  end_le_terminal : endCut ≤ F.length
  allSuffixesContracting :
    Word.AllSuffixesContracting
      (O.segment
        (R.startIndex + startCut)
        (endCut - startCut))
  positive :
    O.value (R.startIndex + startCut) <
      O.value (R.startIndex + endCut)

namespace PositiveSubsegmentCandidate

/-- candidate の長さ。 -/
def length
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D) : ℕ :=
  C.endCut - C.startCut

/-- candidate の actual word。 -/
def word
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D) : Collatz.Word :=
  O.segment (R.startIndex + C.startCut) C.length

@[simp] theorem word_length
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D) :
    C.word.length = C.length := by
  simp [word]

/-- candidate の終端は startCut + length。 -/
theorem endCut_eq_startCut_add_length
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D) :
    C.endCut = C.startCut + C.length := by
  have hlt : C.startCut < C.endCut :=
    C.start_lt_end
  dsimp [length]
  omega

/-- candidate length は正。 -/
theorem length_pos
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D) :
    0 < C.length := by
  dsimp [length]
  exact Nat.sub_pos_of_lt C.start_lt_end

/-- candidate word は非空。 -/
theorem word_nonempty
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D) :
    C.word ≠ [] := by
  apply List.ne_nil_of_length_pos
  rw [C.word_length]
  exact C.length_pos

/-- candidate は actual run。 -/
theorem runs
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D) :
    Word.Runs C.word
      (O.value (R.startIndex + C.startCut))
      (O.value (R.startIndex + C.endCut)) := by
  have hrun :=
    O.runsSegment
      (R.startIndex + C.startCut) C.length
  have hend :
      (R.startIndex + C.startCut) + C.length =
        R.startIndex + C.endCut := by
    have hcut : C.startCut < C.endCut :=
      C.start_lt_end
    dsimp [length]
    omega
  simpa [word, hend] using hrun

/-- candidate は valid。 -/
theorem valid
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D) :
    Word.Valid C.word :=
  C.runs.valid

/-- candidate は contracting。 -/
theorem contracting
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D) :
    Word.Contracting C.word := by
  exact
    Word.AllSuffixesContracting.whole
      C.word_nonempty
      (by simpa [word, length] using C.allSuffixesContracting)

end PositiveSubsegmentCandidate

/-- natural predecessor 自身が candidate を与える。 -/
def initialPositiveSubsegmentCandidate
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    PositiveSubsegmentCandidate D := by
  refine {
    startCut := D.pred
    endCut := F.length
    pred_le_start := le_rfl
    start_lt_end := ?_
    end_le_terminal := le_rfl
    allSuffixesContracting := ?_
    positive := ?_
  }
  · have hpredCut : D.pred < D.cut := by
      rw [← D.pred_succ]
      exact Nat.lt_succ_self D.pred
    exact lt_trans hpredCut D.cut_lt
  · simpa [
      PositiveSubsegmentCandidate.length,
      PositiveSubsegmentCandidate.word,
      FirstCrossingData.NaturalZeroReplaySignChangeData.predecessorWord,
      FirstCrossingData.suffixWord
    ] using D.predecessor_allSuffixesContracting
  · simpa [
      FirstCrossingData.boundaryValue,
      FirstCrossingData.endpointValue
    ] using D.pred_boundary_lt_endpoint

/-- candidate length は少なくとも一つ存在する。 -/
theorem exists_positiveSubsegmentCandidate_length
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    ∃ m : ℕ,
      ∃ C : PositiveSubsegmentCandidate D,
        C.length = m := by
  let C := D.initialPositiveSubsegmentCandidate
  exact ⟨C.length, C, rfl⟩

/-- 最短 candidate 長。 -/
noncomputable def minimalPositiveLength
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) : ℕ := by
  classical
  exact Nat.find D.exists_positiveSubsegmentCandidate_length

/-- 最短 candidate。 -/
noncomputable def minimalPositiveCandidate
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    PositiveSubsegmentCandidate D := by
  classical
  exact Classical.choose
    (Nat.find_spec D.exists_positiveSubsegmentCandidate_length)

/-- 最短 candidate の length は `minimalPositiveLength`。 -/
theorem minimalPositiveCandidate_length
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    D.minimalPositiveCandidate.length = D.minimalPositiveLength := by
  classical
  simpa [minimalPositiveCandidate, minimalPositiveLength] using
    (Classical.choose_spec
      (Nat.find_spec D.exists_positiveSubsegmentCandidate_length))

/-- 最短 candidate は任意の candidate 以下の長さ。 -/
theorem minimalPositiveLength_le
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    (C : PositiveSubsegmentCandidate D) :
    D.minimalPositiveLength ≤ C.length := by
  classical
  simpa [minimalPositiveLength] using
    (Nat.find_min'
      D.exists_positiveSubsegmentCandidate_length
      ⟨C, rfl⟩)

namespace PositiveSubsegmentCandidate

/--
candidate word の先頭 `p` 文字が FirstCrossing なら `p > 0`。
-/
theorem firstCrossing_take_length_pos
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D)
    {p : ℕ}
    (hFirst : Word.FirstCrossing (C.word.take p)) :
    0 < p := by
  have hne : C.word.take p ≠ [] :=
    hFirst.nonempty
  by_contra hp
  have hp0 : p = 0 := by
    omega
  subst p
  simp at hne

/--
candidate の FirstCrossing prefix が actual-positive なら、
その prefix 自身が長さ `p` の candidate を与える。
-/
theorem exists_prefix_candidate_of_firstCrossing_positive
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D)
    {p : ℕ}
    (hpPos : 0 < p)
    (hpLe : p ≤ C.length)
    (hFirst : Word.FirstCrossing (C.word.take p))
    (hPrefixPositive :
      O.value (R.startIndex + C.startCut) <
        O.value (R.startIndex + (C.startCut + p))) :
    ∃ P : PositiveSubsegmentCandidate D,
      P.length = p := by
  let middleCut := C.startCut + p
  let P : PositiveSubsegmentCandidate D := {
    startCut := C.startCut
    endCut := middleCut
    pred_le_start := C.pred_le_start
    start_lt_end := by
      dsimp [middleCut]
      omega
    end_le_terminal := by
      have hendEq :
          C.endCut = C.startCut + C.length :=
        C.endCut_eq_startCut_add_length
      have hterminal :
          C.endCut ≤ F.length :=
        C.end_le_terminal
      dsimp [middleCut]
      omega
    allSuffixesContracting := by
      have hAll :=
        hFirst.allSuffixesContracting
      have htake :=
        segment_take_of_le O
          (i := R.startIndex + C.startCut)
          (m := C.length)
          (k := p) hpLe
      have hwordTake :
          C.word.take p =
            O.segment
              (R.startIndex + C.startCut) p := by
        dsimp [PositiveSubsegmentCandidate.word]
        exact htake
      rw [hwordTake] at hAll
      have hlen :
          middleCut - C.startCut = p := by
        dsimp [middleCut]
        omega
      rw [hlen]
      exact hAll
    positive := by
      simpa [middleCut] using hPrefixPositive
  }
  refine ⟨P, ?_⟩
  dsimp [
    P,
    PositiveSubsegmentCandidate.length,
    middleCut
  ]
  omega

/--
candidate 内の位置 `p` の値が candidate start 以下なら、
位置 `p` から terminal までの suffix が shorter positive candidate を与える。
-/
theorem exists_suffix_candidate_of_middle_le_start
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D)
    {p : ℕ}
    (hpLt : p < C.length)
    (hMiddleLe :
      O.value (R.startIndex + (C.startCut + p)) ≤
        O.value (R.startIndex + C.startCut)) :
    ∃ S : PositiveSubsegmentCandidate D,
      S.length = C.length - p := by
  let middleCut := C.startCut + p
  have hpLe : p ≤ C.length :=
    Nat.le_of_lt hpLt
  have hendEq :
      C.endCut = C.startCut + C.length :=
    C.endCut_eq_startCut_add_length
  let S : PositiveSubsegmentCandidate D := {
    startCut := middleCut
    endCut := C.endCut
    pred_le_start := by
      have hpred :
          D.pred ≤ C.startCut :=
        C.pred_le_start
      dsimp [middleCut]
      omega
    start_lt_end := by
      dsimp [middleCut]
      omega
    end_le_terminal := C.end_le_terminal
    allSuffixesContracting := by
      have hAllBase :
          Word.AllSuffixesContracting
            (O.segment
              (R.startIndex + C.startCut)
              C.length) := by
        simpa [PositiveSubsegmentCandidate.length] using
          C.allSuffixesContracting
      have hAll0 :=
        hAllBase.drop p
      have hdrop :=
        segment_drop_of_le O
          (i := R.startIndex + C.startCut)
          (m := C.length)
          (k := p) hpLe
      rw [hdrop] at hAll0
      have hindex :
          (R.startIndex + C.startCut) + p =
            R.startIndex + middleCut := by
        dsimp [middleCut]
        omega
      have hlen :
          C.length - p =
            C.endCut - middleCut := by
        dsimp [middleCut]
        omega
      rw [hindex, hlen] at hAll0
      exact hAll0
    positive := by
      have hCEnd :
          O.value (R.startIndex + C.startCut) <
            O.value (R.startIndex + C.endCut) :=
        C.positive
      simpa [middleCut] using
        (lt_of_le_of_lt hMiddleLe hCEnd)
  }
  refine ⟨S, ?_⟩
  dsimp [
    S,
    PositiveSubsegmentCandidate.length,
    middleCut
  ]
  rw [hendEq]
  omega


/--
candidate の interior boundary から terminal endpoint までが
actual-positive なら、その suffix 自身が candidate を与える。
-/
theorem exists_terminalSuffixCandidate_of_value_lt_endpoint
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D)
    {k : ℕ}
    (hkLt : k < C.length)
    (hPositive :
      O.value (R.startIndex + (C.startCut + k)) <
        O.value (R.startIndex + (C.startCut + C.length))) :
    ∃ S : PositiveSubsegmentCandidate D,
      S.length = C.length - k := by
  have hkLe : k ≤ C.length :=
    Nat.le_of_lt hkLt
  have hendEq :
      C.endCut = C.startCut + C.length :=
    C.endCut_eq_startCut_add_length
  let S : PositiveSubsegmentCandidate D := {
    startCut := C.startCut + k
    endCut := C.endCut
    pred_le_start := by
      have hpred :
          D.pred ≤ C.startCut :=
        C.pred_le_start
      omega
    start_lt_end := by
      rw [hendEq]
      omega
    end_le_terminal := C.end_le_terminal
    allSuffixesContracting := by
      have hAllBase :
          Word.AllSuffixesContracting
            (O.segment
              (R.startIndex + C.startCut)
              C.length) := by
        simpa [PositiveSubsegmentCandidate.length] using
          C.allSuffixesContracting
      have hAll0 :=
        hAllBase.drop k
      have hdrop :=
        segment_drop_of_le O
          (i := R.startIndex + C.startCut)
          (m := C.length)
          (k := k) hkLe
      rw [hdrop] at hAll0
      have hindex :
          (R.startIndex + C.startCut) + k =
            R.startIndex + (C.startCut + k) := by
        omega
      have hlen :
          C.length - k =
            C.endCut - (C.startCut + k) := by
        rw [hendEq]
        omega
      rw [hindex, hlen] at hAll0
      exact hAll0
    positive := by
      rw [hendEq]
      simpa [Nat.add_assoc] using hPositive
  }
  refine ⟨S, ?_⟩
  dsimp [
    S,
    PositiveSubsegmentCandidate.length
  ]
  rw [hendEq]
  omega

/--
長さ最小の candidate に FirstCrossing prefix があるなら、
その FirstCrossing は candidate 全体でなければならない。
-/
theorem firstCrossing_take_length_eq_of_minimal
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    {D : NaturalZeroReplaySignChangeData F}
    (C : PositiveSubsegmentCandidate D)
    (hMinimal :
      C.length = D.minimalPositiveLength)
    {p : ℕ}
    (hpLe : p ≤ C.length)
    (hFirst : Word.FirstCrossing (C.word.take p)) :
    p = C.length := by
  have hpPos : 0 < p :=
    C.firstCrossing_take_length_pos hFirst
  by_contra hpNe
  have hpLt : p < C.length := by
    omega
  by_cases hPrefixPositive :
      O.value (R.startIndex + C.startCut) <
        O.value
          (R.startIndex + (C.startCut + p))
  · obtain ⟨P, hPLen⟩ :=
      C.exists_prefix_candidate_of_firstCrossing_positive
        hpPos hpLe hFirst hPrefixPositive
    have hmin :=
      D.minimalPositiveLength_le P
    rw [← hMinimal, hPLen] at hmin
    omega
  · have hMiddleLe :
        O.value
            (R.startIndex + (C.startCut + p)) ≤
          O.value
            (R.startIndex + C.startCut) :=
      Nat.le_of_not_gt hPrefixPositive
    obtain ⟨S, hSLen⟩ :=
      C.exists_suffix_candidate_of_middle_le_start
        hpLt hMiddleLe
    have hmin :=
      D.minimalPositiveLength_le S
    rw [← hMinimal, hSLen] at hmin
    omega

end PositiveSubsegmentCandidate

/-- 最短 candidate 自身が FirstCrossing。 -/
theorem minimalPositiveCandidate_firstCrossing
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F) :
    Word.FirstCrossing
      D.minimalPositiveCandidate.word := by
  classical
  let C := D.minimalPositiveCandidate
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
      C.length = D.minimalPositiveLength := by
    simpa [C] using
      D.minimalPositiveCandidate_length
  have hpEq : p = C.length :=
    C.firstCrossing_take_length_eq_of_minimal
      hMinimal hpLe hFirstRaw
  have hpEqWord : p = C.word.length := by
    rw [C.word_length]
    exact hpEq
  rw [hpEqWord] at hFirstRaw
  have hCFirst : Word.FirstCrossing C.word := by
    simpa only [List.take_length] using hFirstRaw
  simpa only [C] using hCFirst

/--
最短 candidate の proper interior boundary から
terminal endpoint への actual-positive suffix は存在しない。
存在すれば、より短い positive candidate が得られる。
-/
theorem minimalPositiveCandidate_not_interior_below_endpoint
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < D.minimalPositiveCandidate.length) :
    ¬
      O.value
          (R.startIndex +
            (D.minimalPositiveCandidate.startCut + k)) <
        O.value
          (R.startIndex +
            (D.minimalPositiveCandidate.startCut +
              D.minimalPositiveCandidate.length)) := by
  intro hPositive
  obtain ⟨S, hSLen⟩ :=
    PositiveSubsegmentCandidate.exists_terminalSuffixCandidate_of_value_lt_endpoint
      (C := D.minimalPositiveCandidate)
      hkLt
      hPositive
  have hmin :=
    D.minimalPositiveLength_le S
  have hCmin :
      D.minimalPositiveCandidate.length =
        D.minimalPositiveLength :=
    D.minimalPositiveCandidate_length
  have hLower :
      D.minimalPositiveCandidate.length ≤ S.length := by
    rw [hCmin]
    exact hmin
  rw [hSLen] at hLower
  omega

/--
最短 candidate の proper interior boundary と terminal endpoint は
actual orbit 上で同じ値にはならない。
unbounded orbit の injectivity により index まで一致してしまうため。
-/
theorem minimalPositiveCandidate_interior_value_ne_endpoint
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hkLt : k < D.minimalPositiveCandidate.length) :
    O.value
        (R.startIndex +
          (D.minimalPositiveCandidate.startCut + k)) ≠
      O.value
        (R.startIndex +
          (D.minimalPositiveCandidate.startCut +
            D.minimalPositiveCandidate.length)) := by
  intro hvalue
  have hindex :=
    (O.value_injective_of_unbounded R.unbounded) hvalue
  omega

/--
最短 candidate の全 proper interior boundary は
terminal endpoint より真に上。
-/
theorem minimalPositiveCandidate_endpointFloor_actual
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < D.minimalPositiveCandidate.length) :
    O.value
        (R.startIndex +
          (D.minimalPositiveCandidate.startCut +
            D.minimalPositiveCandidate.length)) <
      O.value
        (R.startIndex +
          (D.minimalPositiveCandidate.startCut + k)) := by
  have hnotBelow :=
    D.minimalPositiveCandidate_not_interior_below_endpoint
      hkPos hkLt
  have hne :=
    D.minimalPositiveCandidate_interior_value_ne_endpoint
      hkLt
  omega

end FirstCrossingData.NaturalZeroReplaySignChangeData

namespace EndpointFloorZero

/--
最短 source-preserving candidate から得る pure finite-word zero packet。

`endpointFloor` は canonical run の全 proper interior boundary が
terminal canonical endpoint より真に大きいことを保持する。
-/
structure Packet (v : Collatz.Word) (boundary : ℕ) : Prop where
  tail_nonempty : v ≠ []
  replay : Word.PrependOneReplayData v boundary 0
  paradoxical :
    Word.SmallestFirstParadoxicalExactObstruction (1 :: v)
  endpointFloor :
    ∀ (m y : ℕ),
      0 < m →
      m < (1 :: v).length →
      Word.Runs
        ((1 :: v).take m)
        (Word.canonicalStart (1 :: v))
        y →
      Word.canonicalEnd (1 :: v) < y

/-- zero packet は CORE を必ず破る。 -/
theorem Packet.coreFailure
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary) :
    ¬ Word.PrependOneCoreCondition v 0 := by
  intro hCore
  have hdesc :=
    Word.canonicalEnd_le_canonicalStart_of_prependOneCore
      P.paradoxical.firstCrossing.terminalContracting
      P.replay
      hCore
  exact (Nat.not_le_of_gt P.paradoxical.positiveReturn) hdesc

/-- tail は valid。 -/
theorem Packet.tail_valid
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary) :
    Word.Valid v := by
  intro e he
  exact P.paradoxical.valid e (by simp [he])

/-- tail は all-suffix-contracting。 -/
theorem Packet.tail_allSuffixesContracting
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary) :
    Word.AllSuffixesContracting v := by
  have hAll := P.paradoxical.allSuffixesContracting
  change
    Word.Contracting (1 :: v) ∧
      Word.AllSuffixesContracting v at hAll
  exact hAll.2

/-- tail 自身は contracting。 -/
theorem Packet.tail_contracting
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary) :
    Word.Contracting v :=
  P.tail_allSuffixesContracting.whole P.tail_nonempty

/-- whole canonical run の最初の一歩。 -/
theorem Packet.headRuns
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary) :
    Word.Runs ([1] : Collatz.Word)
      (Word.canonicalStart (1 :: v)) boundary := by
  have hrun :
      Word.Runs (1 :: v)
        (Word.canonicalStart (1 :: v))
        (Word.canonicalEnd (1 :: v)) :=
    P.paradoxical.valid.canonicalRuns
  have hdecomp : (1 :: v) = ([1] : Collatz.Word) ++ v := by
    simp
  rw [hdecomp] at hrun
  obtain ⟨y, hhead, _htail⟩ := hrun.split_append
  have hreal := hhead.realizes
  have hstep :
      2 * y = 3 * Word.canonicalStart (1 :: v) + 1 := by
    simpa [
      Word.Realizes,
      Word.twoSteps,
      Word.oddSteps,
      Word.affineConst
    ] using hreal
  have hy : y = boundary := by
    have hReplay := P.replay.headStep
    omega
  simpa [hy] using hhead

/-- whole endpoint は tail endpoint。 -/
theorem Packet.fullEnd_eq_tailEnd
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary) :
    Word.canonicalEnd (1 :: v) = Word.canonicalEnd v :=
  P.replay.zero_fullEnd_eq_suffixEnd

/-- first boundary は tail canonical start。 -/
theorem Packet.boundary_eq_tailStart
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary) :
    boundary = Word.canonicalStart v :=
  P.replay.zero_boundary_eq_canonicalStart

/-- endpoint floor を最初の一歩へ適用して `T < s`。 -/
theorem Packet.fullEnd_lt_tailStart
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary) :
    Word.canonicalEnd (1 :: v) < Word.canonicalStart v := by
  have hlen : 1 < (1 :: v).length := by
    have hv : 0 < v.length := List.length_pos_of_ne_nil P.tail_nonempty
    simpa using hv
  have hfloor :=
    P.endpointFloor 1 boundary (by omega) hlen (by
      simpa using P.headRuns)
  rw [P.boundary_eq_tailStart] at hfloor
  exact hfloor

/-- zero packet の三 canonical value は `S < T < s`。 -/
theorem Packet.start_end_tailStart_order
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary) :
    Word.canonicalStart (1 :: v) <
      Word.canonicalEnd (1 :: v) ∧
    Word.canonicalEnd (1 :: v) <
      Word.canonicalStart v :=
  ⟨P.paradoxical.positiveReturn, P.fullEnd_lt_tailStart⟩

/--
zero packet の natural 型 coordinate。
`n` は positive return half-gap、`d` は tail descent half-gap。
-/
structure CoordinateData
    (v : Collatz.Word) (n d : ℕ) : Prop where
  n_pos : 0 < n
  d_pos : 0 < d
  positiveGap :
    Word.canonicalEnd (1 :: v) =
      Word.canonicalStart (1 :: v) + 2 * n
  descentGap :
    Word.canonicalStart v =
      Word.canonicalEnd v + 2 * d
  fullStart_add_one :
    Word.canonicalStart (1 :: v) + 1 = 4 * (n + d)
  tailStart_add_one :
    Word.canonicalStart v + 1 = 6 * (n + d)
  endpoint_add_one :
    Word.canonicalEnd v + 1 = 6 * n + 4 * d
  exactReturn :
    Word.affineConst (1 :: v) =
      Word.contractingGap (1 :: v) *
          Word.canonicalStart (1 :: v) +
        2 ^ (Word.twoSteps (1 :: v) + 1) * n

/-- endpoint-floor zero packet から natural 型 `n,d` を再構成する。 -/
theorem Packet.exists_coordinateData
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary) :
    ∃ n d : ℕ, CoordinateData v n d := by
  rcases P.paradoxical.exactReturn with
    ⟨n, hn, hreturn, hexact⟩
  have hTltS := P.fullEnd_lt_tailStart
  have hTailEnd := P.fullEnd_eq_tailEnd
  have hTailValid := P.tail_valid
  have hTailStartOdd : Odd (Word.canonicalStart v) := by
    exact
      hTailValid.canonicalRuns.start_odd
        (Word.canonicalEnd_odd v)
  have hTailEndOdd : Odd (Word.canonicalEnd v) :=
    Word.canonicalEnd_odd v
  rcases hTailEndOdd with ⟨a, ha⟩
  rcases hTailStartOdd with ⟨b, hb⟩
  have hab : a < b := by
    rw [hTailEnd] at hTltS
    rw [ha, hb] at hTltS
    omega
  let d := b - a
  have hd : 0 < d := by
    dsimp [d]
    omega
  have hdescent :
      Word.canonicalStart v =
        Word.canonicalEnd v + 2 * d := by
    rw [ha, hb]
    dsimp [d]
    omega
  have hboundary := P.boundary_eq_tailStart
  have hhead := P.replay.headStep
  rw [hboundary] at hhead
  have hS :
      Word.canonicalStart (1 :: v) + 1 =
        4 * (n + d) := by
    rw [hTailEnd] at hreturn
    omega
  have hs :
      Word.canonicalStart v + 1 =
        6 * (n + d) := by
    omega
  have ht :
      Word.canonicalEnd v + 1 =
        6 * n + 4 * d := by
    omega
  exact
    ⟨n, d,
      {
        n_pos := hn
        d_pos := hd
        positiveGap := hreturn
        descentGap := hdescent
        fullStart_add_one := hS
        tailStart_add_one := hs
        endpoint_add_one := ht
        exactReturn := hexact
      }⟩

/--
whole-word exact suffix-gap budget から `6*n+2 <= tailLength`。
natural packet の旧定理を endpoint-floor packet 上へ再構成する。
-/
theorem CoordinateData.six_mul_n_add_two_le_tailLength
    {v : Collatz.Word} {boundary n d : ℕ}
    (P : Packet v boundary)
    (A : CoordinateData v n d) :
    6 * n + 2 ≤ Word.oddSteps v := by
  let w : Collatz.Word := 1 :: v
  have hAll : Word.AllSuffixesContracting w :=
    P.paradoxical.allSuffixesContracting
  have hAffine :
      3 * Word.affineConst w <
        Word.oddSteps w * 2 ^ Word.twoSteps w :=
    Word.AllSuffixesContracting.three_mul_affineConst_lt_oddSteps
      P.paradoxical.firstCrossing.nonempty hAll
  have hAffine' := hAffine
  have hExact := A.exactReturn
  change
    Word.affineConst w =
      Word.contractingGap w * Word.canonicalStart w +
        2 ^ (Word.twoSteps w + 1) * n at hExact
  rw [hExact, pow_succ] at hAffine'
  have hPowPos : 0 < 2 ^ Word.twoSteps w :=
    Nat.pow_pos (by omega)
  have hNonneg :
      0 ≤ 3 * Word.contractingGap w * Word.canonicalStart w :=
    Nat.zero_le _
  have hSixScaled :
      (6 * n) * 2 ^ Word.twoSteps w <
        Word.oddSteps w * 2 ^ Word.twoSteps w := by
    nlinarith [hAffine', hNonneg]
  have hSix : 6 * n < Word.oddSteps w :=
    (Nat.mul_lt_mul_right hPowPos).1
      (by simpa [Nat.mul_assoc] using hSixScaled)
  have hlen7 : 7 ≤ Word.oddSteps w := by
    have hn := A.n_pos
    omega
  have hBudgetLower :
      2 * 2 ^ Word.twoSteps w <
        Word.suffixGapBudget w := by
    exact
      hAll.two_mul_twoPow_lt_suffixGapBudget_of_seven_le_length
        (by simpa [Word.oddSteps] using hlen7)
  have hBudgetEq :=
    Word.AllSuffixesContracting.oddSteps_mul_twoPow_eq_three_mul_affine_add_suffixGapBudget
      hAll
  have hTargetScaled :
      (6 * n + 2) * 2 ^ Word.twoSteps w <
        Word.oddSteps w * 2 ^ Word.twoSteps w := by
    calc
      (6 * n + 2) * 2 ^ Word.twoSteps w
          = 6 * n * 2 ^ Word.twoSteps w +
              2 * 2 ^ Word.twoSteps w := by ring
      _ < 6 * n * 2 ^ Word.twoSteps w +
              Word.suffixGapBudget w :=
            Nat.add_lt_add_left hBudgetLower _
      _ ≤ 3 * Word.contractingGap w * Word.canonicalStart w +
              6 * n * 2 ^ Word.twoSteps w +
              Word.suffixGapBudget w := by
            omega
      _ = 3 * Word.affineConst w + Word.suffixGapBudget w := by
            rw [hExact, pow_succ]
            ring
      _ = Word.oddSteps w * 2 ^ Word.twoSteps w := hBudgetEq.symm
  have hCoeff : 6 * n + 2 < Word.oddSteps w :=
    (Nat.mul_lt_mul_right hPowPos).1
      (by simpa [Nat.mul_assoc] using hTargetScaled)
  simp only [w, Word.oddSteps_cons] at hCoeff
  omega

/-- tail の最初の指数は 1 または2。 -/
theorem Packet.tail_head_eq_one_or_two
    {v : Collatz.Word} {boundary n d : ℕ}
    (P : Packet v boundary)
    (A : CoordinateData v n d) :
    ∃ e : ℕ, ∃ u : Collatz.Word,
      v = e :: u ∧ (e = 1 ∨ e = 2) := by
  cases v with
  | nil =>
      exact False.elim (P.tail_nonempty rfl)
  | cons e u =>
      have hlen := A.six_mul_n_add_two_le_tailLength P
      have hn := A.n_pos
      have htailLen : 6 * n + 2 ≤ (e :: u).length := by
        simpa [Word.oddSteps] using hlen
      have hTwoLeTail : 2 ≤ (e :: u).length := by
        have hTwoLe : 2 ≤ 6 * n + 2 := by
          exact Nat.le_add_left 2 (6 * n)
        exact le_trans hTwoLe htailLen
      have hwholeLen : 2 < (1 :: e :: u).length := by
        change 2 < (e :: u).length + 1
        exact Nat.lt_succ_of_le hTwoLeTail
      have hExp :=
        P.paradoxical.firstCrossing.properExpanding
          2 (by omega) hwholeLen
      have hpow : 2 ^ (1 + e) < 9 := by
        simpa [
          Word.Expanding,
          Word.twoSteps,
          Word.oddSteps
        ] using hExp
      have hePos : 0 < e :=
        P.paradoxical.valid e (by simp)
      have heLe : e ≤ 2 := by
        by_contra hnot
        have he3 : 3 ≤ e := by omega
        have hmono : 2 ^ (1 + 3) ≤ 2 ^ (1 + e) :=
          Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)
        norm_num at hmono
        omega
      refine ⟨e, u, rfl, ?_⟩
      omega

/--
contracting word が actual に `x > T` から `T` へ走るなら、
その affine constant は contracting center の strict 側にある。
-/
theorem strictCenter_of_contracting_descent
    {u : Collatz.Word} {x T : ℕ}
    (hrun : Word.Runs u x T)
    (hC : Word.Contracting u)
    (hdesc : T < x) :
    Word.affineConst u <
      Word.contractingGap u * T := by
  have hreal :=
    hrun.realizes
  have hGapEq :
      3 ^ Word.oddSteps u +
          Word.contractingGap u =
        2 ^ Word.twoSteps u := by
    unfold Word.contractingGap
    exact Nat.add_sub_of_le (Nat.le_of_lt hC)
  have hThreePos :
      0 < 3 ^ Word.oddSteps u :=
    Nat.pow_pos (by omega)
  have hscaled :
      3 ^ Word.oddSteps u * T <
        3 ^ Word.oddSteps u * x :=
    (Nat.mul_lt_mul_left hThreePos).2 hdesc
  have hreal' :
      2 ^ Word.twoSteps u * T =
        3 ^ Word.oddSteps u * x +
          Word.affineConst u := by
    simpa [Word.Realizes] using hreal
  have hsum :
      3 ^ Word.oddSteps u * T +
          Word.affineConst u <
        3 ^ Word.oddSteps u * T +
          Word.contractingGap u * T := by
    calc
      3 ^ Word.oddSteps u * T +
            Word.affineConst u
          <
        3 ^ Word.oddSteps u * x +
            Word.affineConst u :=
        Nat.add_lt_add_right hscaled _
      _ =
          2 ^ Word.twoSteps u * T :=
        hreal'.symm
      _ =
          (3 ^ Word.oddSteps u +
            Word.contractingGap u) * T := by
        rw [hGapEq]
      _ =
          3 ^ Word.oddSteps u * T +
            Word.contractingGap u * T := by
        ring
  exact Nat.lt_of_add_lt_add_left hsum

/--
endpoint floor により、末尾 `r` 文字は
terminal より真に大きい actual start から terminal へ走る。
-/
theorem Packet.exists_tailSuffix_runs_from_above
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ v.length) :
    ∃ x : ℕ,
      Word.canonicalEnd (1 :: v) < x ∧
        Word.Runs
          (v.drop (v.length - r))
          x
          (Word.canonicalEnd (1 :: v)) := by
  let s : ℕ := v.length - r
  let w : Collatz.Word := 1 :: v
  let k : ℕ := s + 1
  have hvPos : 0 < v.length := by
    omega
  have hsLt : s < v.length := by
    dsimp [s]
    omega
  have hkPos : 0 < k := by
    dsimp [k]
    omega
  have hkLt : k < w.length := by
    dsimp [k, w]
    exact Nat.add_lt_add_right hsLt 1
  have hrun :
      Word.Runs
        w
        w.canonicalStart
        w.canonicalEnd :=
    P.paradoxical.valid.canonicalRuns
  have hdecomp :
      w = w.take k ++ w.drop k :=
    (List.take_append_drop k w).symm
  have hrun' :
      Word.Runs
        (w.take k ++ w.drop k)
        w.canonicalStart
        w.canonicalEnd := by
    rw [← hdecomp]
    exact hrun
  obtain ⟨x, hprefix, hsuffix0⟩ :=
    hrun'.split_append
  have hfloor :
      w.canonicalEnd < x := by
    exact
      P.endpointFloor k x hkPos hkLt
        (by
          simpa [w] using hprefix)
  have hdrop :
      w.drop k = v.drop s := by
    dsimp [w, k]
  have hsuffix :
      Word.Runs
        (v.drop s)
        x
        (Word.canonicalEnd (1 :: v)) := by
    rw [← hdrop]
    simpa [w] using hsuffix0
  refine ⟨x, ?_, ?_⟩
  · simpa [w] using hfloor
  · simpa [s] using hsuffix

/--
末尾 `r` 文字は nonempty suffix なので contracting。
-/
theorem Packet.tailSuffix_contracting
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ v.length) :
    Word.Contracting
      (v.drop (v.length - r)) := by
  have hAll :=
    P.tail_allSuffixesContracting.drop
      (v.length - r)
  have hlen :
      (v.drop (v.length - r)).length = r := by
    simp only [List.length_drop]
    omega
  have hne :
      v.drop (v.length - r) ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hlen]
    exact hrPos
  exact hAll.whole hne

/--
末尾 `r` 文字の backward strict-center inequality。
endpoint floor により suffix actual start は terminal `T` より真に大きい。
-/
theorem Packet.tailSuffix_strictCenter
    {v : Collatz.Word} {boundary : ℕ}
    (P : Packet v boundary)
    {r : ℕ}
    (hrPos : 0 < r)
    (hrLe : r ≤ v.length) :
    Word.affineConst (v.drop (v.length - r)) <
      Word.contractingGap (v.drop (v.length - r)) *
        Word.canonicalEnd (1 :: v) := by
  obtain ⟨x, hfloor, hsuffix⟩ :=
    P.exists_tailSuffix_runs_from_above
      hrPos hrLe
  have hC :
      Word.Contracting
        (v.drop (v.length - r)) :=
    P.tailSuffix_contracting
      hrPos hrLe
  exact
    strictCenter_of_contracting_descent
      hsuffix hC hfloor

end EndpointFloorZero

namespace FirstCrossingData.NaturalZeroReplaySignChangeData

/--
最短 source-preserving candidate から endpoint-floor zero packet を構成する。
-/
theorem exists_endpointFloorZeroPacket
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (D : NaturalZeroReplaySignChangeData F)
    (hGap : External.TwoThreeEffectiveGapInput) :
    ∃ v : Collatz.Word,
    ∃ boundary : ℕ,
      EndpointFloorZero.Packet v boundary := by
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
      segment_take_of_le O
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
    have hendCut :=
      C.endCut_eq_startCut_add_length
    have hEndCanonical' :
        O.value (R.startIndex + (C.startCut + C.length)) =
          Word.canonicalEnd C.word := by
      rw [← hendCut]
      exact hEndCanonical
    rw [hEndCanonical'] at hfloor
    rw [hy]
    simpa [C, Nat.add_assoc] using hfloor
  obtain ⟨v, hvNe, hCv⟩ := hObs.exists_prependOne_form
  rw [hCv] at hObs hPureFloor
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
      }⟩

end FirstCrossingData.NaturalZeroReplaySignChangeData

end PositiveReturn
end AdjacentReturn
end Collatz
