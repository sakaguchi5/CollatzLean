import CollatzLean.Collatz3.CSTMicro.RecordCompatibility
import CollatzLean.Collatz3.Ferrers.RecordExactConsequences

/-!
# Collatz3 CSTCarry: Record compatibility failure の exact 分解

`FirstPassagePath.RecordCompatible` が偽である場合を fake theorem で埋めず、

* record-level tie,
* proper block 内の premature roof return + Beatty carry 1,
* terminal Beatty carry 1

へ有限再帰的に分解する。

`RecordCarryFailureFrom` は block start を再帰で保持するだけの thin predicate である。
-/

namespace Collatz3

namespace Critical

/-- proper local position で roof return と Beatty carry 1 が同時に起きる witness。 -/
def HasPrematureCarryOneRoofReturn
    {m : ℕ}
    (h : Profile m)
    (a r : ℕ) : Prop :=
  ∃ j : ℕ,
    0 < j ∧
    j < r ∧
    IsRoofCut h (a + j) ∧
    beattyCarry a j = 1

/-- `NoPrematureCarryOneRoofReturn` の exact negation。 -/
theorem not_noPrematureCarryOneRoofReturn_iff
    {m : ℕ}
    {h : Profile m}
    {a r : ℕ} :
    (¬ NoPrematureCarryOneRoofReturn h a r) ↔
      HasPrematureCarryOneRoofReturn h a r := by
  constructor
  · intro hBad
    classical
    unfold NoPrematureCarryOneRoofReturn at hBad
    push Not at hBad
    exact hBad
  · rintro ⟨j, hjPos, hjLt, hRoof, hCarry⟩ hNo
    exact hNo j hjPos hjLt ⟨hRoof, hCarry⟩

/--
canonical block length 列上の exact carry failure。

* singleton 最終 block: premature failure または terminal carry 1,
* interior block: premature failure または suffix failure。

空列では `RecordCarryCompatibleFrom = False` なので failure は `True`。
-/
def RecordCarryFailureFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | _a, [] => True
  | a, [r] =>
      HasPrematureCarryOneRoofReturn h a r ∨
        beattyCarry a r = 1
  | a, r :: s :: rs =>
      HasPrematureCarryOneRoofReturn h a r ∨
        RecordCarryFailureFrom h (a + r) (s :: rs)


/-- block chain のどこかに premature carry-1 roof return があること。 -/
def PrematureCarryFailureFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, r :: rs =>
      HasPrematureCarryOneRoofReturn h a r ∨
        PrematureCarryFailureFrom h (a + r) rs

/-- block chain の最後の block が terminal Beatty carry 1 を持つこと。 -/
def TerminalCarryOneFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] => beattyCarry a r = 1
  | a, r :: s :: rs =>
      TerminalCarryOneFrom h (a + r) (s :: rs)

/-- `RecordCarryCompatibleFrom` の exact negation。 -/
theorem not_recordCarryCompatibleFrom_iff_failure
    {m : ℕ}
    {h : Profile m} :
    ∀ (a : ℕ) (rs : List ℕ),
      (¬ RecordCarryCompatibleFrom h a rs) ↔
        RecordCarryFailureFrom h a rs
  | a, [] => by
      simp [RecordCarryCompatibleFrom, RecordCarryFailureFrom]
  | a, [r] => by
      constructor
      · intro hBad
        by_cases hNo : NoPrematureCarryOneRoofReturn h a r
        · have hCarryNe : beattyCarry a r ≠ 0 := by
            intro hZero
            exact hBad ⟨hNo, hZero⟩
          rcases beattyCarry_eq_zero_or_one a r with hZero | hOne
          · exact False.elim (hCarryNe hZero)
          · exact Or.inr hOne
        · exact Or.inl
            ((not_noPrematureCarryOneRoofReturn_iff).1 hNo)
      · intro hFail hGood
        rcases hFail with hPremature | hOne
        · exact
            ((not_noPrematureCarryOneRoofReturn_iff).2 hPremature)
              hGood.1
        · rw [hGood.2] at hOne
          omega
  | a, r :: s :: rs => by
      constructor
      · intro hBad
        by_cases hNo : NoPrematureCarryOneRoofReturn h a r
        · have hTailBad :
              ¬ RecordCarryCompatibleFrom h (a + r) (s :: rs) := by
            intro hTail
            exact hBad ⟨hNo, hTail⟩
          exact Or.inr
            ((not_recordCarryCompatibleFrom_iff_failure
              (a + r) (s :: rs)).1 hTailBad)
        · exact Or.inl
            ((not_noPrematureCarryOneRoofReturn_iff).1 hNo)
      · intro hFail hGood
        rcases hFail with hPremature | hTail
        · exact
            ((not_noPrematureCarryOneRoofReturn_iff).2 hPremature)
              hGood.1
        · exact
            ((not_recordCarryCompatibleFrom_iff_failure
              (a + r) (s :: rs)).2 hTail) hGood.2

/--
非空 block chain では carry failure は exact に

* どこかの premature failure,
* 最後の block の terminal carry 1

の二分岐になる。
-/
theorem recordCarryFailureFrom_iff_premature_or_terminal
    {m : ℕ}
    {h : Profile m} :
    ∀ {a : ℕ} {rs : List ℕ},
      rs ≠ [] →
      (RecordCarryFailureFrom h a rs ↔
        PrematureCarryFailureFrom h a rs ∨
          TerminalCarryOneFrom h a rs)
  | _a, [], hNonempty => by
      exact False.elim (hNonempty rfl)
  | a, [r], _hNonempty => by
      simp [RecordCarryFailureFrom, PrematureCarryFailureFrom,
        TerminalCarryOneFrom]
  | a, r :: s :: rs, _hNonempty => by
      simp only [RecordCarryFailureFrom, PrematureCarryFailureFrom,
        TerminalCarryOneFrom]
      rw [recordCarryFailureFrom_iff_premature_or_terminal
        (a := a + r) (rs := s :: rs) (by simp)]
      simp only [PrematureCarryFailureFrom]
      tauto

/--
非空 block 列の recursive failure から、
実際の premature witness または terminal carry-1 witness を得る。
-/
theorem RecordCarryFailureFrom.exists_premature_or_terminal
    {m : ℕ}
    {h : Profile m} :
    ∀ {a : ℕ} {rs : List ℕ},
      rs ≠ [] →
      RecordCarryFailureFrom h a rs →
        (∃ b r : ℕ, HasPrematureCarryOneRoofReturn h b r) ∨
        (∃ b r : ℕ, beattyCarry b r = 1)
  | _a, [], hNonempty, _h => by
      exact False.elim (hNonempty rfl)
  | a, [r], _hNonempty, hFail => by
      rcases hFail with hPremature | hOne
      · exact Or.inl ⟨a, r, hPremature⟩
      · exact Or.inr ⟨a, r, hOne⟩
  | a, r :: s :: rs, _hNonempty, hFail => by
      rcases hFail with hPremature | hTail
      · exact Or.inl ⟨a, r, hPremature⟩
      · exact RecordCarryFailureFrom.exists_premature_or_terminal
          (by simp) hTail

end Critical

namespace Ferrers

open Critical

/-- weak record cut が strict record cut に昇格しない exact tie witness。 -/
def RecordLevelTieWitness
    {m : ℕ}
    (h : Profile m)
    (anchor : ℕ) : Prop :=
  ∃ k : ℕ,
    IsWeakRecordCutAfter h anchor k ∧
      ¬ IsRecordCutAfter h anchor k

/-- `NoRecordLevelTie` の exact negation。 -/
theorem not_noRecordLevelTie_iff
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ} :
    (¬ NoRecordLevelTie h anchor) ↔
      RecordLevelTieWitness h anchor := by
  constructor
  · intro hBad
    classical
    unfold NoRecordLevelTie at hBad
    push Not at hBad
    exact hBad
  · rintro ⟨k, hWeak, hNotStrict⟩ hNo
    exact hNotStrict (hNo k hWeak)


/-- `m>1` なら canonical record length 列は非空。 -/
theorem canonicalRecordLengths_ne_nil
    {m : ℕ}
    {h : Profile m}
    (hm : 1 < m) :
    canonicalRecordLengths h ≠ [] := by
  intro hNil
  have hSum := canonicalRecordLengths_sum (h := h) hm
  rw [hNil] at hSum
  simp at hSum
  omega

end Ferrers

namespace CSTMicro
namespace FirstPassagePath

open Critical

/--
`p>1` の FirstPassagePath について、Record compatibility failure は
canonical record length 列上の exact carry failure と同値。

これは `CanonicalCarryCompatibleFrom ↔ RecordCarryCompatibleFrom` の
negation だけであり、新しい幾何仮定を置かない。
-/
theorem not_recordCompatible_iff_canonicalCarryFailure
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hm : 1 < P.endpointOddCount) :
    (¬ P.RecordCompatible hp) ↔
      Critical.RecordCarryFailureFrom
        (P.endpointIndexedCriticalProfile hp)
        Critical.initialRoofAnchor
        (Ferrers.canonicalRecordLengths
          (P.endpointIndexedCriticalProfile hp)) := by
  let h := P.endpointIndexedCriticalProfile hp
  have hBridge :=
    Ferrers.canonicalCarryCompatibleFrom_iff_recordCarryCompatibleCanonicalRecordLengths
      (h := h) hm
  constructor
  · intro hNotRecord
    have hNotCarry :
        ¬ Ferrers.CanonicalCarryCompatibleFrom
          h Critical.initialRoofAnchor
          (Ferrers.initialRecordCuts h) := by
      intro hCarry
      apply hNotRecord
      exact ⟨hm, hCarry⟩
    have hNotBlocks :
        ¬ Critical.RecordCarryCompatibleFrom
          h Critical.initialRoofAnchor
          (Ferrers.canonicalRecordLengths h) := by
      exact fun hBlocks => hNotCarry (hBridge.2 hBlocks)
    exact
      (Critical.not_recordCarryCompatibleFrom_iff_failure
        Critical.initialRoofAnchor
        (Ferrers.canonicalRecordLengths h)).1 hNotBlocks
  · intro hFailure hRecord
    have hCarry := hRecord.2
    have hBlocks := hBridge.1 hCarry
    have hNotBlocks :=
      (Critical.not_recordCarryCompatibleFrom_iff_failure
        Critical.initialRoofAnchor
        (Ferrers.canonicalRecordLengths h)).2 hFailure
    exact hNotBlocks hBlocks

/--
Record-compatible でない branch を

1. record-level tie,
2. canonical block carry failure

の disjunction に exact に持ち上げる。

後者は前 theorem によりさらに
premature roof return + carry 1 / terminal carry 1
へ再帰的に分解される。
-/
theorem not_recordCompatible_iff_tie_or_carryFailure
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hm : 1 < P.endpointOddCount) :
    (¬ P.RecordCompatible hp) ↔
      Ferrers.RecordLevelTieWitness
        (P.endpointIndexedCriticalProfile hp)
        Critical.initialRoofAnchor ∨
      Critical.RecordCarryFailureFrom
        (P.endpointIndexedCriticalProfile hp)
        Critical.initialRoofAnchor
        (Ferrers.canonicalRecordLengths
          (P.endpointIndexedCriticalProfile hp)) := by
  constructor
  · intro hNot
    exact Or.inr
      ((P.not_recordCompatible_iff_canonicalCarryFailure hp hm).1 hNot)
  · intro hFail
    rcases hFail with hTie | hCarryFailure
    · intro hRecord
      let h := P.endpointIndexedCriticalProfile hp
      have hNoTie :
          Ferrers.NoRecordLevelTie h Critical.initialRoofAnchor :=
        Ferrers.noRecordLevelTie_of_canonicalCarry
          (P.endpointIndexedCriticalProfile_admissible hp)
          hm hRecord.2
      exact
        ((Ferrers.not_noRecordLevelTie_iff).2 hTie) hNoTie
    · exact
        (P.not_recordCompatible_iff_canonicalCarryFailure hp hm).2
          hCarryFailure



/--
`p>1` では non-Record branch は exact に三分岐する。

1. record-level tie,
2. canonical block chain 内の premature carry-1 roof return,
3. canonical terminal block の Beatty carry 1.
-/
theorem not_recordCompatible_iff_three_way
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hm : 1 < P.endpointOddCount) :
    (¬ P.RecordCompatible hp) ↔
      Ferrers.RecordLevelTieWitness
        (P.endpointIndexedCriticalProfile hp)
        Critical.initialRoofAnchor ∨
      Critical.PrematureCarryFailureFrom
        (P.endpointIndexedCriticalProfile hp)
        Critical.initialRoofAnchor
        (Ferrers.canonicalRecordLengths
          (P.endpointIndexedCriticalProfile hp)) ∨
      Critical.TerminalCarryOneFrom
        (P.endpointIndexedCriticalProfile hp)
        Critical.initialRoofAnchor
        (Ferrers.canonicalRecordLengths
          (P.endpointIndexedCriticalProfile hp)) := by
  have hNonempty :
      Ferrers.canonicalRecordLengths
          (P.endpointIndexedCriticalProfile hp) ≠ [] :=
    Ferrers.canonicalRecordLengths_ne_nil hm
  constructor
  · intro hNot
    have hSplit :=
      (P.not_recordCompatible_iff_tie_or_carryFailure hp hm).1 hNot
    rcases hSplit with hTie | hCarry
    · exact Or.inl hTie
    · have hPT :=
        (Critical.recordCarryFailureFrom_iff_premature_or_terminal
          (a := Critical.initialRoofAnchor)
          (rs := Ferrers.canonicalRecordLengths
            (P.endpointIndexedCriticalProfile hp))
          hNonempty).1 hCarry
      exact Or.inr hPT
  · intro hThree
    rcases hThree with hTie | hPT
    · exact
        (P.not_recordCompatible_iff_tie_or_carryFailure hp hm).2
          (Or.inl hTie)
    · have hCarry :=
        (Critical.recordCarryFailureFrom_iff_premature_or_terminal
          (a := Critical.initialRoofAnchor)
          (rs := Ferrers.canonicalRecordLengths
            (P.endpointIndexedCriticalProfile hp))
          hNonempty).2 hPT
      exact
        (P.not_recordCompatible_iff_tie_or_carryFailure hp hm).2
          (Or.inr hCarry)

/--
`p>1` の non-Record branch から、三種類の具体的 witness のいずれかを得る。

1. record-level tie,
2. proper local premature roof return + carry 1,
3. terminal carry 1.
-/
theorem not_recordCompatible_three_way
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hm : 1 < P.endpointOddCount)
    (hNot : ¬ P.RecordCompatible hp) :
    Ferrers.RecordLevelTieWitness
        (P.endpointIndexedCriticalProfile hp)
        Critical.initialRoofAnchor ∨
      (∃ b r : ℕ,
        Critical.HasPrematureCarryOneRoofReturn
          (P.endpointIndexedCriticalProfile hp) b r) ∨
      (∃ b r : ℕ, Critical.beattyCarry b r = 1) := by
  have hSplit :=
    (P.not_recordCompatible_iff_tie_or_carryFailure hp hm).1 hNot
  rcases hSplit with hTie | hCarry
  · exact Or.inl hTie
  · have hNonempty :
        Ferrers.canonicalRecordLengths
            (P.endpointIndexedCriticalProfile hp) ≠ [] :=
      Ferrers.canonicalRecordLengths_ne_nil hm
    have hWitness :=
      Critical.RecordCarryFailureFrom.exists_premature_or_terminal
        hNonempty hCarry
    rcases hWitness with hPremature | hTerminal
    · exact Or.inr (Or.inl hPremature)
    · exact Or.inr (Or.inr hTerminal)

end FirstPassagePath
end CSTMicro

end Collatz3
