import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordFerrers
import CollatzLean.Collatz3.Experimental2.Normalization

/-!
# Collatz3 Experimental2: 整数直線成分に対する gauge 不変性

屋根と path に同じ整数直線 `c*n` を加える。

`βᶜ(n) = c*n + β(n)`
`heightᶜ(n) = c*n + height(n)`

proper cut `k ≤ m` では、終端弦順位の線形成分が exact に相殺される。
その結果、

* unit-carry law と carry,
* roof contact,
* proper-cut chord rank,
* deterministic record cuts,
* canonical record lengths,
* canonical carry compatibility

は保存される。

一方 `β 1 = 1` は `βᶜ 1 = c + β 1` に変わるので不変ではない。
したがって `β 1 = 1` は RecordFerrers の本質的 law ではなく、
標準座標を一つ選ぶ gauge 固定条件である。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/-- 屋根へ整数直線 `c*n` を加える。 -/
def linearLiftRoof
    (c : ℕ)
    (β : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  c * n + β n

/-- path へ同じ整数直線 `c*n` を加える。 -/
def linearLiftHeight
    (c : ℕ)
    (height : ℕ → ℕ)
    (n : ℕ) : ℕ :=
  c * n + height n

/-- linear lift 後の critical depth。 -/
theorem criticalDepth_linearLiftRoof
    (c : ℕ)
    (β : ℕ → ℕ)
    (m : ℕ) :
    criticalDepth (linearLiftRoof c β) m =
      c * m + criticalDepth β m := by
  unfold criticalDepth linearLiftRoof
  omega

/-- linear lift は unit-carry 性を保存する。 -/
theorem linearLiftRoof_hasUnitCarry
    {β : ℕ → ℕ}
    (c : ℕ)
    (U : HasUnitCarry β) :
    HasUnitCarry (linearLiftRoof c β) := by
  unfold HasUnitCarry
  constructor
  · unfold IsSuperadditiveRoof
    intro a b
    have h := U.lower a b
    simp only [linearLiftRoof, Nat.mul_add]
    omega
  · unfold HasUnitUpperDefect
    intro a b
    have h := U.upper a b
    simp only [linearLiftRoof, Nat.mul_add]
    omega

/-- unit-carry 性そのものも linear lift で exact に不変。 -/
theorem hasUnitCarry_linearLift_iff
    {β : ℕ → ℕ}
    (c : ℕ) :
    HasUnitCarry (linearLiftRoof c β) ↔ HasUnitCarry β := by
  constructor
  · intro Uc
    unfold HasUnitCarry at Uc ⊢
    constructor
    · unfold IsSuperadditiveRoof at Uc ⊢
      intro a b
      have h := Uc.1 a b
      simp only [linearLiftRoof, Nat.mul_add] at h
      omega
    · unfold HasUnitUpperDefect at Uc ⊢
      intro a b
      have h := Uc.2 a b
      simp only [linearLiftRoof, Nat.mul_add] at h
      omega
  · exact linearLiftRoof_hasUnitCarry c

/-- linear lift で binary carry は exact に変わらない。 -/
theorem roofCarry_linearLiftRoof_eq
    {β : ℕ → ℕ}
    (c : ℕ)
    (U : HasUnitCarry β)
    (a b : ℕ) :
    roofCarry (linearLiftRoof c β) a b = roofCarry β a b := by
  have hBase := U.add_eq a b
  have hLift := (linearLiftRoof_hasUnitCarry c U).add_eq a b
  simp only [linearLiftRoof, Nat.mul_add] at hLift
  omega

/-- linear lift の `1` での値。標準条件 `β 1 = 1` 自体は gauge 不変ではない。 -/
@[simp] theorem linearLiftRoof_one
    (c : ℕ)
    (β : ℕ → ℕ) :
    linearLiftRoof c β 1 = c + β 1 := by
  simp [linearLiftRoof]

/--
整数直線を加えてから正規化しても、元の屋根を正規化したものと exact に一致する。
これが slope の整数部分を消した canonical 座標の不変性。
-/
theorem normalizeRoof_linearLiftRoof_eq
    {β : ℕ → ℕ}
    (c : ℕ)
    (U : HasUnitCarry β)
    (n : ℕ) :
    normalizeRoof (linearLiftRoof c β) n = normalizeRoof β n := by
  have hLe := U.linearPart_le n
  unfold normalizeRoof linearLiftRoof
  simp only [Nat.mul_one, Nat.mul_add]
  rw [Nat.mul_comm c n]
  omega

/-- roof contact は path と roof を同時に linear lift すると exact に保存される。 -/
theorem isOnRoof_linearLift_iff
    (c : ℕ)
    (β height : ℕ → ℕ)
    (a : ℕ) :
    IsOnRoof (linearLiftRoof c β) (linearLiftHeight c height) a ↔
      IsOnRoof β height a := by
  unfold IsOnRoof linearLiftRoof linearLiftHeight
  omega

/-- proper roof cut も linear lift で exact に保存される。 -/
theorem isProperRoofCut_linearLift_iff
    (c : ℕ)
    (β : ℕ → ℕ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (a : ℕ) :
    IsProperRoofCut (linearLiftRoof c β) m (linearLiftHeight c height) a ↔
      IsProperRoofCut β m height a := by
  unfold IsProperRoofCut
  constructor
  · rintro ⟨haPos, haLt, hRoof⟩
    exact ⟨haPos, haLt, (isOnRoof_linearLift_iff c β height a).1 hRoof⟩
  · rintro ⟨haPos, haLt, hRoof⟩
    exact ⟨haPos, haLt, (isOnRoof_linearLift_iff c β height a).2 hRoof⟩

/-- admissible path は roof と path の同時 linear lift で admissible のまま。 -/
theorem admissibleRoofPath_linearLift
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    (A : IsAdmissibleRoofPath β m height) :
    IsAdmissibleRoofPath
      (linearLiftRoof c β) m (linearLiftHeight c height) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have hLe := A.1 k hk
    unfold linearLiftRoof linearLiftHeight
    omega
  · intro k hk
    have hLt := A.2.1 k hk
    unfold linearLiftHeight
    rw [Nat.mul_succ]
    omega
  · unfold HasCriticalTerminal
    rw [criticalDepth_linearLiftRoof]
    unfold linearLiftHeight
    rw [A.2.2]

/-- proper cut では cut depth 自体が同じ線形成分だけ増える。 -/
theorem cutDepth_linearLift_of_lt
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    {k : ℕ}
    (hk : k < m) :
    cutDepth (linearLiftRoof c β) m (linearLiftHeight c height) k =
      c * k + cutDepth β m height k := by
  rw [cutDepth_of_lt (β := linearLiftRoof c β)
      (height := linearLiftHeight c height) hk]
  rw [cutDepth_of_lt (β := β) (height := height) hk]
  rfl

/-- proper cut の chord rank は linear lift で exact に不変。 -/
theorem chordRank_linearLift_of_lt
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    {k : ℕ}
    (hk : k < m) :
    chordRank (linearLiftRoof c β) m (linearLiftHeight c height) k =
      chordRank β m height k := by
  rw [chordRank_of_lt
      (β := linearLiftRoof c β)
      (height := linearLiftHeight c height) hk]
  rw [chordRank_of_lt (β := β) (height := height) hk]
  rw [criticalDepth_linearLiftRoof]
  unfold linearLiftHeight
  push_cast
  ring

/-- terminal `m` を含む `k ≤ m` の全域で chord rank は不変。 -/
theorem chordRank_linearLift_of_le
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    {k : ℕ}
    (hk : k ≤ m) :
    chordRank (linearLiftRoof c β) m (linearLiftHeight c height) k =
      chordRank β m height k := by
  rcases lt_or_eq_of_le hk with hkLt | rfl
  · exact chordRank_linearLift_of_lt c hkLt
  · simp [chordRank_terminal_eq_zero]

/-- strict record cut predicate は linear lift で exact に不変。 -/
theorem isRecordCutAfter_linearLift_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    {anchor k : ℕ} :
    IsRecordCutAfter
        (linearLiftRoof c β) m (linearLiftHeight c height) anchor k ↔
      IsRecordCutAfter β m height anchor k := by
  constructor
  · intro R
    have hR :=
      (isRecordCutAfter_iff
        (β := linearLiftRoof c β) (m := m)
        (height := linearLiftHeight c height)
        (anchor := anchor) (k := k)).1 R
    apply
      (isRecordCutAfter_iff
        (β := β) (m := m) (height := height)
        (anchor := anchor) (k := k)).2
    refine ⟨hR.1, hR.2.1, ?_⟩
    intro j haj hjk
    have hjm : j < m := lt_trans hjk hR.2.1
    have h := hR.2.2 j haj hjk
    rw [chordRank_linearLift_of_lt c hR.2.1] at h
    rw [chordRank_linearLift_of_lt c hjm] at h
    exact h
  · intro R
    have hR :=
      (isRecordCutAfter_iff
        (β := β) (m := m) (height := height)
        (anchor := anchor) (k := k)).1 R
    apply
      (isRecordCutAfter_iff
        (β := linearLiftRoof c β) (m := m)
        (height := linearLiftHeight c height)
        (anchor := anchor) (k := k)).2
    refine ⟨hR.1, hR.2.1, ?_⟩
    intro j haj hjk
    have hjm : j < m := lt_trans hjk hR.2.1
    have h := hR.2.2 j haj hjk
    rw [chordRank_linearLift_of_lt c hR.2.1]
    rw [chordRank_linearLift_of_lt c hjm]
    exact h

/-- weak record cut predicate も linear lift で exact に不変。 -/
theorem isWeakRecordCutAfter_linearLift_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    {anchor k : ℕ} :
    IsWeakRecordCutAfter
        (linearLiftRoof c β) m (linearLiftHeight c height) anchor k ↔
      IsWeakRecordCutAfter β m height anchor k := by
  constructor
  · intro R
    have hR :=
      (isWeakRecordCutAfter_iff
        (β := linearLiftRoof c β) (m := m)
        (height := linearLiftHeight c height)
        (anchor := anchor) (k := k)).1 R
    apply
      (isWeakRecordCutAfter_iff
        (β := β) (m := m) (height := height)
        (anchor := anchor) (k := k)).2
    refine ⟨hR.1, hR.2.1, ?_⟩
    intro j haj hjk
    have hjm : j < m := lt_trans hjk hR.2.1
    have h := hR.2.2 j haj hjk
    rw [chordRank_linearLift_of_lt c hR.2.1] at h
    rw [chordRank_linearLift_of_lt c hjm] at h
    exact h
  · intro R
    have hR :=
      (isWeakRecordCutAfter_iff
        (β := β) (m := m) (height := height)
        (anchor := anchor) (k := k)).1 R
    apply
      (isWeakRecordCutAfter_iff
        (β := linearLiftRoof c β) (m := m)
        (height := linearLiftHeight c height)
        (anchor := anchor) (k := k)).2
    refine ⟨hR.1, hR.2.1, ?_⟩
    intro j haj hjk
    have hjm : j < m := lt_trans hjk hR.2.1
    have h := hR.2.2 j haj hjk
    rw [chordRank_linearLift_of_lt c hR.2.1]
    rw [chordRank_linearLift_of_lt c hjm]
    exact h

/-- record-level tie 排除条件も linear lift で exact に不変。 -/
theorem noRecordLevelTie_linearLift_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    (anchor : ℕ) :
    NoRecordLevelTie
        (linearLiftRoof c β) m (linearLiftHeight c height) anchor ↔
      NoRecordLevelTie β m height anchor := by
  unfold NoRecordLevelTie
  constructor
  · intro T k Wbase
    have Wlift := (isWeakRecordCutAfter_linearLift_iff c).2 Wbase
    have Rlift := T k Wlift
    exact (isRecordCutAfter_linearLift_iff c).1 Rlift
  · intro T k Wlift
    have Wbase := (isWeakRecordCutAfter_linearLift_iff c).1 Wlift
    have Rbase := T k Wbase
    exact (isRecordCutAfter_linearLift_iff c).2 Rbase

/-- 任意 anchor の deterministic record cut list は linear lift で変わらない。 -/
theorem recordCutsAfter_linearLift_eq
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    (anchor : ℕ) :
    recordCutsAfter
        (linearLiftRoof c β) m (linearLiftHeight c height) anchor =
      recordCutsAfter β m height anchor := by
  unfold recordCutsAfter
  apply List.filter_congr
  intro k _hk
  simp only [isRecordCutAfter_linearLift_iff c]

/-- canonical record cut list は linear lift で変わらない。 -/
theorem canonicalRecordCuts_linearLift_eq
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ) :
    canonicalRecordCuts
        (linearLiftRoof c β) m (linearLiftHeight c height) =
      canonicalRecordCuts β m height := by
  unfold canonicalRecordCuts
  exact recordCutsAfter_linearLift_eq c canonicalAnchor

/-- canonical block length 列も linear lift で exact に変わらない。 -/
theorem canonicalRecordLengths_linearLift_eq
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ) :
    canonicalRecordLengths
        (linearLiftRoof c β) m (linearLiftHeight c height) =
      canonicalRecordLengths β m height := by
  unfold canonicalRecordLengths recordLengthsAfter
  rw [recordCutsAfter_linearLift_eq c canonicalAnchor]

/-- premature carry-1 roof return 排除も linear lift で exact に不変。 -/
theorem noPrematureCarryOneRoofReturn_linearLift_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    (U : HasUnitCarry β)
    (a r : ℕ) :
    NoPrematureCarryOneRoofReturn
        (linearLiftRoof c β) m (linearLiftHeight c height) a r ↔
      NoPrematureCarryOneRoofReturn β m height a r := by
  constructor
  · intro H j hjPos hjLt hBad
    apply H j hjPos hjLt
    refine ⟨(isProperRoofCut_linearLift_iff
      c β m height (a + j)).2 hBad.1, ?_⟩
    rw [roofCarry_linearLiftRoof_eq c U]
    exact hBad.2
  · intro H j hjPos hjLt hBad
    apply H j hjPos hjLt
    refine ⟨(isProperRoofCut_linearLift_iff
      c β m height (a + j)).1 hBad.1, ?_⟩
    have hCarry : roofCarry β a j = 1 := by
      simpa [roofCarry_linearLiftRoof_eq c U] using hBad.2
    exact hCarry

/-- contextual carry compatibility は任意 block list 上で linear lift 不変。 -/
theorem contextualCarryCompatibleFrom_linearLift_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    (U : HasUnitCarry β) :
    ∀ (a : ℕ) (rs : List ℕ),
      ContextualCarryCompatibleFrom
          (linearLiftRoof c β) m (linearLiftHeight c height) a rs ↔
        ContextualCarryCompatibleFrom β m height a rs
  | _a, [] => by
      simp [ContextualCarryCompatibleFrom]
  | a, [r] => by
      simp only [ContextualCarryCompatibleFrom]
      rw [noPrematureCarryOneRoofReturn_linearLift_iff c U a r]
      rw [roofCarry_linearLiftRoof_eq c U]
  | a, r :: s :: rs => by
      simp only [ContextualCarryCompatibleFrom]
      rw [noPrematureCarryOneRoofReturn_linearLift_iff c U a r]
      exact and_congr Iff.rfl
        (contextualCarryCompatibleFrom_linearLift_iff
          c U (a + r) (s :: rs))

/-- canonical carry compatibility は linear lift で exact に不変。 -/
theorem canonicalCarryCompatible_linearLift_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    (U : HasUnitCarry β) :
    CanonicalCarryCompatible
        (linearLiftRoof c β) m (linearLiftHeight c height) ↔
      CanonicalCarryCompatible β m height := by
  unfold CanonicalCarryCompatible
  rw [canonicalRecordLengths_linearLift_eq c]
  exact contextualCarryCompatibleFrom_linearLift_iff
    c U canonicalAnchor (canonicalRecordLengths β m height)

/-- admissible path 上の local depth は同じ線形成分 `c*j` だけ増える。 -/
theorem localDepth_linearLift_eq
    {height : ℕ → ℕ}
    (c : ℕ)
    {a j : ℕ}
    (hMono : height a ≤ height (a + j)) :
    localDepth (linearLiftHeight c height) a j =
      c * j + localDepth height a j := by
  unfold localDepth linearLiftHeight
  rw [Nat.mul_add]
  omega

/--
base path が admissible なら、一 block の local criticality は linear lift で exact に不変。
-/
theorem isLocalRoofCriticalBlock_linearLift_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    (A : IsAdmissibleRoofPath β m height)
    {a r : ℕ} :
    IsLocalRoofCriticalBlock
        (linearLiftRoof c β) m (linearLiftHeight c height) a r ↔
      IsLocalRoofCriticalBlock β m height a r := by
  constructor
  · intro L
    refine ⟨L.1, L.2.1, ?_, ?_⟩
    · have hMono := A.height_le_add a r L.2.1
      have hDepth := localDepth_linearLift_eq c hMono
      have hCrit := criticalDepth_linearLiftRoof c β r
      have hEq := L.2.2.1
      rw [hDepth, hCrit] at hEq
      omega
    · intro j hjPos hjLt
      have hArLe : a + r ≤ m := L.2.1
      have hEnd : a + j ≤ m := by
        omega
      have hMono := A.height_le_add a j hEnd
      have hDepth := localDepth_linearLift_eq c hMono
      have hBound := L.2.2.2 j hjPos hjLt
      rw [hDepth] at hBound
      unfold linearLiftRoof at hBound
      omega
  · intro L
    refine ⟨L.1, L.2.1, ?_, ?_⟩
    · have hMono := A.height_le_add a r L.2.1
      rw [localDepth_linearLift_eq c hMono]
      rw [criticalDepth_linearLiftRoof]
      rw [L.2.2.1]
    · intro j hjPos hjLt
      have hArLe : a + r ≤ m := L.2.1
      have hEnd : a + j ≤ m := by
        omega
      have hMono := A.height_le_add a j hEnd
      rw [localDepth_linearLift_eq c hMono]
      unfold linearLiftRoof
      have hBound := L.2.2.2 j hjPos hjLt
      omega

/-- local critical block chain 全体も linear lift で exact に不変。 -/
theorem localRoofCriticalBlocksFrom_linearLift_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    (A : IsAdmissibleRoofPath β m height) :
    ∀ (a : ℕ) (rs : List ℕ),
      LocalRoofCriticalBlocksFrom
          (linearLiftRoof c β) m (linearLiftHeight c height) a rs ↔
        LocalRoofCriticalBlocksFrom β m height a rs
  | _a, [] => by
      simp [LocalRoofCriticalBlocksFrom]
  | a, r :: rs => by
      simp only [LocalRoofCriticalBlocksFrom]
      rw [isLocalRoofCriticalBlock_linearLift_iff c A]
      exact and_congr Iff.rfl
        (localRoofCriticalBlocksFrom_linearLift_iff c A (a + r) rs)

/-- canonical local criticality も canonical lengths の不変性と合わせて exact に保存される。 -/
theorem canonicalLocalCritical_linearLift_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ)
    (A : IsAdmissibleRoofPath β m height) :
    LocalRoofCriticalBlocksFrom
        (linearLiftRoof c β) m (linearLiftHeight c height) canonicalAnchor
        (canonicalRecordLengths
          (linearLiftRoof c β) m (linearLiftHeight c height)) ↔
      LocalRoofCriticalBlocksFrom
        β m height canonicalAnchor (canonicalRecordLengths β m height) := by
  rw [canonicalRecordLengths_linearLift_eq c]
  exact localRoofCriticalBlocksFrom_linearLift_iff
    c A canonicalAnchor (canonicalRecordLengths β m height)

/--
本質的 canonical record/carry law は linear lift で exact に不変。

`HasCanonicalRecordLaw` から admissibility と `β 1 = 1` を分離したことで、
この層では本当に iff が得られる。
-/
theorem hasCanonicalRecordLaw_linearLift_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    {height : ℕ → ℕ}
    (c : ℕ) :
    HasCanonicalRecordLaw
        (linearLiftRoof c β) m (linearLiftHeight c height) ↔
      HasCanonicalRecordLaw β m height := by
  constructor
  · intro H
    have U : HasUnitCarry β :=
      (hasUnitCarry_linearLift_iff c).1 H.1
    refine ⟨U, H.2.1, ?_⟩
    exact (canonicalCarryCompatible_linearLift_iff c U).1 H.2.2
  · intro H
    refine ⟨linearLiftRoof_hasUnitCarry c H.1, H.2.1, ?_⟩
    exact (canonicalCarryCompatible_linearLift_iff c H.1).2 H.2.2

/--
完成 RecordFerrers を linear lift すると、本質的 canonical law はそのまま残る。
標準 gauge 条件だけが `βᶜ 1 = c+1` へ移る。
-/
theorem recordFerrers_linearLift_canonicalLaw
    {β : ℕ → ℕ}
    {m : ℕ}
    (c : ℕ)
    (R : RecordFerrers β m) :
    HasCanonicalRecordLaw
      (linearLiftRoof c β) m (linearLiftHeight c R.height) :=
  (hasCanonicalRecordLaw_linearLift_iff c).2 R.canonicalLaw

/-- 完成 RecordFerrers の admissibility も linear lift で前向きに保存される。 -/
theorem recordFerrers_linearLift_admissible
    {β : ℕ → ℕ}
    {m : ℕ}
    (c : ℕ)
    (R : RecordFerrers β m) :
    IsAdmissibleRoofPath
      (linearLiftRoof c β) m (linearLiftHeight c R.height) :=
  admissibleRoofPath_linearLift c R.admissible

/-- normalized RecordFerrers の roof を lift したとき `1` での値は `c+1`。 -/
theorem recordFerrers_linearLift_roof_one
    {β : ℕ → ℕ}
    {m : ℕ}
    (c : ℕ)
    (R : RecordFerrers β m) :
    linearLiftRoof c β 1 = c + 1 := by
  rw [linearLiftRoof_one, R.roof_one]

/--
完成 RecordFerrers を linear lift した path が再び標準座標 `β 1 = 1` を満たすのは
`c = 0` の場合に限る。したがって `β 1 = 1` は genuine gauge fixing である。
-/
theorem recordFerrers_linearLift_isRecordFerrersPath_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    (c : ℕ)
    (R : RecordFerrers β m) :
    IsRecordFerrersPath
        (linearLiftRoof c β) m (linearLiftHeight c R.height) ↔
      c = 0 := by
  constructor
  · intro H
    have hOne := H.1
    rw [recordFerrers_linearLift_roof_one c R] at hOne
    omega
  · intro hc
    subst c
    have hRoof :
        linearLiftRoof 0 β = β := by
      funext n
      simp [linearLiftRoof]
    have hHeight :
        linearLiftHeight 0 R.height = R.height := by
      funext n
      simp [linearLiftHeight]
    rw [hRoof, hHeight]
    exact R.2

end GenericRecordFerrers
end Experimental2
end Collatz3
