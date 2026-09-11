import CollatzLean.Collatz3.Bridge.Experimental2Profile
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordFerrers
import CollatzLean.Collatz3.Ferrers.RecordFerrers

/-!
# Collatz3 Bridge: 一般 RecordFerrers の Beatty 特殊化

`GenericRecordFerrers` で構成した一般理論を、
Collatz の critical Beatty roof

`β = Critical.beattyIndex`

へ戻す。

このファイルの目的は新しい条件を追加することではない。
既存の `Ferrers.RecordFerrers` が、一般 RecordFerrers を
`Critical.profileHeight` で実現した特殊化と exact に一致することを示す。

橋は次の順に閉じる。

1. generic `cutDepth` / `chordRank` は Critical 側のものと一致する。
2. deterministic record cut 列が一致する。
3. canonical block length 列が一致する。
4. cut 列で書かれた旧 canonical carry law と、length 列で書かれた
   generic contextual carry law が exact に一致する。
5. したがって旧 `IsRecordFerrersProfile` と generic `IsRecordFerrersPath` が一致する。

注意：generic `height : ℕ → ℕ` は terminal `m` より後ろにも値を持つため、
任意の generic `RecordFerrers` と finite profile の間に無条件の `Equiv` は置かない。
exact `Equiv` は `Critical.profileHeight` で実現された generic path に限定する。
-/

namespace Collatz3
open Experimental2
namespace Bridge

/--
Beatty roof と profile-height を代入した generic cut depth は、
Critical 側の saturated cut depth と exact に一致する。
-/
@[simp] theorem genericCutDepth_beatty_profileHeight_eq
    {m : ℕ}
    (h : Critical.Profile m)
    (k : ℕ) :
    GenericRecordFerrers.cutDepth
        Critical.beattyIndex m (Critical.profileHeight h) k =
      Critical.cutDepth h k := by
  by_cases hk : k < m
  · rw [GenericRecordFerrers.cutDepth_of_lt
      (β := Critical.beattyIndex)
      (height := Critical.profileHeight h) hk]
    rw [Critical.cutDepth_of_lt h hk]
    exact Critical.profileHeight_of_lt h hk
  · have hmk : m ≤ k := Nat.le_of_not_gt hk
    rw [GenericRecordFerrers.cutDepth_of_le
      (β := Critical.beattyIndex)
      (height := Critical.profileHeight h) hmk]
    rw [Critical.cutDepth_of_le h hmk]
    rfl

/--
Beatty 特殊化した generic chord rank は `Critical.profileChordRank` そのもの。
したがって deterministic record 幾何は両理論で同じになる。
-/
@[simp] theorem genericChordRank_beatty_profileHeight_eq
    {m : ℕ}
    (h : Critical.Profile m)
    (k : ℕ) :
    GenericRecordFerrers.chordRank
        Critical.beattyIndex m (Critical.profileHeight h) k =
      Critical.profileChordRank h k := by
  unfold GenericRecordFerrers.chordRank
  unfold Critical.profileChordRank
  rw [genericCutDepth_beatty_profileHeight_eq]
  rfl

/-- generic strict record cut と旧 Ferrers strict record cut は exact に同じ条件。 -/
theorem genericIsRecordCutAfter_beatty_iff
    {m : ℕ}
    (h : Critical.Profile m)
    (anchor k : ℕ) :
    GenericRecordFerrers.IsRecordCutAfter
        Critical.beattyIndex m (Critical.profileHeight h) anchor k ↔
      Ferrers.IsRecordCutAfter h anchor k := by
  unfold GenericRecordFerrers.IsRecordCutAfter
  unfold Ferrers.IsRecordCutAfter
  simp only [genericChordRank_beatty_profileHeight_eq]

/-- 任意 anchor に対する deterministic record cut 列も Beatty 特殊化で一致する。 -/
theorem genericRecordCutsAfter_beatty_eq
    {m : ℕ}
    (h : Critical.Profile m)
    (anchor : ℕ) :
    GenericRecordFerrers.recordCutsAfter
        Critical.beattyIndex m (Critical.profileHeight h) anchor =
      Ferrers.recordCutsAfter h anchor := by
  unfold GenericRecordFerrers.recordCutsAfter
  unfold Ferrers.recordCutsAfter
  apply List.filter_congr
  intro k _hk
  simp only [genericIsRecordCutAfter_beatty_iff h anchor k]

/-- 一般側の canonical anchor `1` は Critical 側の `initialRoofAnchor` と同一。 -/
@[simp] theorem genericCanonicalAnchor_eq_initialRoofAnchor :
    GenericRecordFerrers.canonicalAnchor =
      Critical.initialRoofAnchor :=
  rfl

/-- canonical record cut 列の Beatty 特殊化は `initialRecordCuts` そのもの。 -/
@[simp] theorem genericCanonicalRecordCuts_beatty_eq
    {m : ℕ}
    (h : Critical.Profile m) :
    GenericRecordFerrers.canonicalRecordCuts
        Critical.beattyIndex m (Critical.profileHeight h) =
      Ferrers.initialRecordCuts h := by
  unfold GenericRecordFerrers.canonicalRecordCuts
  unfold Ferrers.initialRecordCuts
  simpa using
    (genericRecordCutsAfter_beatty_eq
      h GenericRecordFerrers.canonicalAnchor)

/--
両層の `blockLengthsFromCuts` は同じ純粋な有限計算。
namespace が異なるため、ここで exact equality として明示する。
-/
@[simp] theorem genericBlockLengthsFromCuts_eq_ferrers
    (terminal a : ℕ)
    (cuts : List ℕ) :
    GenericRecordFerrers.blockLengthsFromCuts terminal a cuts =
      Ferrers.blockLengthsFromCuts terminal a cuts := by
  induction cuts generalizing a with
  | nil =>
      rfl
  | cons k ks ih =>
      simp only [
        GenericRecordFerrers.blockLengthsFromCuts,
        Ferrers.blockLengthsFromCuts
      ]
      rw [ih]

/--
Beatty/profile-height 特殊化した generic canonical block lengths は、
旧 `Ferrers.canonicalRecordLengths` と exact に一致する。
-/
@[simp] theorem genericCanonicalRecordLengths_beatty_eq
    {m : ℕ}
    (h : Critical.Profile m) :
    GenericRecordFerrers.canonicalRecordLengths
        Critical.beattyIndex m (Critical.profileHeight h) =
      Ferrers.canonicalRecordLengths h := by
  calc
    GenericRecordFerrers.canonicalRecordLengths
        Critical.beattyIndex m (Critical.profileHeight h)
        = GenericRecordFerrers.blockLengthsFromCuts
            m GenericRecordFerrers.canonicalAnchor
            (GenericRecordFerrers.canonicalRecordCuts
              Critical.beattyIndex m (Critical.profileHeight h)) := by
              rfl
    _ = Ferrers.blockLengthsFromCuts
          m GenericRecordFerrers.canonicalAnchor
          (GenericRecordFerrers.canonicalRecordCuts
            Critical.beattyIndex m (Critical.profileHeight h)) := by
          rw [genericBlockLengthsFromCuts_eq_ferrers]
    _ = Ferrers.blockLengthsFromCuts
          m Critical.initialRoofAnchor (Ferrers.initialRecordCuts h) := by
          rw [genericCanonicalRecordCuts_beatty_eq]
          rfl
    _ = Ferrers.canonicalRecordLengths h := by
          rfl

/--
Critical の premature carry-1 roof return 禁止条件は、
Beatty/profile-height を代入した generic 条件と definitionally 同じ。
-/
@[simp] theorem criticalNoPrematureCarryOneRoofReturn_iff_experimental2
    {m : ℕ}
    (h : Critical.Profile m)
    (a r : ℕ) :
    Critical.NoPrematureCarryOneRoofReturn h a r ↔
      NoPrematureCarryOneRoofReturn
        Critical.beattyIndex m (Critical.profileHeight h) a r := by
  rfl

/--
旧 `CanonicalCarryCompatibleFrom` は cut 列で再帰し、
generic `ContextualCarryCompatibleFrom` は block length 列で再帰する。

strict cut chain なら `a + (k-a) = k` なので、両者は exact に同値になる。
これは第9段階の carry 表現変換の中心補題。
-/
theorem criticalCanonicalCarryCompatibleFrom_iff_experimental2
    {m : ℕ}
    (h : Critical.Profile m) :
    ∀ (a : ℕ) (cuts : List ℕ),
      Ferrers.StrictCutChainFrom m a cuts →
      (Ferrers.CanonicalCarryCompatibleFrom h a cuts ↔
        ContextualCarryCompatibleFrom
          Critical.beattyIndex m (Critical.profileHeight h) a
          (Ferrers.blockLengthsFromCuts m a cuts))
  | a, [], _hChain => by
      rfl
  | a, k :: ks, hChain => by
      simp only [Ferrers.StrictCutChainFrom] at hChain
      have hak : a + (k - a) = k :=
        Nat.add_sub_of_le (Nat.le_of_lt hChain.1)
      have hTail :=
        criticalCanonicalCarryCompatibleFrom_iff_experimental2
          h k ks hChain.2.2
      change
        (Critical.NoPrematureCarryOneRoofReturn h a (k - a) ∧
          Ferrers.CanonicalCarryCompatibleFrom h k ks) ↔
        ContextualCarryCompatibleFrom
          Critical.beattyIndex m (Critical.profileHeight h) a
          ((k - a) :: Ferrers.blockLengthsFromCuts m k ks)
      have hTailNe :
          Ferrers.blockLengthsFromCuts m k ks ≠ [] :=
        Ferrers.blockLengthsFromCuts_ne_nil m k ks
      cases hEq : Ferrers.blockLengthsFromCuts m k ks with
      | nil =>
          exact False.elim (hTailNe hEq)
      | cons s ss =>
          rw [hEq] at hTail
          simp only [ContextualCarryCompatibleFrom]
          rw [hak]
          exact and_congr
            (criticalNoPrematureCarryOneRoofReturn_iff_experimental2
              h a (k - a))
            hTail

/--
旧 deterministic canonical carry law と、一般側の `CanonicalCarryCompatible` は
Beatty/profile-height 特殊化で exact に一致する。
-/
theorem criticalCanonicalCarryCompatible_iff_generic
    {m : ℕ}
    (H : Critical.AdmissibleProfile m)
    (hm : 1 < m) :
    Ferrers.CanonicalCarryCompatibleFrom
        H.1 Critical.initialRoofAnchor (Ferrers.initialRecordCuts H.1) ↔
      GenericRecordFerrers.CanonicalCarryCompatible
        Critical.beattyIndex m (Critical.profileHeight H.1) := by
  have hChain :
      Ferrers.StrictCutChainFrom
        m Critical.initialRoofAnchor (Ferrers.initialRecordCuts H.1) :=
    Ferrers.initialRecordCuts_strictCutChain (h := H.1) hm
  have hBridge :=
    criticalCanonicalCarryCompatibleFrom_iff_experimental2
      H.1 Critical.initialRoofAnchor (Ferrers.initialRecordCuts H.1) hChain
  unfold GenericRecordFerrers.CanonicalCarryCompatible
  rw [genericCanonicalRecordLengths_beatty_eq]
  simpa [Ferrers.canonicalRecordLengths] using hBridge

/--
旧 `IsRecordFerrersProfile` は、同じ profile の `profileHeight` を一般 Beatty roof 上で読む
`IsRecordFerrersPath` と exact に同値。

これにより旧 RecordFerrers は一般理論の genuine specialization になる。
-/
theorem isRecordFerrersProfile_iff_genericBeattyRecordFerrersPath
    {m : ℕ}
    (H : Critical.AdmissibleProfile m) :
    Ferrers.IsRecordFerrersProfile H ↔
      GenericRecordFerrers.IsRecordFerrersPath
        Critical.beattyIndex m (Critical.profileHeight H.1) := by
  constructor
  · intro R
    have hm : 1 < m := R.1
    have hCarry :
        GenericRecordFerrers.CanonicalCarryCompatible
          Critical.beattyIndex m (Critical.profileHeight H.1) :=
      (criticalCanonicalCarryCompatible_iff_generic H hm).1 R.2
    exact
      ⟨Critical.beattyIndex_one,
        admissibleProfile_isExperimental2RoofPath H.2,
        beattyIndex_hasUnitCarry,
        hm,
        hCarry⟩
  · intro R
    have hm : 1 < m := R.2.2.2.1
    have hCarry :
        Ferrers.CanonicalCarryCompatibleFrom
          H.1 Critical.initialRoofAnchor (Ferrers.initialRecordCuts H.1) :=
      (criticalCanonicalCarryCompatible_iff_generic H hm).2 R.2.2.2.2
    exact ⟨hm, hCarry⟩

/--
旧 RecordFerrers を一般 RecordFerrers へ送る canonical specialization map。
underlying generic path は `Critical.profileHeight` そのもの。
-/
def recordFerrersToGenericBeatty
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    GenericRecordFerrers.RecordFerrers
      Critical.beattyIndex m :=
  ⟨Critical.profileHeight R.profile.1,
    (isRecordFerrersProfile_iff_genericBeattyRecordFerrersPath R.profile).1 R.2⟩

@[simp] theorem recordFerrersToGenericBeatty_height
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    (recordFerrersToGenericBeatty R).height =
      Critical.profileHeight R.profile.1 :=
  rfl

/--
finite profile を保持したまま一般 RecordFerrers 条件で読む subtype。

任意の generic height ではなく、profile から `profileHeight` で実現されたものだけを取る。
この制限により terminal より後ろの不要な自由度を持ち込まない。
-/
abbrev BeattyProfileRecordFerrers (m : ℕ) :=
  {H : Critical.AdmissibleProfile m //
    GenericRecordFerrers.IsRecordFerrersPath
      Critical.beattyIndex m (Critical.profileHeight H.1)}

/--
旧 `Ferrers.RecordFerrers` と profile-realized generic Beatty RecordFerrers の exact equivalence。

第9段階の最終 bridge。
-/
def recordFerrersEquivBeattyProfileRecordFerrers
    (m : ℕ) :
    Ferrers.RecordFerrers m ≃ BeattyProfileRecordFerrers m where
  toFun R :=
    ⟨R.profile,
      (isRecordFerrersProfile_iff_genericBeattyRecordFerrersPath R.profile).1 R.2⟩
  invFun R :=
    ⟨R.1,
      (isRecordFerrersProfile_iff_genericBeattyRecordFerrersPath R.1).2 R.2⟩
  left_inv R := by
    apply Subtype.ext
    rfl
  right_inv R := by
    apply Subtype.ext
    rfl

end Bridge
end Collatz3
