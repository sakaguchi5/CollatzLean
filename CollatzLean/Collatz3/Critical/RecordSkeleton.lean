import CollatzLean.Collatz3.Critical.Ferrers
import CollatzLean.Collatz3.Critical.RoofAnchor
import CollatzLean.Collatz3.Combinatorics.Record

/-!
# Collatz3: critical roof record skeleton

この層は full `RecordFerrers` ではない。

* 開始点は positive critical-roof anchor。
* 各 block は global chord rank に対する strict excursion。
* interior endpoint は再び critical roof に戻る。
* 最後の block は terminal `m` へ strict に落ちる。

local block 自身が critical first-passage であること、Beatty carry、Ferrers deficit の
factorization、actual Collatz realization はここには保存しない。

旧 `Critical.RecordFerrers` が担っていた責務を、このより正確な名前へ分離する。
-/

namespace Collatz3
namespace Critical

namespace RoofRecordSkeleton

/--
roof anchor から strict record block 長さ列を terminal まで連結する pure predicate。

最後の block だけは endpoint が terminal `m` に一致し、roof return を要求しない。
-/
def RealizesBlocksFrom
    {m : ℕ}
    (h : Profile m) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] =>
      Combinatorics.IsRecordBlock (profileChordRank h) a r ∧
        a + r = m
  | a, r :: s :: rs =>
      Combinatorics.IsRecordBlock (profileChordRank h) a r ∧
        IsRoofCut h (a + r) ∧
        RealizesBlocksFrom h (a + r) (s :: rs)

/-- roof-compatible chain を generic record realization へ忘却する。 -/
theorem realizesBlocksFrom_record
    {m : ℕ}
    {h : Profile m} :
    ∀ (a : ℕ) (rs : List ℕ),
      RealizesBlocksFrom h a rs →
        Combinatorics.RecordSkeleton.realizesLengthsFrom
          (profileChordRank h) a rs
  | _a, [], hFalse => False.elim hFalse
  | a, [r], hOne => by
      refine ⟨hOne.1, ?_⟩
      trivial
  | a, r :: s :: rs, hMany => by
      refine ⟨hMany.1, ?_⟩
      exact realizesBlocksFrom_record
        (a + r) (s :: rs) hMany.2.2

/-- roof-compatible chain は開始点から terminal まで exact に覆う。 -/
theorem realizesBlocksFrom_end
    {m : ℕ}
    {h : Profile m} :
    ∀ (a : ℕ) (rs : List ℕ),
      RealizesBlocksFrom h a rs →
        a + rs.sum = m
  | _a, [], hFalse => False.elim hFalse
  | a, [r], hOne => by
      simpa using hOne.2
  | a, r :: s :: rs, hMany => by
      have hTail := realizesBlocksFrom_end
        (a + r) (s :: rs) hMany.2.2
      simpa [Nat.add_assoc] using hTail

/--
指定した positive roof anchor から skeleton が strict record excursion chain を実現する。
-/
def AnchoredRealizes
    {m : ℕ}
    (h : Profile m)
    (anchor : ℕ)
    (S : Combinatorics.RecordSkeleton) : Prop :=
  IsRoofCut h anchor ∧
    RealizesBlocksFrom h anchor S.lengths

namespace AnchoredRealizes

/-- realization の開始点は roof cut。 -/
theorem anchor_roof
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ}
    {S : Combinatorics.RecordSkeleton}
    (R : AnchoredRealizes h anchor S) :
    IsRoofCut h anchor :=
  R.1

/-- realization の block 列は必ず非空。 -/
theorem lengths_nonempty
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ}
    {S : Combinatorics.RecordSkeleton}
    (R : AnchoredRealizes h anchor S) :
    S.lengths ≠ [] := by
  intro hNil
  have hBlocks := R.2
  rw [hNil] at hBlocks
  simp [RealizesBlocksFrom] at hBlocks

/-- roof-compatible realization は generic record realization を忘却像として持つ。 -/
theorem record_realization
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ}
    {S : Combinatorics.RecordSkeleton}
    (R : AnchoredRealizes h anchor S) :
    S.RealizesFrom (profileChordRank h) anchor := by
  unfold Combinatorics.RecordSkeleton.RealizesFrom
  exact realizesBlocksFrom_record anchor S.lengths R.2

/-- roof-compatible realization は anchor から terminal まで exact に覆う。 -/
theorem anchor_add_totalLength_eq_terminal
    {m : ℕ}
    {h : Profile m}
    {anchor : ℕ}
    {S : Combinatorics.RecordSkeleton}
    (R : AnchoredRealizes h anchor S) :
    anchor + S.totalLength = m := by
  unfold Combinatorics.RecordSkeleton.totalLength
  exact realizesBlocksFrom_end anchor S.lengths R.2

end AnchoredRealizes
end RoofRecordSkeleton

/--
任意の positive roof anchor を明示した critical record skeleton packet。
Profile と generic length skeleton だけを保存し、local criticality は保存しない。
-/
structure AnchoredCriticalRecordSkeleton (m : ℕ) where
  profile : AdmissibleProfile m
  anchor : ℕ
  skeleton : Combinatorics.RecordSkeleton
  realizes : RoofRecordSkeleton.AnchoredRealizes profile.1 anchor skeleton

namespace AnchoredCriticalRecordSkeleton

/-- underlying admissible profile を忘却する。 -/
def forget
    {m : ℕ}
    (R : AnchoredCriticalRecordSkeleton m) : AdmissibleProfile m :=
  R.profile

/-- anchor は正。 -/
theorem anchor_pos
    {m : ℕ}
    (R : AnchoredCriticalRecordSkeleton m) :
    0 < R.anchor :=
  R.realizes.anchor_roof.pos

/-- anchor は terminal より手前。 -/
theorem anchor_lt_terminal
    {m : ℕ}
    (R : AnchoredCriticalRecordSkeleton m) :
    R.anchor < m :=
  R.realizes.anchor_roof.lt_width

/-- skeleton は anchor から terminal まで exact に覆う。 -/
theorem anchor_add_totalLength_eq_terminal
    {m : ℕ}
    (R : AnchoredCriticalRecordSkeleton m) :
    R.anchor + R.skeleton.totalLength = m :=
  R.realizes.anchor_add_totalLength_eq_terminal

/-- terminal rank は anchor rank より strict に低い。 -/
theorem terminal_rank_lt_anchor_rank
    {m : ℕ}
    (R : AnchoredCriticalRecordSkeleton m) :
    profileChordRank R.profile.1 m <
      profileChordRank R.profile.1 R.anchor := by
  have hDrop := R.skeleton.end_drop_of_realizesFrom
    R.realizes.record_realization
    R.realizes.lengths_nonempty
  rw [R.anchor_add_totalLength_eq_terminal] at hDrop
  exact hDrop

end AnchoredCriticalRecordSkeleton

/--
canonical positive roof anchor `1` を使う critical record skeleton。

これは full `RecordFerrers` ではない。local block criticality は後段で導く。
-/
structure CriticalRecordSkeleton (m : ℕ) where
  profile : AdmissibleProfile m
  skeleton : Combinatorics.RecordSkeleton
  realizes : RoofRecordSkeleton.AnchoredRealizes
    profile.1 initialRoofAnchor skeleton

namespace CriticalRecordSkeleton

/-- underlying admissible profile を忘却する。 -/
def forget
    {m : ℕ}
    (R : CriticalRecordSkeleton m) : AdmissibleProfile m :=
  R.profile

/-- canonical anchor `1` は terminal より手前。従って幅は 2 以上。 -/
theorem one_lt_width
    {m : ℕ}
    (R : CriticalRecordSkeleton m) :
    1 < m := by
  simpa [initialRoofAnchor] using R.realizes.anchor_roof.lt_width

/-- canonical anchor は critical roof 上。 -/
theorem initial_anchor_roof
    {m : ℕ}
    (R : CriticalRecordSkeleton m) :
    IsRoofCut R.profile.1 initialRoofAnchor :=
  R.realizes.anchor_roof

/-- skeleton は anchor `1` から terminal まで exact に覆う。 -/
theorem one_add_totalLength_eq_terminal
    {m : ℕ}
    (R : CriticalRecordSkeleton m) :
    1 + R.skeleton.totalLength = m := by
  simpa [initialRoofAnchor] using
    R.realizes.anchor_add_totalLength_eq_terminal

/-- terminal rank は canonical anchor rank より strict に低い。 -/
theorem terminal_rank_lt_anchor_rank
    {m : ℕ}
    (R : CriticalRecordSkeleton m) :
    profileChordRank R.profile.1 m <
      profileChordRank R.profile.1 initialRoofAnchor := by
  have hDrop := R.skeleton.end_drop_of_realizesFrom
    R.realizes.record_realization
    R.realizes.lengths_nonempty
  rw [R.realizes.anchor_add_totalLength_eq_terminal] at hDrop
  exact hDrop

/-- terminal rank が 0 なので canonical anchor rank は strict に正。 -/
theorem anchor_rank_pos
    {m : ℕ}
    (R : CriticalRecordSkeleton m) :
    0 < profileChordRank R.profile.1 initialRoofAnchor := by
  have h := R.terminal_rank_lt_anchor_rank
  simpa using h

/-- general anchored packet への忘却。 -/
def toAnchored
    {m : ℕ}
    (R : CriticalRecordSkeleton m) : AnchoredCriticalRecordSkeleton m where
  profile := R.profile
  anchor := initialRoofAnchor
  skeleton := R.skeleton
  realizes := R.realizes

end CriticalRecordSkeleton

end Critical
end Collatz3
