import CollatzLean.Collatz3.Critical.RoofAnchor
import CollatzLean.Collatz3.Critical.Ferrers

/-!
# Collatz3: weak canonical record view

これは強い `Critical.RecordFerrers` とは別物である。

任意の admissible profile に deterministic な record-low cut list を付けるだけの
**弱い view** をここに置く。profile と完全同値にできるのはこちらであり、
local minimal block や roof-return geometry を含む強い Record--Ferrers ではない。

また record 判定は canonical anchor `1` より後だけで行い、比較集合には anchor 自身を
含める。したがって旧 `properRecordCuts` のように `k=1` が vacuous に record と判定される
ことはない。
-/

namespace Collatz3
namespace Ferrers

open Critical

/--
anchor より後の cut `k` が、anchor から `k-1` までの全 rank より strict に低い。
-/
def IsRecordCutAfter
    {m : ℕ}
    (h : Profile m)
    (anchor k : ℕ) : Prop :=
  anchor < k ∧
    k < m ∧
    ∀ j : ℕ, anchor ≤ j → j < k →
      profileChordRank h k < profileChordRank h j

/-- 指定 anchor より後の deterministic record cut list。 -/
noncomputable def recordCutsAfter
    {m : ℕ}
    (h : Profile m)
    (anchor : ℕ) : List ℕ := by
  classical
  exact (List.range m).filter (fun k => IsRecordCutAfter h anchor k)

/-- record cut list の membership specification。 -/
theorem mem_recordCutsAfter_iff
    {m : ℕ}
    {h : Profile m}
    {anchor k : ℕ} :
    k ∈ recordCutsAfter h anchor ↔
      k < m ∧ IsRecordCutAfter h anchor k := by
  classical
  simp [recordCutsAfter]

/-- canonical positive anchor `1` より後だけを見る record cut list。 -/
noncomputable def initialRecordCuts
    {m : ℕ}
    (h : Profile m) : List ℕ :=
  recordCutsAfter h initialRoofAnchor

/-- canonical view の cut は必ず `1` より後。 -/
theorem initialRecordCut_gt_anchor
    {m : ℕ}
    {h : Profile m}
    {k : ℕ}
    (hk : k ∈ initialRecordCuts h) :
    initialRoofAnchor < k := by
  change k ∈ recordCutsAfter h initialRoofAnchor at hk
  have hSpec := (mem_recordCutsAfter_iff).1 hk
  exact hSpec.2.1

/--
任意の admissible profile に canonical record-low decoration を付けた弱い view。
`cuts` は profile から一意に導かれ、追加の幾何自由度を持たない。
-/
structure RecordView (m : ℕ) where
  profile : AdmissibleProfile m
  cuts : List ℕ
  cuts_eq : cuts = initialRecordCuts profile.1

namespace RecordView

/-- weak view から underlying profile を忘却する。 -/
def forget
    {m : ℕ}
    (R : RecordView m) : AdmissibleProfile m :=
  R.profile

/-- profile に deterministic cut decoration を付ける。 -/
noncomputable def ofProfile
    {m : ℕ}
    (H : AdmissibleProfile m) : RecordView m where
  profile := H
  cuts := initialRecordCuts H.1
  cuts_eq := rfl

@[simp] theorem forget_ofProfile
    {m : ℕ}
    (H : AdmissibleProfile m) :
    (ofProfile H).forget = H :=
  rfl

end RecordView

/--
finite admissible profile と weak canonical `RecordView` は exact `Equiv`。
この theorem は強い `Critical.RecordFerrers` との同値を主張しない。
-/
noncomputable def admissibleProfileEquivRecordView
    (m : ℕ) :
    AdmissibleProfile m ≃ RecordView m where
  toFun H := RecordView.ofProfile H
  invFun R := R.forget
  left_inv H := by
    rfl
  right_inv R := by
    cases R with
    | mk profile cuts hCuts =>
        cases hCuts
        rfl

end Ferrers
end Collatz3
