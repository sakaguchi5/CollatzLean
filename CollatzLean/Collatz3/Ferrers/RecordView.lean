import CollatzLean.Collatz3.Critical.RoofAnchor
import CollatzLean.Collatz3.Critical.Ferrers

/-!
# Collatz3: weak canonical record view

任意の admissible profile に deterministic な record-low cut list を付けるだけの
**弱い view** をここに置く。profile と完全同値にできるのはこちらである。

これは `Critical.CriticalRecordSkeleton` とも full `Critical.RecordFerrers` とも別物である。

* `RecordView`: deterministic strict record-low cuts の decoration。
* `CriticalRecordSkeleton`: roof-return を含む genuine strict excursion skeleton。
* `RecordFerrers`: skeleton の各 block が local critical geometry を持つ層。

record 判定は canonical anchor `1` より後だけで行い、比較集合には anchor 自身を含める。
そのため `k=1` が比較対象なしで record と判定されることはない。

record 判定自体を有限型 `Fin k` 上で書くので、cut list 抽出は classical choice を必要とせず
通常の計算として実行できる。
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
    ∀ j : Fin k,
      anchor ≤ j.1 →
        profileChordRank h k < profileChordRank h j.1

/-- `IsRecordCutAfter` は有限比較だけなので computable に判定できる。 -/
instance instDecidableIsRecordCutAfter
    {m : ℕ}
    (h : Profile m)
    (anchor k : ℕ) :
    Decidable (IsRecordCutAfter h anchor k) := by
  unfold IsRecordCutAfter
  infer_instance

/-- `Fin k` 版の有限定義を通常の自然数区間で読む仕様定理。 -/
theorem isRecordCutAfter_iff
    {m : ℕ}
    {h : Profile m}
    {anchor k : ℕ} :
    IsRecordCutAfter h anchor k ↔
      anchor < k ∧
      k < m ∧
      ∀ j : ℕ,
        anchor ≤ j →
        j < k →
          profileChordRank h k < profileChordRank h j := by
  constructor
  · intro H
    refine ⟨H.1, H.2.1, ?_⟩
    intro j haj hjk
    exact H.2.2 ⟨j, hjk⟩ haj
  · intro H
    refine ⟨H.1, H.2.1, ?_⟩
    intro j haj
    exact H.2.2 j.1 haj j.2

/-- 指定 anchor より後の deterministic record cut list。 -/
def recordCutsAfter
    {m : ℕ}
    (h : Profile m)
    (anchor : ℕ) : List ℕ :=
  (List.range m).filter (fun k => IsRecordCutAfter h anchor k)

/-- record cut list の membership specification。 -/
theorem mem_recordCutsAfter_iff
    {m : ℕ}
    {h : Profile m}
    {anchor k : ℕ} :
    k ∈ recordCutsAfter h anchor ↔
      k < m ∧ IsRecordCutAfter h anchor k := by
  simp [recordCutsAfter]

/-- canonical positive anchor `1` より後だけを見る record cut list。 -/
def initialRecordCuts
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

/-- profile に computable な deterministic cut decoration を付ける。 -/
def ofProfile
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
cut 抽出が有限計算なので、この `Equiv` 自体も computable。

この theorem は `CriticalRecordSkeleton` や full `RecordFerrers` との同値を主張しない。
-/
def admissibleProfileEquivRecordView
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
