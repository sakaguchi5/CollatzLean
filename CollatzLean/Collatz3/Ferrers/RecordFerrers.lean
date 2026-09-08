import CollatzLean.Collatz3.Critical.WordProfileEquiv
import Mathlib.Tactic.Ring

/-!
# Collatz3: canonical Record--Ferrers view

Record 層では profile 自体を書き換えず、profile から **一意に導かれる**
proper record cuts を付加する。

ここで terminal cut `m` は strict record に含めない。
normalized rank は start と terminal で同じ 0 になるため、terminal は
最後の proper record から続く terminal tail として扱う。

従って `RecordFerrers m` は

  admissible profile + canonical proper-record decomposition

という view object であり、record skeleton だけが profile を決めるとは主張しない。
この区別によって、Profile <-> RecordFerrers は無理のない exact `Equiv` になる。
-/

namespace Collatz3
namespace Ferrers

open Critical

/--
critical chord `(m, criticalTwoDepth m)` に対する signed normalized rank。
`k ≤ m` で使う。terminal `k=m` では profileHeight が terminal depth を返す。
-/
def normalizedRank
    {m : ℕ}
    (h : Profile m)
    (k : ℕ) : ℤ :=
  (criticalTwoDepth m : ℤ) * (k : ℤ) -
    (m : ℤ) * (profileHeight h k : ℤ)

/-- positive width の admissible profile では start rank は 0。 -/
theorem normalizedRank_zero_of_admissible
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (hm : 0 < m) :
    normalizedRank h 0 = 0 := by
  rw [normalizedRank, profileHeight_zero A hm]
  simp

/-- terminal rank は常に 0。 -/
@[simp] theorem normalizedRank_terminal
    {m : ℕ}
    (h : Profile m) :
    normalizedRank h m = 0 := by
  rw [normalizedRank, profileHeight_terminal]
  ring

/--
proper index `k` が、それ以前の positive proper index 全体より strict に低い rank を持つ。
`k=0` と terminal `k=m` は record cut に含めない。
-/
def IsProperRecordCut
    {m : ℕ}
    (h : Profile m)
    (k : ℕ) : Prop :=
  0 < k ∧
  k < m ∧
  ∀ j : ℕ, 0 < j → j < k →
    normalizedRank h k < normalizedRank h j

/-- profile から deterministic に抽出する proper record cut 列。 -/
noncomputable def properRecordCuts
    {m : ℕ}
    (h : Profile m) : List ℕ := by
  classical
  exact (List.range m).filter (fun k => IsProperRecordCut h k)

/-- canonical cut list の membership specification。 -/
theorem mem_properRecordCuts_iff
    {m : ℕ}
    {h : Profile m}
    {k : ℕ} :
    k ∈ properRecordCuts h ↔
      k < m ∧ IsProperRecordCut h k := by
  classical
  simp [properRecordCuts]

/-- canonical record cut は必ず positive proper index。 -/
theorem properRecordCut_bounds
    {m : ℕ}
    {h : Profile m}
    {k : ℕ}
    (hk : k ∈ properRecordCuts h) :
    0 < k ∧ k < m := by
  have hSpec := (mem_properRecordCuts_iff).1 hk
  rcases hSpec with ⟨hkM, hRecord⟩
  exact ⟨hRecord.1, hkM⟩

/-- canonical list に入った cut は定義どおり strict record。 -/
theorem isProperRecordCut_of_mem
    {m : ℕ}
    {h : Profile m}
    {k : ℕ}
    (hk : k ∈ properRecordCuts h) :
    IsProperRecordCut h k :=
  ((mem_properRecordCuts_iff).1 hk).2

/--
Record--Ferrers view。
profile と、その profile から一意に導かれる proper record cut 列だけを持つ。
`cuts_eq` により decomposition に余分な選択自由度はない。
-/
structure RecordFerrers (m : ℕ) where
  profile : AdmissibleProfile m
  cuts : List ℕ
  cuts_eq : cuts = properRecordCuts profile.1

namespace RecordFerrers

/-- record cuts は canonical extractor の値そのもの。 -/
theorem cuts_eq_canonical
    {m : ℕ}
    (R : RecordFerrers m) :
    R.cuts = properRecordCuts R.profile.1 :=
  R.cuts_eq

/-- record view から underlying finite profile を忘却する。 -/
def forget
    {m : ℕ}
    (R : RecordFerrers m) : AdmissibleProfile m :=
  R.profile

/-- canonical decomposition を profile に付ける。 -/
noncomputable def ofProfile
    {m : ℕ}
    (H : AdmissibleProfile m) : RecordFerrers m where
  profile := H
  cuts := properRecordCuts H.1
  cuts_eq := rfl

@[simp] theorem forget_ofProfile
    {m : ℕ}
    (H : AdmissibleProfile m) :
    (ofProfile H).forget = H := by
  rfl

/--
同じ profile に付随する canonical cut list は一意。
旧 RecordDecomposition の「どの cut を選ぶか」という自由度をここで消している。
-/
theorem cuts_unique
    {m : ℕ}
    {H : AdmissibleProfile m}
    {cuts₁ cuts₂ : List ℕ}
    (h₁ : cuts₁ = properRecordCuts H.1)
    (h₂ : cuts₂ = properRecordCuts H.1) :
    cuts₁ = cuts₂ := by
  exact h₁.trans h₂.symm

end RecordFerrers

/--
finite admissible profile と canonical Record--Ferrers view は exact `Equiv`。
この同値は「profile に canonical decomposition を付ける／忘れる」の往復である。
-/
noncomputable def admissibleProfileEquivRecordFerrers
    (m : ℕ) :
    AdmissibleProfile m ≃ RecordFerrers m where
  toFun H := RecordFerrers.ofProfile H
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
