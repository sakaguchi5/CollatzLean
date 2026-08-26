import CollatzLean.Collatz2.RecordFerrers.Lattice.UniversalFirstCrossingFiber

/-!
# Record–Ferrers RF-B0: 制約輸送の証明書

既存数学から得た情報を Record–Ferrers、word、さらに上位の軌道幾何へ戻す際に、
「何が完全に決まり、何が必要条件としてだけ戻るか」を区別するための薄い共通語彙。

完全復元そのものを要求せず、目的の性質・数値だけが圧縮情報から決まる場合も
正式な証明書として扱えるようにする。
-/

namespace Collatz2
namespace RecordFerrers
namespace Transport

universe u v w

/--
情報写像 `info` が性質 `P` を決定すること。
同じ情報を持つ二対象では `P` の真偽が一致する。
-/
def DeterminesProp
    {α : Type u}
    {β : Type v}
    (info : α → β)
    (P : α → Prop) : Prop :=
  ∀ ⦃x y : α⦄, info x = info y → (P x ↔ P y)

/--
情報写像 `info` が量 `q` を決定すること。
元の対象全体を復元できなくても、必要な量だけが一意ならこの証明書で十分。
-/
def DeterminesValue
    {α : Type u}
    {β : Type v}
    {γ : Type w}
    (info : α → β)
    (q : α → γ) : Prop :=
  ∀ ⦃x y : α⦄, info x = info y → q x = q y

/--
元の性質 `P` が成り立つ対象は、圧縮先で必ず条件 `Q` を満たす。
矛盾を引き戻すだけなら、この片方向で十分。
-/
def PullsBackConstraint
    {α : Type u}
    {β : Type v}
    (info : α → β)
    (P : α → Prop)
    (Q : β → Prop) : Prop :=
  ∀ x, P x → Q (info x)

/-- 元の性質と圧縮先の条件が対象ごとに完全同値であること。 -/
def ExactTranslation
    {α : Type u}
    {β : Type v}
    (info : α → β)
    (P : α → Prop)
    (Q : β → Prop) : Prop :=
  ∀ x, P x ↔ Q (info x)

/-- 値決定証明書は合成できる。 -/
theorem DeterminesValue.comp
    {α : Type u}
    {β : Type v}
    {γ : Type w}
    {δ : Type*}
    {i : α → β}
    {j : α → γ}
    {q : α → δ}
    (hij : DeterminesValue i j)
    (hjq : DeterminesValue j q) :
    DeterminesValue i q := by
  intro x y hxy
  exact hjq (hij hxy)

/-- 性質決定証明書は、同じ中間情報を通して合成できる。 -/
theorem DeterminesProp.of_value
    {α : Type u}
    {β : Type v}
    {γ : Type w}
    {i : α → β}
    {j : α → γ}
    {P : γ → Prop}
    (hij : DeterminesValue i j) :
    DeterminesProp i (fun x => P (j x)) := by
  intro x y hxy
  change P (j x) ↔ P (j y)
  rw [hij hxy]

/-- 完全翻訳から片方向の制約引き戻しを得る。 -/
theorem ExactTranslation.toPullsBackConstraint
    {α : Type u}
    {β : Type v}
    {info : α → β}
    {P : α → Prop}
    {Q : β → Prop}
    (h : ExactTranslation info P Q) :
    PullsBackConstraint info P Q := by
  intro x hx
  exact (h x).1 hx

/--
圧縮先の条件 `Q` を満たす情報が一つもなければ、
`P` を満たす元対象も一つも存在しない。
-/
theorem impossible_of_pulled_constraint
    {α : Type u}
    {β : Type v}
    {info : α → β}
    {P : α → Prop}
    {Q : β → Prop}
    (hPull : PullsBackConstraint info P Q)
    (hNo : ∀ z : β, ¬ Q z) :
    ∀ x : α, ¬ P x := by
  intro x hx
  exact hNo (info x) (hPull x hx)

/--
完全翻訳の先で `Q` が不可能なら、元の `P` も不可能。
外部数学の不存在定理を元側へ戻す基本形。
-/
theorem impossible_of_exact_translation
    {α : Type u}
    {β : Type v}
    {info : α → β}
    {P : α → Prop}
    {Q : β → Prop}
    (hExact : ExactTranslation info P Q)
    (hNo : ∀ z : β, ¬ Q z) :
    ∀ x : α, ¬ P x :=
  impossible_of_pulled_constraint hExact.toPullsBackConstraint hNo

end Transport
end RecordFerrers
end Collatz2
