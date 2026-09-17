import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Collatz3 Arithmetic: anchor 付き極小消滅部分和

有限和

`∑ i in s, v i = 0`

の中で、指定した anchor を含むものを包含関係で極小化するための純粋な有限組合せ層。
S-unit や Collatz の意味論には依存しない。
-/

namespace Collatz3
namespace Arithmetic

open scoped BigOperators

/-- 有限 index 集合上の整数和が消える。 -/
def Vanishes
    {ι : Type*} [DecidableEq ι]
    (v : ι → ℤ)
    (s : Finset ι) : Prop :=
  Finset.sum s v = 0

/--
`anchor` を含む消滅部分和で、さらに小さい anchor 付き消滅部分和を持たない。
-/
structure AnchorMinimalVanishing
    {ι : Type*} [DecidableEq ι]
    (v : ι → ℤ)
    (anchor : ι)
    (s : Finset ι) : Prop where
  anchor_mem : anchor ∈ s
  sum_eq_zero : Vanishes v s
  minimal :
    ∀ t : Finset ι,
      t ⊆ s →
      anchor ∈ t →
      Vanishes v t →
      t = s

/--
任意の有限 anchor 付き消滅和から、anchor を含む極小消滅部分和を取れる。

`Nat.find` で cardinality を最小化するので、選択対象そのものを新しい primitive にしない。
-/
theorem exists_anchorMinimalVanishing
    {ι : Type*} [DecidableEq ι]
    (v : ι → ℤ)
    (anchor : ι)
    {s₀ : Finset ι}
    (hAnchor : anchor ∈ s₀)
    (hZero : Vanishes v s₀) :
    ∃ s : Finset ι,
      s ⊆ s₀ ∧
        AnchorMinimalVanishing v anchor s := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ s : Finset ι,
      s ⊆ s₀ ∧
        anchor ∈ s ∧
          Vanishes v s ∧
            s.card = n
  have hP : ∃ n : ℕ, P n := by
    refine ⟨s₀.card, s₀, (by intro x hx; exact hx), hAnchor, hZero, rfl⟩
  rcases Nat.find_spec hP with
    ⟨s, hs₀, hAnchorS, hZeroS, hCard⟩
  refine ⟨s, hs₀, ⟨hAnchorS, hZeroS, ?_⟩⟩
  intro t hts hAnchorT hZeroT
  by_contra hne
  have hStrict : t ⊂ s :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hts, hne⟩
  have hCardLt : t.card < s.card :=
    Finset.card_lt_card hStrict
  have hPt : P t.card := by
    exact ⟨t, hts.trans hs₀, hAnchorT, hZeroT, rfl⟩
  have hMin : Nat.find hP ≤ t.card :=
    Nat.find_min' hP hPt
  rw [← hCard] at hMin
  omega

namespace AnchorMinimalVanishing

/--
anchor 極小性は実は通常の nondegeneracy を与える。

anchor を含まない消滅部分和 `u` が存在すれば、補集合 `s \ u` が
より小さい anchor 付き消滅部分和になるため矛盾する。
-/
theorem no_nonempty_proper_vanishing
    {ι : Type*} [DecidableEq ι]
    {v : ι → ℤ} {anchor : ι} {s u : Finset ι}
    (h : AnchorMinimalVanishing v anchor s)
    (huSub : u ⊆ s)
    (huNonempty : u.Nonempty)
    (huNe : u ≠ s) :
    ¬ Vanishes v u := by
  intro hZeroU
  by_cases hAnchorU : anchor ∈ u
  · exact huNe (h.minimal u huSub hAnchorU hZeroU)
  · let t : Finset ι := s \ u
    have htSub : t ⊆ s := by
      exact Finset.sdiff_subset
    have hAnchorT : anchor ∈ t := by
      exact Finset.mem_sdiff.mpr ⟨h.anchor_mem, hAnchorU⟩
    have hZeroT : Vanishes v t := by
      have hSum := h.sum_eq_zero
      unfold Vanishes at hSum hZeroU ⊢
      rw [← Finset.sum_sdiff huSub] at hSum
      rw [hZeroU, add_zero] at hSum
      exact hSum
    have htNe : t ≠ s := by
      intro hEq
      rcases huNonempty with ⟨x, hxU⟩
      have hxS : x ∈ s := huSub hxU
      have hxT : x ∈ t := by
        rw [hEq]
        exact hxS
      exact (Finset.mem_sdiff.mp hxT).2 hxU
    exact htNe (h.minimal t htSub hAnchorT hZeroT)

end AnchorMinimalVanishing

/--
右辺を `1` に正規化した nondegenerate 有限和。

`no_zero_subsum` は ESS 型 S-unit 定理の nondegeneracy 条件に対応する。
-/
structure NondegenerateSumOne
    {ι : Type*} [DecidableEq ι]
    (v : ι → ℤ)
    (s : Finset ι) : Prop where
  sum_eq_one : Finset.sum s v = 1
  no_zero_subsum :
    ∀ u : Finset ι,
      u.Nonempty →
      u ⊆ s →
      (Finset.sum u v) ≠ 0

/--
極小消滅部分和から値 `-1` の項を一つ外すと、
nondegenerate な `sum = 1` 方程式が得られる。
-/
theorem AnchorMinimalVanishing.erase_neg_one
    {ι : Type*} [DecidableEq ι]
    {v : ι → ℤ} {anchor one : ι} {s : Finset ι}
    (h : AnchorMinimalVanishing v anchor s)
    (hOne : one ∈ s)
    (hValue : v one = -1) :
    NondegenerateSumOne v (s.erase one) := by
  constructor
  · have hDecomp := Finset.sum_erase_add s v hOne
    have hZero : Finset.sum s v = 0 := h.sum_eq_zero
    rw [hZero, hValue] at hDecomp
    have hAdd :=
      congrArg (fun z : ℤ => z + 1) hDecomp
    simpa using hAdd
  · intro u huNonempty huSub
    apply h.no_nonempty_proper_vanishing
    · exact huSub.trans (Finset.erase_subset one s)
    · exact huNonempty
    · intro hEq
      have hOneU : one ∈ u := by
        rw [hEq]
        exact hOne
      have hOneErase : one ∈ s.erase one := huSub hOneU
      simp at hOneErase

end Arithmetic
end Collatz3
