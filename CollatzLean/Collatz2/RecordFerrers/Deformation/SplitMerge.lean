import CollatzLean.Collatz2.RecordFerrers.Deformation.BlockReplacement

/-!
# Record–Ferrers Phase A: split / merge as record-wall crossing

split / merge を primitive deformation とせず、fixed-chord bridge が intermediate
record wall を横切る現象として定式化する。minimal block category 内で endpoint を
保ったまま split / merge できる算術 permission bit は `criticalCarry = 1` になる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- 長さ `r` の minimal FirstCrossing block が持つ terminal depth。 -/
def minimalDepth (r : ℕ) : ℕ :=
  criticalHeight r + 1

/-- two-block と one-block の minimal depth が一致する iff local carry = 1。 -/
theorem minimalDepth_add_iff_criticalCarry_one
    (r s : ℕ) :
    minimalDepth (r + s) = minimalDepth r + minimalDepth s ↔
      criticalCarry r s = 1 := by
  have hCrit := criticalHeight_add_eq r s
  unfold minimalDepth
  constructor <;> intro h
  · omega
  · rw [h] at hCrit
    omega

/-- `criticalCarry = 1` を minimal split/merge compatibility と読む。 -/
def MergeCompatible (r s : ℕ) : Prop :=
  criticalCarry r s = 1

/-- adjacent interior blocks は local length pair 自身でも merge-compatible。 -/
theorem mergeCompatible_of_two_interior_carries
    (a r s : ℕ)
    (hAR : criticalCarry a r = 1)
    (hRS : criticalCarry (a + r) s = 1) :
    MergeCompatible r s ∧ criticalCarry a (r + s) = 1 := by
  have hCocycle := criticalCarry_cocycle a r s
  have hLocalLe := criticalCarry_le_one r s
  have hOuterLe := criticalCarry_le_one a (r + s)
  unfold MergeCompatible
  rw [hAR, hRS] at hCocycle
  omega

/-- split は source interior-above point が target で below へ移る wall crossing。 -/
def IsSplitAt
    {p H : ℕ}
    (u v : FiberPoint p H)
    (anchor cut : ℕ) : Prop :=
  SplitWallCrossing u v anchor cut

/-- merge は source below point が target interior-above へ戻る wall crossing。 -/
def IsMergeAt
    {p H : ℕ}
    (u v : FiberPoint p H)
    (anchor cut : ℕ) : Prop :=
  MergeWallCrossing u v anchor cut

/-- fixed anchor で split が起きる exact displacement threshold。 -/
theorem splitAt_iff_threshold
    {p H : ℕ}
    (u v : FiberPoint p H)
    (anchor cut : ℕ)
    (hAnchor : profileDisplacement u v anchor = 0)
    (hSourceAbove : AboveAnchor u anchor cut) :
    IsSplitAt u v anchor cut ↔
      rankGap u anchor cut <
        (p : ℤ) * profileDisplacement u v cut := by
  unfold IsSplitAt SplitWallCrossing
  rw [belowAnchor_iff_of_anchor_fixed u v anchor cut hAnchor]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hSourceAbove, h⟩

/-- fixed anchor で merge が起きる exact displacement threshold。 -/
theorem mergeAt_iff_threshold
    {p H : ℕ}
    (u v : FiberPoint p H)
    (anchor cut : ℕ)
    (hAnchor : profileDisplacement u v anchor = 0)
    (hSourceBelow : BelowAnchor u anchor cut) :
    IsMergeAt u v anchor cut ↔
      (p : ℤ) * profileDisplacement u v cut <
        rankGap u anchor cut := by
  unfold IsMergeAt MergeWallCrossing
  rw [aboveAnchor_iff_of_anchor_fixed u v anchor cut hAnchor]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨hSourceBelow, h⟩

/-- block replacement の内部で起きる split は endpoint rank を変えない。 -/
theorem split_preserves_block_endpoint
    {p H start stop cut : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop)
    (_hSplit : IsSplitAt u v start cut) :
    rankGap v start stop = rankGap u start stop :=
  R.rankGap_endpoints

/-- block replacement の内部で起きる merge も endpoint rank を変えない。 -/
theorem merge_preserves_block_endpoint
    {p H start stop cut : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop)
    (_hMerge : IsMergeAt u v start cut) :
    rankGap v start stop = rankGap u start stop :=
  R.rankGap_endpoints

end RecordFerrers
end Collatz2
