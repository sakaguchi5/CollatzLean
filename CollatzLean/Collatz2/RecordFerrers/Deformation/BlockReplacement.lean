import CollatzLean.Collatz2.RecordFerrers.Deformation.IntervalTransfer

/-!
# Record–Ferrers Phase A: block replacement

二つの fixed-chord paths が同じ block anchors を共有し、差がその block 内部にだけ
support を持つ場合を compact-support deformation として切り出す。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
`start` と `stop` を固定し、displacement が open interval `(start,stop)` の外で 0。
同じ二つの anchors を結ぶ subpath replacement の pure definition。
-/
structure BlockReplacement
    {p H : ℕ}
    (u v : FiberPoint p H)
    (start stop : ℕ) : Prop where
  start_lt_stop : start < stop
  stop_le_terminal : stop ≤ p
  outside :
    ∀ k : ℕ,
      k ≤ p →
      (k ≤ start ∨ stop ≤ k) →
      profileDisplacement u v k = 0

namespace BlockReplacement

/-- start anchor は固定。 -/
theorem displacement_start
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop) :
    profileDisplacement u v start = 0 := by
  apply R.outside start
  · exact Nat.le_trans
      (Nat.le_of_lt R.start_lt_stop)
      R.stop_le_terminal
  · exact Or.inl le_rfl

/-- stop anchor も固定。 -/
theorem displacement_stop
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop) :
    profileDisplacement u v stop = 0 := by
  apply R.outside stop R.stop_le_terminal
  exact Or.inr le_rfl

/-- replacement の両 anchor heights は不変。 -/
theorem height_start
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop) :
    u.height start = v.height start := by
  have h := R.displacement_start
  unfold profileDisplacement at h
  exact_mod_cast (sub_eq_zero.mp h).symm

/-- replacement の右 anchor height も不変。 -/
theorem height_stop
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop) :
    u.height stop = v.height stop := by
  have h := R.displacement_stop
  unfold profileDisplacement at h
  exact_mod_cast (sub_eq_zero.mp h).symm

/-- block 外の rank は完全に不変。 -/
theorem chordRankInt_outside
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop)
    {k : ℕ}
    (hk : k ≤ p)
    (hOutside : k ≤ start ∨ stop ≤ k) :
    chordRankInt v.word k = chordRankInt u.word k := by
  rw [chordRankInt_transport u v k, R.outside k hk hOutside]
  ring

/-- block 外の critical clearance も不変。 -/
theorem criticalDefectInt_outside
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop)
    {k : ℕ}
    (hk : k ≤ p)
    (hOutside : k ≤ start ∨ stop ≤ k) :
    criticalDefectInt v k = criticalDefectInt u k := by
  rw [criticalDefectInt_transport u v k, R.outside k hk hOutside]
  ring

/-- start anchor 基準の rank gap transport は block 内 displacement だけを見る。 -/
theorem rankGap_from_start
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop)
    (k : ℕ) :
    rankGap v start k =
      rankGap u start k - (p : ℤ) * profileDisplacement u v k := by
  exact rankGap_transport_of_anchor_fixed
    u v start k R.displacement_start

/-- replacement endpoint 間の rank gap は不変。 -/
theorem rankGap_endpoints
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop) :
    rankGap v start stop = rankGap u start stop := by
  rw [R.rankGap_from_start stop, R.displacement_stop]
  ring

/-- source block endpoint が below なら replacement 後も below。 -/
theorem preserves_below_endpoint
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop)
    (hBelow : BelowAnchor u start stop) :
    BelowAnchor v start stop := by
  unfold BelowAnchor at hBelow ⊢
  rw [R.rankGap_endpoints]
  exact hBelow

/-- source block endpoint が above なら replacement 後も above。 -/
theorem preserves_above_endpoint
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop)
    (hAbove : AboveAnchor u start stop) :
    AboveAnchor v start stop := by
  unfold AboveAnchor at hAbove ⊢
  rw [R.rankGap_endpoints]
  exact hAbove

/--
block 内 displacement が source clearance 以下なら replacement は FirstCrossing を保つ。
-/
theorem preserves_firstCrossing
    {p H start stop : ℕ}
    {u v : FiberPoint p H}
    (R : BlockReplacement u v start stop)
    (hFu : FirstCrossing u.word)
    (hInside :
      ∀ k : ℕ,
        start < k →
        k < stop →
        profileDisplacement u v k ≤ criticalDefectInt u k) :
    FirstCrossing v.word := by
  apply (firstCrossing_iff_displacement_le_clearance u v hFu).2
  intro k hkPos hkLt
  by_cases hkInside : start < k ∧ k < stop
  · exact hInside k hkInside.1 hkInside.2
  · have hOutside : k ≤ start ∨ stop ≤ k := by
      omega
    rw [R.outside k (Nat.le_of_lt hkLt) hOutside]
    have hkWord : k < oddSteps u.word := by
      rw [u.oddSteps_eq]
      exact hkLt
    have hDepthRaw := hFu.prefixTwoDepth_le_criticalHeight hkPos hkWord
    have hDepth : u.height k ≤ criticalHeight k := by
      simpa [FiberPoint.height] using hDepthRaw
    have hDepthZ :
        (u.height k : ℤ) ≤ (criticalHeight k : ℤ) := by
      exact_mod_cast hDepth
    unfold criticalDefectInt
    exact sub_nonneg.mpr hDepthZ

end BlockReplacement

end RecordFerrers
end Collatz2
