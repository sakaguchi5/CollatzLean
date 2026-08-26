import CollatzLean.Collatz2.RecordFerrers.Record.RecordWalls

/-!
# Record–Ferrers Phase A: interval depth transfer

fixed-chord deformation の displacement bridge が一区間上で一定になる場合を切り出す。
1-cell swap の long-range / mesoscopic 版として扱う。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/--
source `u` から target `v` への interval transfer。
`left < k ≤ right` で displacement が `amount`、外では 0。
-/
structure IntervalTransfer
    {p H : ℕ}
    (u v : FiberPoint p H)
    (left right amount : ℕ) : Prop where
  left_lt_right : left < right
  right_lt_terminal : right < p
  inside :
    ∀ k : ℕ,
      left < k →
      k ≤ right →
      profileDisplacement u v k = (amount : ℤ)
  outside :
    ∀ k : ℕ,
      k ≤ p →
      (k ≤ left ∨ right < k) →
      profileDisplacement u v k = 0

namespace IntervalTransfer

/-- left anchor は固定される。 -/
theorem displacement_left
    {p H left right amount : ℕ}
    {u v : FiberPoint p H}
    (T : IntervalTransfer u v left right amount) :
    profileDisplacement u v left = 0 := by
  apply T.outside left
  · have hLeftLtP : left < p :=
      T.left_lt_right.trans T.right_lt_terminal
    omega
  · exact Or.inl le_rfl

/-- right endpoint では amount 分だけ上がる。 -/
theorem displacement_right
    {p H left right amount : ℕ}
    {u v : FiberPoint p H}
    (T : IntervalTransfer u v left right amount) :
    profileDisplacement u v right = (amount : ℤ) := by
  exact T.inside right T.left_lt_right le_rfl

/-- interval 内の critical clearance は amount だけ減る。 -/
theorem criticalDefectInt_inside
    {p H left right amount : ℕ}
    {u v : FiberPoint p H}
    (T : IntervalTransfer u v left right amount)
    {k : ℕ}
    (hkLeft : left < k)
    (hkRight : k ≤ right) :
    criticalDefectInt v k =
      criticalDefectInt u k - (amount : ℤ) := by
  rw [criticalDefectInt_transport u v k, T.inside k hkLeft hkRight]

/-- interval 内の chord rank は `p*amount` だけ下がる。 -/
theorem chordRankInt_inside
    {p H left right amount : ℕ}
    {u v : FiberPoint p H}
    (T : IntervalTransfer u v left right amount)
    {k : ℕ}
    (hkLeft : left < k)
    (hkRight : k ≤ right) :
    chordRankInt v.word k =
      chordRankInt u.word k - (p : ℤ) * (amount : ℤ) := by
  rw [chordRankInt_transport u v k, T.inside k hkLeft hkRight]

/-- interval 外の critical clearance は不変。 -/
theorem criticalDefectInt_outside
    {p H left right amount : ℕ}
    {u v : FiberPoint p H}
    (T : IntervalTransfer u v left right amount)
    {k : ℕ}
    (hk : k ≤ p)
    (hOutside : k ≤ left ∨ right < k) :
    criticalDefectInt v k = criticalDefectInt u k := by
  rw [criticalDefectInt_transport u v k, T.outside k hk hOutside]
  ring

/-- interval 外の chord rank は不変。 -/
theorem chordRankInt_outside
    {p H left right amount : ℕ}
    {u v : FiberPoint p H}
    (T : IntervalTransfer u v left right amount)
    {k : ℕ}
    (hk : k ≤ p)
    (hOutside : k ≤ left ∨ right < k) :
    chordRankInt v.word k = chordRankInt u.word k := by
  rw [chordRankInt_transport u v k, T.outside k hk hOutside]
  ring

/-- source FirstCrossing の proper cut clearance は nonnegative。 -/
private theorem source_clearance_nonneg
    {p H : ℕ}
    {u : FiberPoint p H}
    (hFu : FirstCrossing u.word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < p) :
    0 ≤ criticalDefectInt u k := by
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

/--
interval 内で amount が source clearance を越えなければ FirstCrossing は保存される。
外側は displacement 0 なので自動で安全。
-/
theorem preserves_firstCrossing
    {p H left right amount : ℕ}
    {u v : FiberPoint p H}
    (T : IntervalTransfer u v left right amount)
    (hFu : FirstCrossing u.word)
    (hClear :
      ∀ k : ℕ,
        left < k →
        k ≤ right →
        (amount : ℤ) ≤ criticalDefectInt u k) :
    FirstCrossing v.word := by
  apply (firstCrossing_iff_displacement_le_clearance u v hFu).2
  intro k hkPos hkLt
  by_cases hInside : left < k ∧ k ≤ right
  · rw [T.inside k hInside.1 hInside.2]
    exact hClear k hInside.1 hInside.2
  · have hOutside : k ≤ left ∨ right < k := by
      omega
    rw [T.outside k (Nat.le_of_lt hkLt) hOutside]
    exact source_clearance_nonneg hFu hkPos hkLt

/-- FirstCrossing 同士の interval transfer は rank residue を保存する。 -/
theorem rankResidue_invariant_of_firstCrossing
    {p H left right amount : ℕ}
    {u v : FiberPoint p H}
    (_T : IntervalTransfer u v left right amount)
    (hFu : FirstCrossing u.word)
    (hFv : FirstCrossing v.word)
    {k : ℕ}
    (hk : k < p) :
    rankResidue u.word k = rankResidue v.word k :=
  RecordFerrers.rankResidue_invariant u v hFu hFv hk

end IntervalTransfer

end RecordFerrers
end Collatz2
