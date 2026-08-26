import CollatzLean.Collatz2.RecordFerrers.Core.FixedChordFiber
import CollatzLean.Collatz2.Geometry.RankQuotient
import CollatzLean.Collatz2.Geometry.CriticalProfile

/-!
# Record–Ferrers Phase A: profile displacement

同じ `(p,H)` fiber 上の二点の差を、両端 0 の signed integer bridge として読む。
rank / critical defect / residue への transport をここで一度だけ証明する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- source `u` から target `v` への signed height displacement。 -/
def profileDisplacement
    {p H : ℕ}
    (u v : FiberPoint p H)
    (k : ℕ) : ℤ :=
  (v.height k : ℤ) - (u.height k : ℤ)

@[simp] theorem profileDisplacement_zero
    {p H : ℕ}
    (u v : FiberPoint p H) :
    profileDisplacement u v 0 = 0 := by
  simp [profileDisplacement]

@[simp] theorem profileDisplacement_terminal
    {p H : ℕ}
    (u v : FiberPoint p H) :
    profileDisplacement u v p = 0 := by
  simp [profileDisplacement]

/-- deformation composition は bridge の pointwise addition。 -/
theorem profileDisplacement_comp
    {p H : ℕ}
    (u v z : FiberPoint p H)
    (k : ℕ) :
    profileDisplacement u z k =
      profileDisplacement u v k + profileDisplacement v z k := by
  unfold profileDisplacement
  ring

/-- deformation inverse は bridge の符号反転。 -/
theorem profileDisplacement_symm
    {p H : ℕ}
    (u v : FiberPoint p H)
    (k : ℕ) :
    profileDisplacement v u k = - profileDisplacement u v k := by
  unfold profileDisplacement
  ring

/-- critical roof からの signed clearance。FirstCrossing 外でも truncation せず保持する。 -/
def criticalDefectInt
    {p H : ℕ}
    (x : FiberPoint p H)
    (k : ℕ) : ℤ :=
  (criticalHeight k : ℤ) - (x.height k : ℤ)

/-- arbitrary fixed-chord deformation の critical clearance transport。 -/
theorem criticalDefectInt_transport
    {p H : ℕ}
    (u v : FiberPoint p H)
    (k : ℕ) :
    criticalDefectInt v k =
      criticalDefectInt u k - profileDisplacement u v k := by
  unfold criticalDefectInt profileDisplacement
  ring

/--
fixed chord では signed chord rank の変化は exact に `-p * displacement`。
Record–Ferrers deformation の master rank identity。
-/
theorem chordRankInt_transport
    {p H : ℕ}
    (u v : FiberPoint p H)
    (k : ℕ) :
    chordRankInt v.word k =
      chordRankInt u.word k -
        (p : ℤ) * profileDisplacement u v k := by
  unfold chordRankInt profileDisplacement FiberPoint.height
  rw [u.oddSteps_eq, v.oddSteps_eq, u.twoSteps_eq, v.twoSteps_eq]
  ring

/-- FirstCrossing fixed-chord deformation は rank residue を変えない。 -/
theorem rankResidue_invariant
    {p H : ℕ}
    (u v : FiberPoint p H)
    (hFu : FirstCrossing u.word)
    (hFv : FirstCrossing v.word)
    {k : ℕ}
    (hk : k < p) :
    rankResidue u.word k = rankResidue v.word k := by
  by_cases hk0 : k = 0
  · subst k
    simp [
      rankResidue,
      chordRank,
      u.oddSteps_eq,
      v.oddSteps_eq
    ]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    have hkU : k < oddSteps u.word := by
      rw [u.oddSteps_eq]
      exact hk
    have hkV : k < oddSteps v.word := by
      rw [v.oddSteps_eq]
      exact hk
    rw [hFu.rankResidue_eq_stripRank_mod hkPos hkU,
        hFv.rankResidue_eq_stripRank_mod hkPos hkV]
    unfold stripRank
    rw [u.oddSteps_eq, v.oddSteps_eq, u.twoSteps_eq, v.twoSteps_eq]

/-- critical roof 以下の positive prefix は expanding。 -/
private theorem expanding_take_of_depth_le_criticalHeight
    (w : Word)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLe : k ≤ oddSteps w)
    (hDepth : prefixTwoDepth w k ≤ criticalHeight k) :
    Expanding (w.take k) := by
  have hPowLe :
      2 ^ prefixTwoDepth w k ≤ 2 ^ criticalHeight k :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hDepth
  have hCrit := criticalHeight_pow_lt_threePow hkPos
  have hPow : 2 ^ prefixTwoDepth w k < 3 ^ k :=
    lt_of_le_of_lt hPowLe hCrit
  have hTakeLen : (w.take k).length = k := by
    apply List.length_take_of_le
    simpa [oddSteps] using hkLe
  apply (expanding_iff_twoPow_lt_threePow).2
  simpa [prefixTwoDepth, oddSteps, hTakeLen] using hPow

/--
source が FirstCrossing のとき、target も FirstCrossing であるための exact bridge criterion。
proper cuts で displacement が source clearance を越えないことと同値。
-/
theorem firstCrossing_iff_displacement_le_clearance
    {p H : ℕ}
    (u v : FiberPoint p H)
    (hFu : FirstCrossing u.word) :
    FirstCrossing v.word ↔
      ∀ k : ℕ, 0 < k → k < p →
        profileDisplacement u v k ≤ criticalDefectInt u k := by
  constructor
  · intro hFv k hkPos hkLt
    have hkV : k < oddSteps v.word := by
      simpa [v.oddSteps_eq] using hkLt
    have hDepthVRaw := hFv.prefixTwoDepth_le_criticalHeight hkPos hkV
    have hDepthV : v.height k ≤ criticalHeight k := by
      simpa [FiberPoint.height] using hDepthVRaw
    have hDepthVZ :
        (v.height k : ℤ) ≤ (criticalHeight k : ℤ) := by
      exact_mod_cast hDepthV
    unfold profileDisplacement criticalDefectInt
    linarith
  · intro hClear
    refine {
      nonempty := ?_
      properPositive := ?_
      terminalNegative := ?_
    }
    · have hpPos : 0 < p := by
        have huLenPos : 0 < u.word.length :=
          List.length_pos_iff.mpr hFu.nonempty
        have huLen : u.word.length = p := by
          simpa [oddSteps] using u.oddSteps_eq
        omega
      apply List.ne_nil_of_length_pos
      have hvLen : v.word.length = p := by
        simpa [oddSteps] using v.oddSteps_eq
      omega
    · intro k hkPos hkLtLen
      have hkLt : k < p := by
        have : v.word.length = p := by
          simpa [oddSteps] using v.oddSteps_eq
        omega
      have hC := hClear k hkPos hkLt
      have hDepthZ :
          (v.height k : ℤ) ≤ (criticalHeight k : ℤ) := by
        unfold profileDisplacement criticalDefectInt at hC
        linarith
      have hDepth : v.height k ≤ criticalHeight k := by
        exact_mod_cast hDepthZ
      have hkWord : k < oddSteps v.word := by
        rw [v.oddSteps_eq]
        exact hkLt
      apply expanding_take_of_depth_le_criticalHeight
        v.word hkPos (Nat.le_of_lt hkWord)
      simpa [FiberPoint.height] using hDepth
    · have hPow :=
        (contracting_iff_threePow_lt_twoPow).1 hFu.terminalContracting
      apply (contracting_iff_threePow_lt_twoPow).2
      simpa [u.oddSteps_eq, v.oddSteps_eq,
        u.twoSteps_eq, v.twoSteps_eq] using hPow

end RecordFerrers
end Collatz2
