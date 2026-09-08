import CollatzLean.Collatz3.Critical.RecordLocalGeometry
import CollatzLean.Collatz3.Critical.RecordRankArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3: terminal record block の minimality

`TerminalMinimalFrom` は完成した `RecordFerrers` の field ではなく、
前段の局所幾何で一時的に使っている補助 predicate である。

ここでは width `m > 2` に対し

* `CriticalRecordSkeleton`,
* `IsBestUpperWidth m`

だけから最後の block の minimal depth が自動的に従うことを示す。
`m = 2` は実際に退化例なので、`2 < m` は意図的な小幅除外である。
-/

namespace Collatz3
namespace Critical

/-- roof cut では integer chord rank は natural `criticalStripWidth` と一致する。 -/
theorem profileChordRank_eq_criticalStripWidth_of_roof
    {m : ℕ}
    {h : Profile m}
    {a : ℕ}
    (R : IsRoofCut h a) :
    profileChordRank h a = (criticalStripWidth m a : ℤ) := by
  have hm : 0 < m := lt_trans R.pos R.lt_width
  have hLower :=
    beattyIndex_below_criticalChord
      (m := m) (r := a) hm R.pos
  have hCut : cutDepth h a = beattyIndex a := by
    calc
      cutDepth h a = profileHeight h a := by
        simp [cutDepth_of_lt, profileHeight_of_lt, R.lt_width]
      _ = beattyIndex a := R.height_eq
  have hSub :
      criticalStripWidth m a + m * beattyIndex a =
        criticalTwoDepth m * a := by
    unfold criticalStripWidth
    exact Nat.sub_add_cancel (Nat.le_of_lt hLower)
  have hSubZ :
      (criticalStripWidth m a : ℤ) +
          (m : ℤ) * (beattyIndex a : ℤ) =
        (criticalTwoDepth m : ℤ) * (a : ℤ) := by
    exact_mod_cast hSub
  unfold profileChordRank
  rw [hCut]
  linarith

/--
`a+r=m` かつ terminal Beatty carry が `1` なら、二つの strip width の和は exact に `2m`。
-/
theorem criticalStripWidth_add_eq_two_mul_of_terminal_carry_one
    {m a r : ℕ}
    (haPos : 0 < a)
    (hrPos : 0 < r)
    (hTerminal : a + r = m)
    (hCarry : beattyCarry a r = 1) :
    criticalStripWidth m a + criticalStripWidth m r = 2 * m := by
  have hm : 0 < m := by omega
  have hLowerA :=
    beattyIndex_below_criticalChord
      (m := m) (r := a) hm haPos
  have hLowerR :=
    beattyIndex_below_criticalChord
      (m := m) (r := r) hm hrPos
  have hSubA :
      criticalStripWidth m a + m * beattyIndex a =
        criticalTwoDepth m * a := by
    unfold criticalStripWidth
    exact Nat.sub_add_cancel (Nat.le_of_lt hLowerA)
  have hSubR :
      criticalStripWidth m r + m * beattyIndex r =
        criticalTwoDepth m * r := by
    unfold criticalStripWidth
    exact Nat.sub_add_cancel (Nat.le_of_lt hLowerR)
  have hBeatty := beattyIndex_add_eq a r
  rw [hCarry] at hBeatty
  have hHm :
      criticalTwoDepth m = beattyIndex a + beattyIndex r + 2 := by
    unfold criticalTwoDepth
    rw [← hTerminal]
    omega
  have hTotal :
      criticalTwoDepth m * a + criticalTwoDepth m * r =
        criticalTwoDepth m * m := by
    rw [← Nat.mul_add, hTerminal]
  have hRoofTotal :
      m * beattyIndex a + m * beattyIndex r =
        m * (beattyIndex a + beattyIndex r) := by ring
  have hTerminalDepth :
      criticalTwoDepth m * m =
        m * (beattyIndex a + beattyIndex r) + 2 * m := by
    rw [hHm]
    ring
  omega

/--
最後の singleton record block では、best-upper と start-rank `< m` から
terminal carry `0` が強制される。
-/
theorem terminal_beattyCarry_eq_zero_of_bestUpper
    {m : ℕ}
    {h : Profile m}
    (Best : IsBestUpperWidth m)
    {a r : ℕ}
    (hStartRoof : IsRoofCut h a)
    (hTerminal : a + r = m)
    (hrPos : 0 < r)
    (hRankLt : profileChordRank h a < (m : ℤ)) :
    beattyCarry a r = 0 := by
  have hrLt : r < m := by
    have haPos := hStartRoof.pos
    omega
  have haLt : a < m := hStartRoof.lt_width
  have hCases := beattyCarry_eq_zero_or_one a r
  rcases hCases with hZero | hOne
  · exact hZero
  · have hSum :=
      criticalStripWidth_add_eq_two_mul_of_terminal_carry_one
        hStartRoof.pos hrPos hTerminal hOne
    have hA := Best.criticalStripWidth_le hStartRoof.pos haLt
    have hR := Best.criticalStripWidth_le hrPos hrLt
    have hStripA : criticalStripWidth m a = m := by omega
    have hRankEq := profileChordRank_eq_criticalStripWidth_of_roof hStartRoof
    rw [hRankEq, hStripA] at hRankLt
    exact False.elim (by omega)

/--
terminal singleton block の local depth は best-upper の下で minimal critical depthになる。
-/
theorem terminal_localDepth_eq_criticalTwoDepth_of_bestUpper
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (Best : IsBestUpperWidth m)
    {a r : ℕ}
    (B : Combinatorics.IsRecordBlock (profileChordRank h) a r)
    (hStartRoof : IsRoofCut h a)
    (hTerminal : a + r = m)
    (hRankLt : profileChordRank h a < (m : ℤ)) :
    localDepth h a r = criticalTwoDepth r := by
  have hrPos := B.length_pos
  have hEndLe : a + r ≤ m := Nat.le_of_eq hTerminal
  have hDepthAdd := profileHeight_add_localDepth A hEndLe
  have hStart := hStartRoof.height_eq
  have hTerminalHeight : profileHeight h (a + r) = criticalTwoDepth m := by
    rw [hTerminal]
    exact profileHeight_terminal h
  have hLocal :
      beattyIndex a + localDepth h a r = criticalTwoDepth m := by
    simpa [hStart, hTerminalHeight] using hDepthAdd
  have hCarryZero :=
    terminal_beattyCarry_eq_zero_of_bestUpper
      Best hStartRoof hTerminal hrPos hRankLt
  have hBeatty := beattyIndex_add_eq a r
  rw [hCarryZero, Nat.add_zero, hTerminal] at hBeatty
  unfold criticalTwoDepth at hLocal ⊢
  omega

/--
roof record chain の start rank が `m` 未満なら、best-upper により最後の block は自動 minimal。
-/
theorem terminalMinimalFrom_of_bestUpper
    {m : ℕ}
    {h : Profile m}
    (A : Admissible h)
    (Best : IsBestUpperWidth m) :
    ∀ (a : ℕ) (rs : List ℕ),
      IsRoofCut h a →
      RoofRecordSkeleton.RealizesBlocksFrom h a rs →
      profileChordRank h a < (m : ℤ) →
      TerminalMinimalFrom h a rs
  | _a, [], _hRoof, hFalse, _hRank => False.elim hFalse
  | a, [r], hRoof, hOne, hRank => by
      exact terminal_localDepth_eq_criticalTwoDepth_of_bestUpper
        A Best hOne.1 hRoof hOne.2 hRank
  | a, r :: s :: rs, hRoof, hMany, hRank => by
      have hNextRoof := hMany.2.1
      have hNextRank :
          profileChordRank h (a + r) < (m : ℤ) :=
        lt_trans hMany.1.end_drop hRank
      exact terminalMinimalFrom_of_bestUpper
        A Best (a + r) (s :: rs)
        hNextRoof hMany.2.2 hNextRank

namespace CriticalRecordSkeleton

/--
`m>2` の critical record skeleton では best-upper だけから terminal minimality が従う。
-/
theorem terminalMinimal_of_bestUpper
    {m : ℕ}
    (R : CriticalRecordSkeleton m)
    (Best : IsBestUpperWidth m)
    (hm : 2 < m) :
    TerminalMinimalFrom
      R.profile.1 initialRoofAnchor R.skeleton.lengths := by
  have hAnchorRank :=
    profileChordRank_initialRoofAnchor_lt_width R.profile.2 hm
  exact terminalMinimalFrom_of_bestUpper
    R.profile.2 Best
    initialRoofAnchor R.skeleton.lengths
    R.realizes.anchor_roof R.realizes.2 hAnchorRank

/--
`m>2` では `CriticalRecordSkeleton + IsBestUpperWidth` から
全 block の local critical geometry が一括して導かれる。
-/
theorem localCriticalBlocks_of_bestUpper
    {m : ℕ}
    (R : CriticalRecordSkeleton m)
    (Best : IsBestUpperWidth m)
    (hm : 2 < m) :
    LocalCriticalBlocksFrom
      R.profile.1 initialRoofAnchor R.skeleton.lengths := by
  exact localCriticalBlocksFrom_of_bestUpper
    R.profile.2 Best
    initialRoofAnchor R.skeleton.lengths
    R.realizes.anchor_roof R.realizes.2
    (R.terminalMinimal_of_bestUpper Best hm)

end CriticalRecordSkeleton

end Critical
end Collatz3
