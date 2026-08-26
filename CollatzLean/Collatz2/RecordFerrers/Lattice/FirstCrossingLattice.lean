import CollatzLean.Collatz2.RecordFerrers.Lattice.FerrersFiber
import CollatzLean.Collatz2.Geometry.CriticalCarry

/-!
# Record–Ferrers Phase A: FirstCrossing as a critical Ferrers lower ideal

critical roof `criticalHeight k` から baseline `k` を引いた profile を
critical Ferrers shape とし、FirstCrossing proper-prefix 条件を shape inclusion にする。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- critical roof の Ferrers excess。 -/
def criticalExcess (k : ℕ) : ℕ :=
  criticalHeight k - k

/-- `criticalHeight k` は少なくとも baseline `k` にある。 -/
theorem index_le_criticalHeight (k : ℕ) :
    k ≤ criticalHeight k := by
  by_cases hk0 : k = 0
  · subst k
    simp [criticalHeight]
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    have hPow : 2 ^ k < 3 ^ k :=
      Nat.pow_lt_pow_left (by omega : (2 : ℕ) < 3) (Nat.ne_of_gt hkPos)
    exact le_criticalHeight_of_twoPow_lt_threePow hPow

/-- critical excess 自身も nondecreasing。 -/
theorem criticalExcess_mono
    {a b : ℕ}
    (hab : a ≤ b) :
    criticalExcess a ≤ criticalExcess b := by
  let d := b - a
  have habEq : a + d = b := by
    dsimp [d]
    omega
  have hdBase := index_le_criticalHeight d
  have hAdd := criticalHeight_add_lower a d
  rw [habEq] at hAdd
  have haBase := index_le_criticalHeight a
  have hbBase := index_le_criticalHeight b
  unfold criticalExcess
  omega

/-- length `p` の critical Beatty/Sturmian Ferrers roof。 -/
def criticalShape (p : ℕ) : FerrersShape p :=
  { column := fun i => criticalExcess i.1
    mono := by
      intro i j hij
      have hijNat : i.1 ≤ j.1 := hij
      exact criticalExcess_mono hijNat }

/-- Ferrers shape が critical roof の下側にあること。 -/
def IsCriticalSubshape
    {p : ℕ}
    (S : FerrersShape p) : Prop :=
  S.Le (criticalShape p)

/-- critical subshapes は downward closed。 -/
theorem IsCriticalSubshape.downward
    {p : ℕ}
    {A B : FerrersShape p}
    (hB : IsCriticalSubshape B)
    (hAB : A.Le B) :
    IsCriticalSubshape A := by
  exact FerrersShape.le_trans hAB hB

/-- meet は critical subshape を保つ。 -/
theorem criticalSubshape_meet
    {p : ℕ}
    {A B : FerrersShape p}
    (hA : IsCriticalSubshape A) :
    IsCriticalSubshape (FerrersShape.meet A B) := by
  intro i
  simp only [FerrersShape.meet_column]
  exact le_trans (min_le_left _ _) (hA i)

/-- join も critical subshape を保つ。 -/
theorem criticalSubshape_join
    {p : ℕ}
    {A B : FerrersShape p}
    (hA : IsCriticalSubshape A)
    (hB : IsCriticalSubshape B) :
    IsCriticalSubshape (FerrersShape.join A B) := by
  intro i
  simp only [FerrersShape.join_column]
  exact max_le (hA i) (hB i)

/-- fixed terminal chord が coefficient-contracting である pure condition。 -/
def ContractingChord (p H : ℕ) : Prop :=
  3 ^ p < 2 ^ H

/--
fixed `(p,H)` 上では FirstCrossing と critical Ferrers inclusion が同値。
terminal contracting は `ContractingChord p H` が担当する。
-/
theorem firstCrossing_iff_criticalSubshape
    {p H : ℕ}
    (x : FiberPoint p H)
    (hp : 0 < p)
    (hContract : ContractingChord p H) :
    FirstCrossing x.word ↔
      IsCriticalSubshape x.toFerrersShape := by
  constructor
  · intro hF i
    have hiLt : i.1 < p := i.isLt
    by_cases hi0 : i.1 = 0
    · change x.excessAt i.1 ≤ criticalExcess i.1
      rw [hi0]
      simp [FiberPoint.excessAt, criticalExcess, criticalHeight]
    · have hiPos : 0 < i.1 := Nat.pos_of_ne_zero hi0
      have hiWord : i.1 < oddSteps x.word := by
        rw [x.oddSteps_eq]
        exact hiLt
      have hDepth := hF.prefixTwoDepth_le_criticalHeight hiPos hiWord
      have hIndexX := x.index_le_height (Nat.le_of_lt hiLt)
      have hIndexC := index_le_criticalHeight i.1
      change x.excessAt i.1 ≤ criticalExcess i.1
      unfold FiberPoint.excessAt criticalExcess FiberPoint.height
      omega
  · intro hShape
    refine {
      nonempty := ?_
      properPositive := ?_
      terminalNegative := ?_
    }
    · apply List.ne_nil_of_length_pos
      have hLen : x.word.length = p := by
        simpa [oddSteps] using x.oddSteps_eq
      omega
    · intro k hkPos hkLtLen
      have hkLt : k < p := by
        have hLen : x.word.length = p := by
          simpa [oddSteps] using x.oddSteps_eq
        omega
      have hCol := hShape ⟨k, hkLt⟩
      change x.excessAt k ≤ criticalExcess k at hCol
      have hIndexX := x.index_le_height (Nat.le_of_lt hkLt)
      have hIndexC := index_le_criticalHeight k
      have hDepth : x.height k ≤ criticalHeight k := by
        unfold FiberPoint.excessAt criticalExcess at hCol
        omega
      have hPowLe :
          2 ^ x.height k ≤ 2 ^ criticalHeight k :=
        Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hDepth
      have hCrit := criticalHeight_pow_lt_threePow hkPos
      have hPow : 2 ^ x.height k < 3 ^ k :=
        lt_of_le_of_lt hPowLe hCrit
      have hkLeLen : k ≤ x.word.length := Nat.le_of_lt hkLtLen
      have hTakeLen : (x.word.take k).length = k :=
        List.length_take_of_le hkLeLen
      apply (expanding_iff_twoPow_lt_threePow).2
      simpa [FiberPoint.height, prefixTwoDepth,
        oddSteps, hTakeLen] using hPow
    · apply (contracting_iff_threePow_lt_twoPow).2
      simpa [ContractingChord, x.oddSteps_eq, x.twoSteps_eq] using hContract

/-- FirstCrossing fixed-chord fiber は Ferrers order の lower ideal。 -/
theorem firstCrossing_downward
    {p H : ℕ}
    {x y : FiberPoint p H}
    (hp : 0 < p)
    (hContract : ContractingChord p H)
    (hFx : FirstCrossing x.word)
    (hyx : y.toFerrersShape.Le x.toFerrersShape) :
    FirstCrossing y.word := by
  have hxShape : IsCriticalSubshape x.toFerrersShape :=
    (firstCrossing_iff_criticalSubshape x hp hContract).1 hFx
  have hyShape : IsCriticalSubshape y.toFerrersShape :=
    hxShape.downward hyx
  exact (firstCrossing_iff_criticalSubshape y hp hContract).2 hyShape

namespace FiberShape

/-- exact FiberShape 上で FirstCrossing は critical subshape condition そのもの。 -/
theorem firstCrossing_toFiberPoint_iff
    {p H : ℕ}
    (S : FiberShape p H)
    (hContract : ContractingChord p H) :
    FirstCrossing S.toFiberPoint.word ↔
      IsCriticalSubshape S.shape := by
  have h := firstCrossing_iff_criticalSubshape
    S.toFiberPoint S.p_pos hContract
  rw [S.toFerrersShape_toFiberPoint] at h
  exact h

/-- FirstCrossing exact fiber is closed under meet。 -/
theorem firstCrossing_meet
    {p H : ℕ}
    (A B : FiberShape p H)
    (hContract : ContractingChord p H)
    (hA : FirstCrossing A.toFiberPoint.word) :
    FirstCrossing (FiberShape.meet A B).toFiberPoint.word := by
  have hAShape := (A.firstCrossing_toFiberPoint_iff hContract).1 hA
  have hMeet : IsCriticalSubshape (FerrersShape.meet A.shape B.shape) :=
    criticalSubshape_meet hAShape
  apply ((FiberShape.meet A B).firstCrossing_toFiberPoint_iff hContract).2
  simpa [FiberShape.meet] using hMeet

/-- FirstCrossing exact fiber is closed under join。 -/
theorem firstCrossing_join
    {p H : ℕ}
    (A B : FiberShape p H)
    (hContract : ContractingChord p H)
    (hA : FirstCrossing A.toFiberPoint.word)
    (hB : FirstCrossing B.toFiberPoint.word) :
    FirstCrossing (FiberShape.join A B).toFiberPoint.word := by
  have hAShape := (A.firstCrossing_toFiberPoint_iff hContract).1 hA
  have hBShape := (B.firstCrossing_toFiberPoint_iff hContract).1 hB
  have hJoin : IsCriticalSubshape (FerrersShape.join A.shape B.shape) :=
    criticalSubshape_join hAShape hBShape
  apply ((FiberShape.join A B).firstCrossing_toFiberPoint_iff hContract).2
  simpa [FiberShape.join] using hJoin

/-- FirstCrossing exact fiber is downward closed in FiberShape inclusion。 -/
theorem firstCrossing_downward
    {p H : ℕ}
    {A B : FiberShape p H}
    (hContract : ContractingChord p H)
    (hB : FirstCrossing B.toFiberPoint.word)
    (hAB : A.Le B) :
    FirstCrossing A.toFiberPoint.word := by
  have hBShape := (B.firstCrossing_toFiberPoint_iff hContract).1 hB
  have hAShape := hBShape.downward hAB
  exact (A.firstCrossing_toFiberPoint_iff hContract).2 hAShape

end FiberShape

end RecordFerrers
end Collatz2
