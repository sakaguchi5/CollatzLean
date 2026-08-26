import CollatzLean.Collatz2.RecordFerrers.Factorization.RecordFerrersFactorization
import CollatzLean.Collatz2.Geometry.ContractingPairDescent

/-!
# Record–Ferrers Phase A: carry-compatible assembly gives FirstCrossing

critical roof 上の anchor と carry-compatible minimal blocks を連結すると、interior carry 1
で roof packet が伝播し、最後の carry 0 で whole word が minimal FirstCrossing になる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- anchor が critical roof 上にあり、全 positive prefix が roof 以下にある。 -/
structure CriticalRoofPrefix (w : Word) : Prop where
  roof : twoSteps w = criticalHeight (oddSteps w)
  prefix_le :
    ∀ k : ℕ,
      0 < k →
      k ≤ oddSteps w →
      prefixTwoDepth w k ≤ criticalHeight k

/-- append の左側内部では prefix depth は左 word と一致。 -/
theorem prefixTwoDepth_append_left_of_le
    (u v : Word)
    {k : ℕ}
    (hk : k ≤ oddSteps u) :
    prefixTwoDepth (u ++ v) k = prefixTwoDepth u k := by
  unfold oddSteps at hk
  unfold prefixTwoDepth
  rw [List.take_append_of_le_length hk]

/-- append 境界から `j` だけ進んだ cumulative depth の exact formula。 -/
theorem prefixTwoDepth_append_add
    (u v : Word)
    (j : ℕ) :
    prefixTwoDepth (u ++ v) (oddSteps u + j) =
      twoSteps u + prefixTwoDepth v j := by
  have h := FiberPoint.prefixTwoDepth_add_drop (u ++ v) (oddSteps u) j
  have hLeft : prefixTwoDepth (u ++ v) (oddSteps u) = twoSteps u := by
    unfold prefixTwoDepth oddSteps
    simp
  have hDrop : (u ++ v).drop (oddSteps u) = v := by
    unfold oddSteps
    simp
  rw [hLeft, hDrop] at h
  exact h

/-- critical roof 以下の positive prefix は expanding。 -/
theorem expanding_take_of_prefixTwoDepth_le_criticalHeight
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

/-- minimal critical terminal depth は contracting。 -/
theorem contracting_of_twoSteps_eq_minimalDepth
    {w : Word}
    (hpPos : 0 < oddSteps w)
    (hDepth : twoSteps w = minimalDepth (oddSteps w)) :
    Contracting w := by
  have hC :=
    (ContractingExponentPair.criticalUpperPair
      (oddSteps w) hpPos).contracting
  apply (contracting_iff_threePow_lt_twoPow).2
  unfold minimalDepth at hDepth
  rw [hDepth]
  simpa using hC

namespace CriticalRoofPrefix

/-- roof anchor + minimal block の proper prefix は global critical roof 以下。 -/
theorem prefix_le_append_minimal_of_lt
    {anchor b : Word}
    (A : CriticalRoofPrefix anchor)
    (M : MinimalBlock b)
    {k : ℕ}
    (hkPos : 0 < k)
    (hkLt : k < oddSteps (anchor ++ b)) :
    prefixTwoDepth (anchor ++ b) k ≤ criticalHeight k := by
  by_cases hkLeft : k ≤ oddSteps anchor
  · rw [prefixTwoDepth_append_left_of_le anchor b hkLeft]
    exact A.prefix_le k hkPos hkLeft
  · have haLt : oddSteps anchor < k := by omega
    let j := k - oddSteps anchor
    have hjPos : 0 < j := by
      dsimp [j]
      omega
    have hkEq : k = oddSteps anchor + j := by
      dsimp [j]
      omega
    have hjLt : j < oddSteps b := by
      rw [oddSteps_append] at hkLt
      dsimp [j]
      omega
    have hLocal : prefixTwoDepth b j ≤ criticalHeight j :=
      M.firstCrossing.prefixTwoDepth_le_criticalHeight hjPos hjLt
    have hCritLower := criticalHeight_add_lower (oddSteps anchor) j
    rw [hkEq, prefixTwoDepth_append_add, A.roof]
    omega

/-- interior carry 1 なら append 後も CriticalRoofPrefix。 -/
theorem append_minimal_of_carry_one
    {anchor b : Word}
    (A : CriticalRoofPrefix anchor)
    (M : MinimalBlock b)
    (hCarry : criticalCarry (oddSteps anchor) (oddSteps b) = 1) :
    CriticalRoofPrefix (anchor ++ b) := by
  have hCrit := criticalHeight_add_eq (oddSteps anchor) (oddSteps b)
  rw [hCarry] at hCrit
  have hRoof :
      twoSteps (anchor ++ b) =
        criticalHeight (oddSteps (anchor ++ b)) := by
    rw [twoSteps_append, oddSteps_append, A.roof, M.minimalDepth]
    omega
  refine {
    roof := hRoof
    prefix_le := ?_
  }
  intro k hkPos hkLe
  by_cases hkLt : k < oddSteps (anchor ++ b)
  · exact A.prefix_le_append_minimal_of_lt M hkPos hkLt
  · have hkEq : k = oddSteps (anchor ++ b) := by
      omega
    subst k
    have hTerminal :
        prefixTwoDepth (anchor ++ b) (oddSteps (anchor ++ b)) =
          twoSteps (anchor ++ b) := by
      unfold prefixTwoDepth oddSteps
      rw [List.take_length]
    rw [hTerminal, hRoof]

end CriticalRoofPrefix

/-- final carry 0 なら roof anchor + minimal block は whole minimal FirstCrossing。 -/
theorem minimalBlock_append_of_carry_zero
    {anchor b : Word}
    (A : CriticalRoofPrefix anchor)
    (M : MinimalBlock b)
    (hCarry : criticalCarry (oddSteps anchor) (oddSteps b) = 0) :
    MinimalBlock (anchor ++ b) := by
  have hCrit := criticalHeight_add_eq (oddSteps anchor) (oddSteps b)
  rw [hCarry] at hCrit
  have hTerminalDepth :
      twoSteps (anchor ++ b) =
        minimalDepth (oddSteps (anchor ++ b)) := by
    unfold minimalDepth
    rw [twoSteps_append, oddSteps_append, A.roof, M.minimalDepth]
    omega
  have hpPos : 0 < oddSteps (anchor ++ b) := by
    rw [oddSteps_append]
    have hbPos := M.oddSteps_pos
    omega
  have hFirst : FirstCrossing (anchor ++ b) := by
    refine {
      nonempty := ?_
      properPositive := ?_
      terminalNegative := ?_
    }
    · apply List.ne_nil_of_length_pos
      simpa [oddSteps] using hpPos
    · intro k hkPos hkLtLen
      have hkLt : k < oddSteps (anchor ++ b) := by
        simpa [oddSteps] using hkLtLen
      have hDepth := A.prefix_le_append_minimal_of_lt M hkPos hkLt
      exact expanding_take_of_prefixTwoDepth_le_criticalHeight
        (anchor ++ b) hkPos (Nat.le_of_lt hkLt) hDepth
    · exact contracting_of_twoSteps_eq_minimalDepth hpPos hTerminalDepth
  exact {
    firstCrossing := hFirst
    minimalDepth := hTerminalDepth
  }

/-- carry-compatible minimal block list は roof anchor から whole minimal FirstCrossing を組み立てる。 -/
theorem minimalBlock_of_blocks_carryCondition
    (anchor : Word)
    (bs : List Word)
    (A : CriticalRoofPrefix anchor)
    (hMinimal : ∀ b ∈ bs, MinimalBlock b)
    (hCarry :
      Skeleton.carryConditionFrom
        (oddSteps anchor) (bs.map oddSteps)) :
    MinimalBlock (anchor ++ bs.flatten) := by
  induction bs generalizing anchor with
  | nil =>
      simp [Skeleton.carryConditionFrom] at hCarry
  | cons b bs ih =>
      cases bs with
      | nil =>
          have hMb : MinimalBlock b := hMinimal b (by simp)
          have hCarryZero :
              criticalCarry (oddSteps anchor) (oddSteps b) = 0 := by
            simpa [Skeleton.carryConditionFrom] using hCarry
          simpa using minimalBlock_append_of_carry_zero A hMb hCarryZero
      | cons c cs =>
          have hMb : MinimalBlock b := hMinimal b (by simp)
          have hTailMinimal : ∀ d ∈ c :: cs, MinimalBlock d := by
            intro d hd
            exact hMinimal d (by simp [hd])
          change
            criticalCarry (oddSteps anchor) (oddSteps b) = 1 ∧
              Skeleton.carryConditionFrom
                (oddSteps anchor + oddSteps b)
                ((c :: cs).map oddSteps) at hCarry
          let A' : CriticalRoofPrefix (anchor ++ b) :=
            A.append_minimal_of_carry_one hMb hCarry.1
          have hTailCarry :
              Skeleton.carryConditionFrom
                (oddSteps (anchor ++ b))
                ((c :: cs).map oddSteps) := by
            simpa [oddSteps_append] using hCarry.2
          have hTail :=
            ih
              (anchor := anchor ++ b)
              A'
              hTailMinimal
              hTailCarry
          simpa [List.append_assoc] using hTail

end RecordFerrers
end Collatz2
