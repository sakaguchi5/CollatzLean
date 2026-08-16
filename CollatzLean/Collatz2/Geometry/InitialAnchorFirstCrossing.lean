import CollatzLean.Collatz2.Geometry.PrimitiveReducedRecordInverse
import Mathlib.Tactic.NormNum

/-!
# Collatz2 Geometry: initial `[1]` anchor から FirstCrossing を自動回収

full record carry condition

* interior boundary: `criticalCarry = 1`
* final boundary: `criticalCarry = 0`

と local `MinimalCrossingBlock` 列だけから、critical roof 上の anchor に decorations を
concatenate した whole word が再び minimal FirstCrossing になることを証明する。

特に current A の initial anchor `[1]` では、inverse theorem に whole `FirstCrossing` を
外部仮定として渡す必要がなくなる。
-/

namespace Collatz2
namespace Word

/--
anchor が critical roof 上にあり、その全 nonempty prefix が critical roof 以下にある packet。
terminal 自身も expanding 側の roof 上にある。
-/
structure CriticalRoofPrefixData (w : Word) : Prop where
  roof :
    twoSteps w = criticalHeight (oddSteps w)
  prefix_le :
    ∀ k : ℕ,
      0 < k →
      k ≤ oddSteps w →
      prefixTwoDepth w k ≤ criticalHeight k

/-- append の左側内部では prefix depth は左 word と一致する。 -/
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
  have h := prefixTwoDepth_add_drop (u ++ v) (oddSteps u) j
  rw [prefixTwoDepth_append_left u v] at h
  simpa [oddSteps] using h

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
  have hPow :
      2 ^ prefixTwoDepth w k < 3 ^ k :=
    lt_of_le_of_lt hPowLe hCrit
  have hTakeLen : (w.take k).length = k := by
    apply List.length_take_of_le
    simpa [oddSteps] using hkLe
  apply (expanding_iff_twoPow_lt_threePow).2
  simpa [prefixTwoDepth, oddSteps, hTakeLen] using hPow

/-- minimal critical depth `criticalHeight(p)+1` は contracting。 -/
theorem contracting_of_twoSteps_eq_criticalHeight_add_one
    {w : Word}
    (hpPos : 0 < oddSteps w)
    (hDepth :
      twoSteps w = criticalHeight (oddSteps w) + 1) :
    Contracting w := by
  have hC :=
    (ContractingExponentPair.criticalUpperPair
      (oddSteps w) hpPos).contracting
  apply (contracting_iff_threePow_lt_twoPow).2
  rw [hDepth]
  simpa using hC

/-- current-A initial anchor `[1]` は critical roof profile そのもの。 -/
theorem criticalRoofPrefixData_one :
    CriticalRoofPrefixData ([1] : Word) := by
  refine {
    roof := ?_
    prefix_le := ?_
  }
  · norm_num [twoSteps, oddSteps, criticalHeight]
    decide
  · intro k hkPos hkLe
    have hk : k = 1 := by
      change k ≤ 1 at hkLe
      omega
    subst k
    norm_num [prefixTwoDepth, twoSteps, oddSteps, criticalHeight]
    decide

namespace CriticalRoofPrefixData

/--
roof anchor の後ろに local minimal block を置いた proper prefix は、
block endpoint を除き global critical roof 以下に残る。
-/
theorem prefix_le_append_minimal_of_lt
    {anchor b : Word}
    (A : CriticalRoofPrefixData anchor)
    (M : MinimalCrossingBlock b)
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
    have hLocal :
        prefixTwoDepth b j ≤ criticalHeight j :=
      M.firstCrossing.prefixTwoDepth_le_criticalHeight hjPos hjLt
    have hCritLower :=
      criticalHeight_add_lower (oddSteps anchor) j
    rw [hkEq, prefixTwoDepth_append_add, A.roof]
    omega

/--
interior carry `1` なら、minimal block を append した新しい endpoint も roof 上に戻る。
そのため critical-roof prefix packet をそのまま次 block へ渡せる。
-/
theorem append_minimal_of_carry_one
    {anchor b : Word}
    (A : CriticalRoofPrefixData anchor)
    (M : MinimalCrossingBlock b)
    (hCarry :
      criticalCarry (oddSteps anchor) (oddSteps b) = 1) :
    CriticalRoofPrefixData (anchor ++ b) := by
  have hRoof :
      twoSteps (anchor ++ b) =
        criticalHeight (oddSteps (anchor ++ b)) :=
    criticalRoof_append_of_carry_one
      anchor b A.roof M hCarry
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
      unfold prefixTwoDepth
      have hTake :
          List.take (oddSteps (anchor ++ b)) (anchor ++ b) =
            anchor ++ b := by
        unfold oddSteps
        simp only [List.length_append, List.take_eq_self_iff, Std.le_refl]
      rw [hTake]
    rw [hTerminal, hRoof]

end CriticalRoofPrefixData

/--
final carry `0` では、roof anchor + local minimal block の whole depth が
`criticalHeight(total)+1` になり、whole 自身が minimal FirstCrossing になる。
-/
theorem minimalCrossingBlock_append_of_carry_zero
    {anchor b : Word}
    (A : CriticalRoofPrefixData anchor)
    (M : MinimalCrossingBlock b)
    (hCarry :
      criticalCarry (oddSteps anchor) (oddSteps b) = 0) :
    MinimalCrossingBlock (anchor ++ b) := by
  have hCritAdd :=
    criticalHeight_add_eq (oddSteps anchor) (oddSteps b)
  rw [hCarry, add_zero] at hCritAdd
  have hTerminalDepth :
      twoSteps (anchor ++ b) =
        criticalHeight (oddSteps (anchor ++ b)) + 1 := by
    rw [twoSteps_append, oddSteps_append, A.roof, M.minimalDepth]
    omega
  have hpPos : 0 < oddSteps (anchor ++ b) := by
    rw [oddSteps_append]
    have hbPos := M.oddSteps_pos
    omega
  have hWholeFirst : FirstCrossing (anchor ++ b) := by
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
      have hDepth :=
        A.prefix_le_append_minimal_of_lt M hkPos hkLt
      exact expanding_take_of_prefixTwoDepth_le_criticalHeight
        (anchor ++ b) hkPos (Nat.le_of_lt hkLt) hDepth
    · exact
        contracting_of_twoSteps_eq_criticalHeight_add_one
          hpPos hTerminalDepth
  exact {
    firstCrossing := hWholeFirst
    minimalDepth := hTerminalDepth
  }

/--
critical-roof anchor の後ろに carry-compatible local minimal blocks を並べると、
interior carry `1` で roof packet を再帰的に運び、final carry `0` で whole が
minimal FirstCrossing になる。
-/
theorem minimalCrossingBlock_of_minimalBlocks_carryCondition
    (anchor : Word)
    (bs : List Word)
    (A : CriticalRoofPrefixData anchor)
    (hMinimal : ∀ b ∈ bs, MinimalCrossingBlock b)
    (hCarry :
      RecordSkeleton.carryConditionFrom
        (oddSteps anchor) (bs.map oddSteps)) :
    MinimalCrossingBlock (anchor ++ bs.flatten) := by
  induction bs generalizing anchor with
  | nil =>
      simp [RecordSkeleton.carryConditionFrom] at hCarry
  | cons b bs ih =>
      cases bs with
      | nil =>
          have hMb : MinimalCrossingBlock b :=
            hMinimal b (by simp)
          have hCarryZero :
              criticalCarry (oddSteps anchor) (oddSteps b) = 0 := by
            simpa [RecordSkeleton.carryConditionFrom] using hCarry
          simpa using
            minimalCrossingBlock_append_of_carry_zero
              A hMb hCarryZero
      | cons c cs =>
          have hMb : MinimalCrossingBlock b :=
            hMinimal b (by simp)
          have hTailMinimal :
              ∀ d ∈ c :: cs, MinimalCrossingBlock d := by
            intro d hd
            exact hMinimal d (by simp [hd])
          change
            criticalCarry (oddSteps anchor) (oddSteps b) = 1 ∧
              RecordSkeleton.carryConditionFrom
                (oddSteps anchor + oddSteps b)
                ((c :: cs).map oddSteps)
            at hCarry
          let A' : CriticalRoofPrefixData (anchor ++ b) :=
            A.append_minimal_of_carry_one hMb hCarry.1
          have hTailCarry :
              RecordSkeleton.carryConditionFrom
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

/--
current-A initial anchor `[1]` specialization。
carry-compatible arbitrary local minimal decorations を concatenate した whole は
自動的に minimal FirstCrossing。
-/
theorem minimalCrossingBlock_one_append_of_minimalBlocks_carryCondition
    (bs : List Word)
    (hMinimal : ∀ b ∈ bs, MinimalCrossingBlock b)
    (hCarry :
      RecordSkeleton.carryConditionFrom
        1 (bs.map oddSteps)) :
    MinimalCrossingBlock (([1] : Word) ++ bs.flatten) := by
  have hCarry' :
      RecordSkeleton.carryConditionFrom
        (oddSteps ([1] : Word)) (bs.map oddSteps) := by
    simpa [oddSteps] using hCarry
  exact
    minimalCrossingBlock_of_minimalBlocks_carryCondition
      ([1] : Word) bs criticalRoofPrefixData_one hMinimal hCarry'

/-- requested FirstCrossing corollary。 -/
theorem firstCrossing_one_append_of_minimalBlocks_carryCondition
    (bs : List Word)
    (hMinimal : ∀ b ∈ bs, MinimalCrossingBlock b)
    (hCarry :
      RecordSkeleton.carryConditionFrom
        1 (bs.map oddSteps)) :
    FirstCrossing (([1] : Word) ++ bs.flatten) :=
  (minimalCrossingBlock_one_append_of_minimalBlocks_carryCondition
    bs hMinimal hCarry).firstCrossing

/--
`[1]` anchor 専用の primitive+StripReduced inverse。
whole `FirstCrossing` は仮定せず carry condition から内部で自動構成する。

primitive / reduced は assembled word の pure `(H,p)` 条件として受け取る。
-/
def rankRecordDecomposition_one_of_primitiveReduced
    (bs : List Word)
    (hMinimal : ∀ b ∈ bs, MinimalCrossingBlock b)
    (hCarry :
      RecordSkeleton.carryConditionFrom
        1 (bs.map oddSteps))
    (hPrimitive :
      Nat.Coprime
        (twoSteps (([1] : Word) ++ bs.flatten))
        (oddSteps (([1] : Word) ++ bs.flatten)))
    (hReduced :
      ∀ r : ℕ,
        0 < r →
        r < oddSteps (([1] : Word) ++ bs.flatten) →
        stripRank (([1] : Word) ++ bs.flatten) r ≤
          oddSteps (([1] : Word) ++ bs.flatten)) :
    RankRecordDecomposition
      (([1] : Word) ++ bs.flatten) 1 := by
  let MWhole : MinimalCrossingBlock (([1] : Word) ++ bs.flatten) :=
    minimalCrossingBlock_one_append_of_minimalBlocks_carryCondition
      bs hMinimal hCarry
  let hWhole : FirstCrossing (([1] : Word) ++ bs.flatten) :=
    MWhole.firstCrossing
  have hPrimitivePair :
      hWhole.toContractingExponentPair.IsPrimitive := by
    change
      Nat.Coprime
        (twoSteps (([1] : Word) ++ bs.flatten))
        (oddSteps (([1] : Word) ++ bs.flatten))
    exact hPrimitive
  have hReducedPair :
      hWhole.toContractingExponentPair.StripReduced := by
    intro r hrPos hrLt
    have h := hReduced r hrPos (by simpa using hrLt)
    change
      twoSteps (([1] : Word) ++ bs.flatten) * r -
          oddSteps (([1] : Word) ++ bs.flatten) * criticalHeight r ≤
        oddSteps (([1] : Word) ++ bs.flatten)
    simpa [stripRank] using h
  have hCarry' :
      RecordSkeleton.carryConditionFrom
        (oddSteps ([1] : Word)) (bs.map oddSteps) := by
    simpa [oddSteps] using hCarry
  have hR :=
    rankRecordDecomposition_of_primitiveReduced_carryCondition
      ([1] : Word)
      bs
      (by norm_num [oddSteps])
      hMinimal
      criticalRoofPrefixData_one.roof
      hCarry'
      hWhole
      hPrimitivePair
      hReducedPair
  simpa [oddSteps] using hR

namespace DecoratedRecordSkeleton

/-- decorated skeleton 版の automatic FirstCrossing。 -/
theorem minimalCrossingBlock_one_append
    {S : RecordSkeleton}
    (D : DecoratedRecordSkeleton S)
    (hCarry :
      RecordSkeleton.carryConditionFrom 1 S.lengths) :
    MinimalCrossingBlock (([1] : Word) ++ D.blocks.flatten) := by
  have hCarryBlocks :
      RecordSkeleton.carryConditionFrom
        1 (D.blocks.map oddSteps) := by
    rw [D.lengths_eq]
    exact hCarry
  exact
    minimalCrossingBlock_one_append_of_minimalBlocks_carryCondition
      D.blocks D.minimal hCarryBlocks

/-- decorated skeleton 版の requested FirstCrossing corollary。 -/
theorem firstCrossing_one_append
    {S : RecordSkeleton}
    (D : DecoratedRecordSkeleton S)
    (hCarry :
      RecordSkeleton.carryConditionFrom 1 S.lengths) :
    FirstCrossing (([1] : Word) ++ D.blocks.flatten) :=
  (D.minimalCrossingBlock_one_append hCarry).firstCrossing

end DecoratedRecordSkeleton

end Word
end Collatz2
