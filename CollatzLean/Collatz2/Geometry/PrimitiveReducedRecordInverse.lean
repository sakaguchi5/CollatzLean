import CollatzLean.Collatz2.Geometry.RecordFerrersFactorization
import CollatzLean.Collatz2.Geometry.PrimitiveBestUpper

/-!
# Collatz2 Geometry: primitive + StripReduced record inverse

`RecordFerrersFactorization.rankRecordDecomposition_of_minimalBlocks` では、
任意 local minimal-crossing decorations を record decomposition に戻すために

* global chord が local critical roof より上 (`hCriticalBelow`)
* 各 local block terminal が global chord を strict に跨ぐ (`hDrop`)

を明示的に仮定していた。

このファイルでは whole word が FirstCrossing で、その exponent pair が
primitive + StripReduced なら、この二条件が自動であることを証明する。
従って positive critical-roof anchor と carry-compatible skeleton の上では、
任意の local minimal decorations を同じ block list のまま genuine rank-record chain に戻せる。
-/

namespace Collatz2
namespace Word

namespace FirstCrossing

/-- FirstCrossing word が持つ contracting exponent pair。 -/
def toContractingExponentPair
    {w : Word}
    (hF : FirstCrossing w) : ContractingExponentPair :=
  { oddCount := oddSteps w
    twoDepth := twoSteps w
    oddCount_pos := by
      unfold oddSteps
      exact List.length_pos_iff.mpr hF.nonempty
    contracting :=
      (contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting }

@[simp] theorem toContractingExponentPair_oddCount
    {w : Word}
    (hF : FirstCrossing w) :
    hF.toContractingExponentPair.oddCount = oddSteps w := by
  rfl

@[simp] theorem toContractingExponentPair_twoDepth
    {w : Word}
    (hF : FirstCrossing w) :
    hF.toContractingExponentPair.twoDepth = twoSteps w := by
  rfl

end FirstCrossing

/-- block list に属する block の odd length は flatten 全体以下。 -/
private theorem oddSteps_le_flatten_of_mem
    {b : Word}
    {bs : List Word}
    (hb : b ∈ bs) :
    oddSteps b ≤ oddSteps bs.flatten := by
  induction bs with
  | nil =>
      simp at hb
  | cons c cs ih =>
      simp only [List.mem_cons] at hb
      simp only [List.flatten_cons, oddSteps_append]
      rcases hb with hEq | hb
      · subst c
        omega
      · have hLe := ih hb
        omega

/--
primitive + StripReduced whole FirstCrossing の下では、
positive critical-roof anchor と carry-compatible local minimal blocks だけから
rank-record decomposition を再構成できる。

既存 generic inverse の `hCriticalBelow` と `hDrop` はここでは仮定しない。
-/
def rankRecordDecomposition_of_primitiveReduced
    (anchor : Word)
    (bs : List Word)
    (hAnchorPos : 0 < oddSteps anchor)
    (hMinimal : ∀ b ∈ bs, MinimalCrossingBlock b)
    (hAnchorRoof :
      twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCarry :
      RecordSkeleton.interiorCarryConditionFrom
        (oddSteps anchor) (bs.map oddSteps))
    (hWhole : FirstCrossing (anchor ++ bs.flatten))
    (hPrimitive : hWhole.toContractingExponentPair.IsPrimitive)
    (hReduced : hWhole.toContractingExponentPair.StripReduced) :
    RankRecordDecomposition
      (anchor ++ bs.flatten) (oddSteps anchor) := by
  have hNonempty : bs ≠ [] := by
    intro hNil
    subst bs
    simp [RecordSkeleton.interiorCarryConditionFrom] at hCarry
  have hCriticalBelow :
      ∀ j : ℕ, 0 < j →
        oddSteps (anchor ++ bs.flatten) * criticalHeight j <
          twoSteps (anchor ++ bs.flatten) * j := by
    intro j hjPos
    exact hWhole.criticalHeight_below_chord hjPos
  have hDrop :
      ∀ b ∈ bs,
        twoSteps (anchor ++ bs.flatten) * oddSteps b <
          oddSteps (anchor ++ bs.flatten) *
            (criticalHeight (oddSteps b) + 1) := by
    intro b hb
    have hMb : MinimalCrossingBlock b := hMinimal b hb
    have hrPos : 0 < oddSteps b := hMb.oddSteps_pos
    have hrLeFlat : oddSteps b ≤ oddSteps bs.flatten :=
      oddSteps_le_flatten_of_mem hb
    have hrLtWhole :
        oddSteps b < oddSteps (anchor ++ bs.flatten) := by
      rw [oddSteps_append]
      omega
    have hrLtPair :
        oddSteps b < hWhole.toContractingExponentPair.oddCount := by
      simpa using hrLtWhole
    have hStrip :=
      hWhole.toContractingExponentPair.stripRank_pos_lt_of_primitive_reduced
        hPrimitive hReduced hrPos hrLtPair
    have hStripLt :
        twoSteps (anchor ++ bs.flatten) * oddSteps b -
            oddSteps (anchor ++ bs.flatten) *
              criticalHeight (oddSteps b) <
          oddSteps (anchor ++ bs.flatten) := by
      simpa [ContractingExponentPair.stripRank] using hStrip.2
    have hLower :
        oddSteps (anchor ++ bs.flatten) *
            criticalHeight (oddSteps b) <
          twoSteps (anchor ++ bs.flatten) * oddSteps b :=
      hWhole.criticalHeight_below_chord hrPos
    rw [Nat.mul_add, Nat.mul_one]
    omega
  exact
    rankRecordDecomposition_of_minimalBlocks
      anchor bs hNonempty hMinimal hAnchorRoof hCarry
      hCriticalBelow hDrop

/-- full `carryConditionFrom` から使う convenience constructor。 -/
def rankRecordDecomposition_of_primitiveReduced_carryCondition
    (anchor : Word)
    (bs : List Word)
    (hAnchorPos : 0 < oddSteps anchor)
    (hMinimal : ∀ b ∈ bs, MinimalCrossingBlock b)
    (hAnchorRoof :
      twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCarry :
      RecordSkeleton.carryConditionFrom
        (oddSteps anchor) (bs.map oddSteps))
    (hWhole : FirstCrossing (anchor ++ bs.flatten))
    (hPrimitive : hWhole.toContractingExponentPair.IsPrimitive)
    (hReduced : hWhole.toContractingExponentPair.StripReduced) :
    RankRecordDecomposition
      (anchor ++ bs.flatten) (oddSteps anchor) := by
  exact
    rankRecordDecomposition_of_primitiveReduced
      anchor bs hAnchorPos hMinimal hAnchorRoof
      (RecordSkeleton.interiorCarryConditionFrom_of_carryConditionFrom
        (oddSteps anchor) (bs.map oddSteps) hCarry)
      hWhole hPrimitive hReduced

/-- Prop 版: primitive+reduced hypotheses から generic record chain の存在を得る。 -/
theorem exists_rankRecordDecomposition_of_primitiveReduced
    (anchor : Word)
    (bs : List Word)
    (hAnchorPos : 0 < oddSteps anchor)
    (hMinimal : ∀ b ∈ bs, MinimalCrossingBlock b)
    (hAnchorRoof :
      twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCarry :
      RecordSkeleton.carryConditionFrom
        (oddSteps anchor) (bs.map oddSteps))
    (hWhole : FirstCrossing (anchor ++ bs.flatten))
    (hPrimitive : hWhole.toContractingExponentPair.IsPrimitive)
    (hReduced : hWhole.toContractingExponentPair.StripReduced) :
    Nonempty
      (RankRecordDecomposition
        (anchor ++ bs.flatten) (oddSteps anchor)) := by
  exact ⟨rankRecordDecomposition_of_primitiveReduced_carryCondition
    anchor bs hAnchorPos hMinimal hAnchorRoof hCarry
    hWhole hPrimitive hReduced⟩

namespace DecoratedRecordSkeleton

/--
RecordSkeleton に載せた任意 local minimal decorations 版。
full carry condition と primitive+StripReduced whole word だけで、
その decoration を genuine rank-record decomposition に戻す。
-/
def toRankRecordDecomposition_of_primitiveReduced
    {S : RecordSkeleton}
    (D : DecoratedRecordSkeleton S)
    (anchor : Word)
    (hAnchorPos : 0 < oddSteps anchor)
    (hAnchorRoof :
      twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCarry :
      RecordSkeleton.carryConditionFrom
        (oddSteps anchor) S.lengths)
    (hWhole : FirstCrossing (anchor ++ D.blocks.flatten))
    (hPrimitive : hWhole.toContractingExponentPair.IsPrimitive)
    (hReduced : hWhole.toContractingExponentPair.StripReduced) :
    RankRecordDecomposition
      (anchor ++ D.blocks.flatten) (oddSteps anchor) := by
  have hCarryBlocks :
      RecordSkeleton.carryConditionFrom
        (oddSteps anchor) (D.blocks.map oddSteps) := by
    rw [D.lengths_eq]
    exact hCarry
  exact
    Collatz2.Word.rankRecordDecomposition_of_primitiveReduced_carryCondition
      anchor D.blocks hAnchorPos D.minimal hAnchorRoof hCarryBlocks
      hWhole hPrimitive hReduced

/-- Decorated skeleton 版の Prop-level existence theorem。 -/
theorem exists_rankRecordDecomposition_of_primitiveReduced
    {S : RecordSkeleton}
    (D : DecoratedRecordSkeleton S)
    (anchor : Word)
    (hAnchorPos : 0 < oddSteps anchor)
    (hAnchorRoof :
      twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCarry :
      RecordSkeleton.carryConditionFrom
        (oddSteps anchor) S.lengths)
    (hWhole : FirstCrossing (anchor ++ D.blocks.flatten))
    (hPrimitive : hWhole.toContractingExponentPair.IsPrimitive)
    (hReduced : hWhole.toContractingExponentPair.StripReduced) :
    Nonempty
      (RankRecordDecomposition
        (anchor ++ D.blocks.flatten) (oddSteps anchor)) := by
  exact ⟨D.toRankRecordDecomposition_of_primitiveReduced
    anchor hAnchorPos hAnchorRoof hCarry hWhole hPrimitive hReduced⟩

end DecoratedRecordSkeleton

end Word
end Collatz2
