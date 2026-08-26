import CollatzLean.Collatz2.RecordFerrers.Factorization.RecordInverse
import CollatzLean.Collatz2.Geometry.PrimitiveBestUpper

/-!
# Record–Ferrers Phase A: primitive + StripReduced record inverse

primitive + StripReduced whole chord では generic record inverse が要求する
`critical-below` と各 local terminal `drop` が自動になる。
legacy `Geometry.Record*` には依存しない。
-/

namespace Collatz2
namespace RecordFerrers

open Word

namespace FiberPoint

/-- FirstCrossing fixed fiber を pure contracting exponent pair へ忘却する。 -/
def toContractingExponentPair
    {p H : ℕ}
    (x : FiberPoint p H)
    (hF : FirstCrossing x.word) : ContractingExponentPair :=
  { oddCount := p
    twoDepth := H
    oddCount_pos := by
      have hLenPos : 0 < x.word.length :=
        List.length_pos_iff.mpr hF.nonempty
      have hLen : x.word.length = p := by
        simpa [oddSteps] using x.oddSteps_eq
      omega
    contracting := by
      have h :=
        (contracting_iff_threePow_lt_twoPow).1 hF.terminalContracting
      simpa [x.oddSteps_eq, x.twoSteps_eq] using h }

@[simp] theorem toContractingExponentPair_oddCount
    {p H : ℕ}
    (x : FiberPoint p H)
    (hF : FirstCrossing x.word) :
    (x.toContractingExponentPair hF).oddCount = p := rfl

@[simp] theorem toContractingExponentPair_twoDepth
    {p H : ℕ}
    (x : FiberPoint p H)
    (hF : FirstCrossing x.word) :
    (x.toContractingExponentPair hF).twoDepth = H := rfl

end FiberPoint

/-- block list に属する block length は flatten 全体以下。 -/
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
primitive + StripReduced whole FirstCrossing では、positive roof anchor と local minimal
blocks の carry-compatible factorization から genuine new-layer RecordDecomposition を回収する。
-/
def recordDecomposition_of_primitiveReduced
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor : Word)
    (bs : List Word)
    (hWord : x.word = anchor ++ bs.flatten)
    (hNonempty : bs ≠ [])
    (hAnchorPos : 0 < oddSteps anchor)
    (hMinimal : ∀ b ∈ bs, MinimalBlock b)
    (hAnchorRoof : twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCarry :
      Skeleton.interiorCarryConditionFrom
        (oddSteps anchor) (bs.map oddSteps))
    (hWhole : FirstCrossing x.word)
    (hPrimitive : (x.toContractingExponentPair hWhole).IsPrimitive)
    (hReduced : (x.toContractingExponentPair hWhole).StripReduced) :
    RecordDecomposition x (oddSteps anchor) := by
  let P := x.toContractingExponentPair hWhole
  have hCriticalBelow :
      ∀ j : ℕ, 0 < j → p * criticalHeight j < H * j := by
    intro j hjPos
    have h := P.criticalHeight_below_chord hjPos
    simpa [P] using h
  have hDrop :
      ∀ b ∈ bs,
        H * oddSteps b < p * (criticalHeight (oddSteps b) + 1) := by
    intro b hb
    have hMb : MinimalBlock b := hMinimal b hb
    have hrPos : 0 < oddSteps b := hMb.oddSteps_pos
    have hrLeFlat : oddSteps b ≤ oddSteps bs.flatten :=
      oddSteps_le_flatten_of_mem hb
    have hWholeOdd : p = oddSteps anchor + oddSteps bs.flatten := by
      have hOdd : oddSteps x.word = oddSteps (anchor ++ bs.flatten) := by
        rw [hWord]
      rw [x.oddSteps_eq, oddSteps_append] at hOdd
      exact hOdd
    have hrLt : oddSteps b < p := by
      omega
    have hStrip :=
      P.stripRank_pos_lt_of_primitive_reduced
        hPrimitive hReduced hrPos (by simpa [P] using hrLt)
    have hStripLt :
        H * oddSteps b - p * criticalHeight (oddSteps b) < p := by
      simpa [P, ContractingExponentPair.stripRank] using hStrip.2
    have hLower :
        p * criticalHeight (oddSteps b) < H * oddSteps b :=
      hCriticalBelow (oddSteps b) hrPos
    rw [Nat.mul_add, Nat.mul_one]
    omega
  exact
    recordDecomposition_of_minimalBlocks
      x anchor bs hWord hNonempty hMinimal hAnchorRoof hCarry
      hCriticalBelow hDrop hWhole

/-- full carry condition から interior carry を自動で取り出す convenience constructor。 -/
def recordDecomposition_of_primitiveReduced_fullCarry
    {p H : ℕ}
    (x : FiberPoint p H)
    (anchor : Word)
    (bs : List Word)
    (hWord : x.word = anchor ++ bs.flatten)
    (hNonempty : bs ≠ [])
    (hAnchorPos : 0 < oddSteps anchor)
    (hMinimal : ∀ b ∈ bs, MinimalBlock b)
    (hAnchorRoof : twoSteps anchor = criticalHeight (oddSteps anchor))
    (hCarry :
      Skeleton.carryConditionFrom
        (oddSteps anchor) (bs.map oddSteps))
    (hWhole : FirstCrossing x.word)
    (hPrimitive : (x.toContractingExponentPair hWhole).IsPrimitive)
    (hReduced : (x.toContractingExponentPair hWhole).StripReduced) :
    RecordDecomposition x (oddSteps anchor) :=
  recordDecomposition_of_primitiveReduced
    x anchor bs hWord hNonempty hAnchorPos hMinimal hAnchorRoof
    (Skeleton.interior_of_full _ _ hCarry)
    hWhole hPrimitive hReduced

end RecordFerrers
end Collatz2
