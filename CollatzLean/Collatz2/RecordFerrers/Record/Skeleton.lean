import CollatzLean.Collatz2.RecordFerrers.Record.RecordDecomposition

/-!
# Record–Ferrers Phase A: record skeleton and carry gluing

record decomposition から local word decoration を忘れ、block length 列だけを残す。
criticalHeight の additive carry を skeleton の pure gluing condition として独立化する。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- positive block lengths だけを保持する record skeleton。 -/
structure Skeleton where
  lengths : List ℕ
  positive : ∀ r ∈ lengths, 0 < r

namespace Skeleton

/-- skeleton の total odd length。 -/
def totalLength (S : Skeleton) : ℕ := S.lengths.sum

/-- interior endpoints が roof -> roof であるための carry 条件。 -/
def interiorCarryConditionFrom (start : ℕ) : List ℕ → Prop
  | [] => False
  | [_r] => True
  | r :: s :: rs =>
      criticalCarry start r = 1 ∧
        interiorCarryConditionFrom (start + r) (s :: rs)

/-- 最終 endpoint まで含む full carry condition。interior は 1、terminal は 0。 -/
def carryConditionFrom (start : ℕ) : List ℕ → Prop
  | [] => False
  | [r] => criticalCarry start r = 0
  | r :: s :: rs =>
      criticalCarry start r = 1 ∧
        carryConditionFrom (start + r) (s :: rs)

/-- full carry condition は interior carry condition を含む。 -/
theorem interior_of_full
    (start : ℕ)
    (rs : List ℕ)
    (h : carryConditionFrom start rs) :
    interiorCarryConditionFrom start rs := by
  induction rs generalizing start with
  | nil =>
      simp [carryConditionFrom] at h
  | cons r rs ih =>
      cases rs with
      | nil =>
          simp [interiorCarryConditionFrom]
      | cons s ss =>
          change
            criticalCarry start r = 1 ∧
              carryConditionFrom (start + r) (s :: ss) at h
          change
            criticalCarry start r = 1 ∧
              interiorCarryConditionFrom (start + r) (s :: ss)
          exact ⟨h.1, ih (start + r) h.2⟩

/-- critical carry は引数交換に対して対称。 -/
theorem criticalCarry_comm (a b : ℕ) :
    criticalCarry a b = criticalCarry b a := by
  unfold criticalCarry
  rw [Nat.add_comm a b, Nat.add_comm (criticalHeight a) (criticalHeight b)]

/-- decomposition から skeleton を忘却する。 -/
def ofDecomposition
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) : Skeleton :=
  { lengths := D.lengths
    positive := D.lengths_pos }

@[simp] theorem ofDecomposition_lengths
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    (ofDecomposition D).lengths = D.lengths := rfl

/-- record chain が要求する carry condition は chain から自動で得られる。 -/
theorem carryCondition_of_chain
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    {lengths : List ℕ}
    (C : RecordChain x start lengths)
    (hWhole : FirstCrossing x.word) :
    carryConditionFrom start lengths := by
  induction C with
  | last B hTerminal =>
      simpa [carryConditionFrom] using
        B.criticalCarry_eq_zero_of_terminal hTerminal hWhole
  | @cons start len rest B hInterior T ih =>
      cases rest with
      | nil =>
          cases T
      | cons s ss =>
          simp only [carryConditionFrom]
          exact
            ⟨B.criticalCarry_eq_one_of_interior hInterior, ih⟩

/-- genuine decomposition の skeleton は full carry condition を満たす。 -/
theorem carryCondition_of_decomposition
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    carryConditionFrom start D.lengths :=
  carryCondition_of_chain D.chain D.whole_firstCrossing

end Skeleton

/-- skeleton に local minimal block words を載せた decoration。 -/
structure DecoratedSkeleton (S : Skeleton) where
  blocks : List Word
  lengths_eq : blocks.map oddSteps = S.lengths
  minimal : ∀ b ∈ blocks, MinimalBlock b

/-- decoration が genuine positive exponent words からなる版。 -/
structure ValidDecoratedSkeleton (S : Skeleton)
    extends DecoratedSkeleton S where
  valid : ∀ b ∈ blocks, Valid b


namespace RecordDecomposition

/-- genuine record decomposition の forward decoration。 -/
def toDecoratedSkeleton
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    DecoratedSkeleton (Skeleton.ofDecomposition D) :=
  { blocks := D.blocks
    lengths_eq := D.blocks_oddSteps_eq_lengths
    minimal := D.blocks_minimal }

/-- forward decoration を flatten すると元 word の record-start suffix に戻る。 -/
theorem decorated_flatten_eq_drop
    {p H : ℕ}
    {x : FiberPoint p H}
    {start : ℕ}
    (D : RecordDecomposition x start) :
    D.toDecoratedSkeleton.blocks.flatten = x.word.drop start :=
  D.blocks_flatten_eq_drop

end RecordDecomposition

namespace DecoratedSkeleton

/-- decoration の block 数は skeleton length 数と同じ。 -/
theorem blocks_length
    {S : Skeleton}
    (D : DecoratedSkeleton S) :
    D.blocks.length = S.lengths.length := by
  have h := congrArg List.length D.lengths_eq
  simpa using h

/-- decoration の total odd length は skeleton total length。 -/
theorem oddSteps_sum
    {S : Skeleton}
    (D : DecoratedSkeleton S) :
    (D.blocks.map oddSteps).sum = S.totalLength := by
  rw [D.lengths_eq]
  rfl

end DecoratedSkeleton

end RecordFerrers
end Collatz2
