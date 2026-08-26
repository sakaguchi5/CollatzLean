import CollatzLean.Collatz2.RecordFerrers.Perturbation.P04CarryBoundaryCharacterization
import CollatzLean.Collatz2.RecordFerrers.Core.FixedChordFiber

/-!
# Record–Ferrers 摂動理論 5: 同じ端点を持つ block 交換の局所性

同じ odd length と同じ total two-depth を持つ二つの block を入れ替えると、
block 終端以後の prefix depth は完全に一致する。
minimal block 同士の交換では、この二条件は skeleton length だけから自動で満たされる。
-/

namespace Collatz2
namespace RecordFerrers

open Word

/-- left / block / right context を明示した splice word。 -/
def spliceWord (leftCtx block rightCtx : Word) : Word :=
  leftCtx ++ block ++ rightCtx

/-- 同じ長さ・同じ total depth の block は block 終端の prefix depth を変えない。 -/
theorem prefixTwoDepth_splice_end_eq
    (leftCtx b b' rightCtx : Word)
    (hTwo : twoSteps b = twoSteps b') :
    prefixTwoDepth (spliceWord leftCtx b rightCtx)
        (oddSteps leftCtx + oddSteps b) =
      prefixTwoDepth (spliceWord leftCtx b' rightCtx)
        (oddSteps leftCtx + oddSteps b') := by
  unfold spliceWord prefixTwoDepth oddSteps
  have hTakeB :
      List.take
          (List.length leftCtx + List.length b)
          ((leftCtx ++ b) ++ rightCtx) =
        leftCtx ++ b := by
    rw [← List.length_append]
    exact List.take_left
  have hTakeB' :
      List.take
          (List.length leftCtx + List.length b')
          ((leftCtx ++ b') ++ rightCtx) =
        leftCtx ++ b' := by
    rw [← List.length_append]
    exact List.take_left
  rw [hTakeB, hTakeB']
  rw [twoSteps_append, twoSteps_append, hTwo]

/--
同じ長さ・同じ total depth の block を交換しても、
block 終端から `t` 個先の prefix depth は一致する。
-/
theorem prefixTwoDepth_splice_after_eq
    (leftCtx b b' rightCtx : Word)
    (hTwo : twoSteps b = twoSteps b')
    (t : ℕ) :
    prefixTwoDepth (spliceWord leftCtx b rightCtx)
        (oddSteps leftCtx + oddSteps b + t) =
      prefixTwoDepth (spliceWord leftCtx b' rightCtx)
        (oddSteps leftCtx + oddSteps b' + t) := by
  unfold spliceWord prefixTwoDepth oddSteps
  simp only [Nat.add_assoc, List.append_assoc]
  have hTakeB :
      List.take
          (List.length leftCtx + (List.length b + t))
          (leftCtx ++ (b ++ rightCtx)) =
        leftCtx ++ (b ++ List.take t rightCtx) := by
    rw [List.take_length_add_append]
    rw [List.take_length_add_append]
  have hTakeB' :
      List.take
          (List.length leftCtx + (List.length b' + t))
          (leftCtx ++ (b' ++ rightCtx)) =
        leftCtx ++ (b' ++ List.take t rightCtx) := by
    rw [List.take_length_add_append]
    rw [List.take_length_add_append]
  rw [hTakeB, hTakeB']
  simp only [twoSteps_append]
  rw [hTwo]

/-- minimal block は同じ odd length なら total depth も同じ。 -/
theorem MinimalBlock.twoSteps_eq_of_same_oddSteps
    {b b' : Word}
    (hb : MinimalBlock b)
    (hb' : MinimalBlock b')
    (hOdd : oddSteps b = oddSteps b') :
    twoSteps b = twoSteps b' := by
  rw [hb.minimalDepth, hb'.minimalDepth, hOdd]

/--
同じ skeleton length の minimal decoration 交換は
block 終端以後で prefix depth を変えない。
-/
theorem prefixTwoDepth_after_replaced_minimalBlock
    (leftCtx b b' rightCtx : Word)
    (hb : MinimalBlock b)
    (hb' : MinimalBlock b')
    (hOdd : oddSteps b = oddSteps b')
    (t : ℕ) :
    prefixTwoDepth (spliceWord leftCtx b rightCtx)
        (oddSteps leftCtx + oddSteps b + t) =
      prefixTwoDepth (spliceWord leftCtx b' rightCtx)
        (oddSteps leftCtx + oddSteps b' + t) := by
  exact prefixTwoDepth_splice_after_eq
    leftCtx b b' rightCtx
    (hb.twoSteps_eq_of_same_oddSteps hb' hOdd)
    t

end RecordFerrers
end Collatz2
