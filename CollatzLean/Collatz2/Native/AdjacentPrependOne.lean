import CollatzLean.Collatz2.Native.PrependOneDefect
import CollatzLean.Collatz2.Orbit.FutureMinimumArithmetic
import CollatzLean.Collatz2.Global.AdjacentTransferChain

/-!
# Collatz2 Native: adjacent future-minimum block begins with exponent one

future minimum `x>1` では first exponent が `1`。
この事実を adjacent block word と actual Runs に直接移し、
旧 prepend-one packet を作らず `PrependOneDefect` へ接続する。
-/

namespace Collatz2

namespace AdjacentTransferChain

/-- start future minimum が `>1` なら adjacent word は definitionally `1 :: tail`。 -/
theorem exists_word_eq_one_cons_of_one_lt_startValue
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hstart : 1 < C.startValue n) :
    ∃ v : Word, C.word n = 1 :: v := by
  have hExp : O.exponent (C.startIndex n) = 1 := by
    apply (C.startFutureMinimum n).exponent_eq_one_of_one_lt_value
    simpa [AdjacentTransferChain.startValue] using hstart
  have hlen : 0 < C.length n := C.length_pos n
  obtain ⟨m, hm⟩ : ∃ m : ℕ, C.length n = m + 1 := by
    exact ⟨C.length n - 1, by omega⟩
  refine ⟨O.segment (C.startIndex n + 1) m, ?_⟩
  unfold AdjacentTransferChain.word
  rw [hm, O.segment_succ, hExp]

/--
`1 :: tail` decomposition に沿って actual first step と tail realization を lossless に取り出す。
-/
theorem exists_prependOne_tail_realizations
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hstart : 1 < C.startValue n) :
    ∃ v : Word, ∃ y : ℕ,
      C.word n = 1 :: v ∧
      Word.Realizes ([1] : Word) (C.startValue n) y ∧
      Word.Realizes v y (C.endValue n) := by
  obtain ⟨v, hv⟩ := C.exists_word_eq_one_cons_of_one_lt_startValue hstart
  have hrun : Runs (1 :: v) (C.startValue n) (C.endValue n) := by
    rw [← hv]
    exact C.runs n
  cases hrun with
  | @cons _ _ _ y _ he hstep hyOdd htail =>
      refine ⟨v, y, hv, ?_, htail.realizes⟩
      exact (Word.realizes_singleton_iff 1 (C.startValue n) y).2 hstep

/-- actual first-step boundary は odd。 -/
theorem exists_prependOne_tail_runs
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hstart : 1 < C.startValue n) :
    ∃ v : Word, ∃ y : ℕ,
      C.word n = 1 :: v ∧
      Odd y ∧
      Runs v y (C.endValue n) := by
  obtain ⟨v, hv⟩ := C.exists_word_eq_one_cons_of_one_lt_startValue hstart
  have hrun : Runs (1 :: v) (C.startValue n) (C.endValue n) := by
    rw [← hv]
    exact C.runs n
  cases hrun with
  | @cons _ _ _ y _ he hstep hyOdd htail =>
      exact ⟨v, y, hv, hyOdd, htail⟩

/--
future-minimum adjacent positive return を `[1] ++ tail` defect inequality へ直接接続する。
-/
theorem exists_tail_defect_bound_of_one_lt_startValue
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hstart : 1 < C.startValue n) :
    ∃ v : Word, ∃ y : ℕ,
      C.word n = 1 :: v ∧
      Word.Realizes ([1] : Word) (C.startValue n) y ∧
      Word.Realizes v y (C.endValue n) ∧
      -(2 * Word.startDefect v y) <
        ((AffineTransfer.ofWord v).twoCoeff : ℤ) *
          ((C.startValue n : ℤ) + 1) := by
  obtain ⟨v, y, hv, hOne, hTail⟩ :=
    C.exists_prependOne_tail_realizations hstart
  have hWhole : 0 < Word.startDefect (1 :: v) (C.startValue n) := by
    rw [← hv]
    exact C.startDefect_pos n
  have hBound :=
    Word.tail_defect_bound_of_prependOne_positive hOne hTail hWhole
  exact ⟨v, y, hv, hOne, hTail, hBound⟩

end AdjacentTransferChain
end Collatz2
