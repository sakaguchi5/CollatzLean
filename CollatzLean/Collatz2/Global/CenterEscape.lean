import CollatzLean.Collatz2.Global.SignDichotomy
import CollatzLean.Collatz2.Geometry.Center

/-!
# Collatz2 Global: contracting center escape

adjacent future-minimum block を displacement form の finite root へ直接接続する。
negative positive-return block の center は actual endpoint より右にあり、
negative block が cofinal なら center も任意の固定 bound より cofinally 右へ逃げる。
Matrix / Synthesis 層は介さない。
-/

namespace Collatz2
namespace AdjacentTransferChain

/-- A negative adjacent positive-return block has its finite center beyond its endpoint. -/
theorem centerBeyond_end_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    (C.transfer n).CenterBeyond (C.endValue n) := by
  have hreal :
      (C.transfer n).Realizes
        (C.startValue n) (C.endValue n) := by
    simpa [AdjacentTransferChain.transfer, Word.Realizes] using C.realizes n
  have hneg :
      (C.transfer n).determinant < 0 := by
    simpa [AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant] using hN
  have hoddCoeff : 0 < (C.transfer n).oddCoeff := by
    change 0 < 3 ^ Word.oddSteps (C.word n)
    exact Nat.pow_pos (by omega)
  exact
    hreal.centerBeyond_end_of_negative_of_increasing
      hneg (C.startValue_lt_endValue n) hoddCoeff

/--
If negative blocks are cofinal, their displacement roots escape beyond every
fixed natural bound arbitrarily late.
-/
theorem negativeCenters_cofinally_beyond
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (hN : C.NegativeDeterminantCofinal) :
    ∀ M N : ℕ,
      ∃ n : ℕ,
        N ≤ n ∧
        C.NegativeAt n ∧
        (C.transfer n).CenterBeyond M := by
  intro M N
  obtain ⟨J, hJ⟩ := C.minima.values_eventually_large M
  have hcof : Cofinal (fun n => C.NegativeAt n) := hN
  obtain ⟨n, hnmax, hnNeg⟩ := hcof (max N J)
  have hnN : N ≤ n := le_trans (le_max_left _ _) hnmax
  have hnJ : J ≤ n := le_trans (le_max_right _ _) hnmax
  have hMstart : M < C.startValue n := by
    simpa [AdjacentTransferChain.startValue,
      AdjacentTransferChain.startIndex] using hJ n hnJ
  have hMend : M < C.endValue n :=
    lt_trans hMstart (C.startValue_lt_endValue n)
  have hcenter := C.centerBeyond_end_of_negativeAt hnNeg
  rcases hcenter with ⟨hg, hevalEnd⟩
  refine ⟨n, hnN, hnNeg, ?_⟩
  have hEndOld :
      (-(C.transfer n).determinant) * (C.endValue n : ℤ) <
        ((C.transfer n).translate : ℤ) := by
    have hiff :=
      (C.transfer n).centerBeyond_iff_gap_mul_lt_translate (C.endValue n)
    exact (hiff.mp ⟨hg, hevalEnd⟩).2
  apply ((C.transfer n).centerBeyond_iff_gap_mul_lt_translate M).2
  refine ⟨hg, ?_⟩
  have hMendZ : (M : ℤ) < (C.endValue n : ℤ) := by
    exact_mod_cast hMend
  have hmul :
      (-(C.transfer n).determinant) * (M : ℤ) <
        (-(C.transfer n).determinant) * (C.endValue n : ℤ) :=
    mul_lt_mul_of_pos_left hMendZ hg
  exact lt_trans hmul hEndOld

end AdjacentTransferChain
end Collatz2
