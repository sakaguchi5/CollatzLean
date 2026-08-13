import CollatzLean.Collatz2.Global.SignDichotomy
import CollatzLean.Collatz2.Matrix.ProjectiveDynamics

/-!
# Collatz2 Synthesis: global contracting-center escape

Global future-minimum chain と Matrix fixed-point geometry をここで合流させる。

negative determinant の adjacent block は actual strict positive return なので、
その finite center は actual endpoint より右にある。
negative determinant が cofinal なら future-minimum values の発散と合わせて、
center も division-free な意味で任意の固定 bound より右へ cofinally 逃げる。
-/

namespace Collatz2
namespace Synthesis

open MatrixAnalysis

/--
negative adjacent block の finite center は
その actual endpoint より右にある。
-/
theorem centerBeyond_end_of_negativeAt
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    {n : ℕ}
    (hN : C.NegativeAt n) :
    CenterBeyond (C.transfer n) (C.endValue n) := by
  have hreal :
      (C.transfer n).Realizes
        (C.startValue n) (C.endValue n) := by
    simpa [
      AdjacentTransferChain.transfer,
      Word.Realizes
    ] using C.realizes n
  have hneg :
      (C.transfer n).determinant < 0 := by
    simpa [
      AdjacentTransferChain.NegativeAt,
      AffineTransfer.NegativeDeterminant
    ] using hN
  have hoddCoeff :
      0 < (C.transfer n).oddCoeff := by
    change 0 < 3 ^ Word.oddSteps (C.word n)
    exact Nat.pow_pos (by omega)
  exact
    AffineTransfer.Realizes.centerBeyond_end_of_negative_of_increasing
      hreal
      hneg
      (C.startValue_lt_endValue n)
      hoddCoeff

/--
negative determinant が cofinal なら、その finite centers は division-free な意味で
任意の固定自然数 bound `M` より arbitrarily late に右へ出る。

`CenterBeyond T M` は `g = A-C > 0` に対する `g*M < B` を意味する。
-/
theorem AdjacentTransferChain.negativeCenters_cofinally_beyond
    {O : OddOrbit}
    (C : AdjacentTransferChain O)
    (hN : C.NegativeDeterminantCofinal) :
    ∀ M N : ℕ,
      ∃ n : ℕ,
        N ≤ n ∧
        C.NegativeAt n ∧
        CenterBeyond (C.transfer n) M := by
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
  have hcenter := centerBeyond_end_of_negativeAt C hnNeg
  rcases hcenter with ⟨hg, hgend⟩
  refine ⟨n, hnN, hnNeg, ?_⟩
  refine ⟨hg, ?_⟩
  have hMendZ : (M : ℤ) < (C.endValue n : ℤ) := by
    exact_mod_cast hMend
  have hmul :
      (-(C.transfer n).determinant) * (M : ℤ) <
        (-(C.transfer n).determinant) * (C.endValue n : ℤ) :=
    mul_lt_mul_of_pos_left hMendZ hg
  exact lt_trans hmul hgend

end Synthesis
end Collatz2
