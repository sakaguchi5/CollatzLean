import CollatzLean.Collatz2.Orbit.RealizationRecovery
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.RecordCarryCorrectionPhi

/-!
# Ferrers deficit 方程式から gap-one paradoxical packet へ

Record/Ferrers 側で作った deficit `D` が critical affine budget をちょうど調整し、

  3^p + Bcrit = 2^H + D + m*G,
  3^(p+1) + G = 2^(H+1)

を満たすとする。さらに actual word の affine constant `B` が

  B + D = Bcrit

なら、開始値 `3m+1` はその word を通って `2m+1` へ落ちる。
次の exponent-1 step は exact に `3m+2 = (3m+1)+1` へ戻る。

これは 7 や 91 で見える「first drop の直後に start+1」という gap-one 型を
抽象 certificate から復元する定理である。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

/--
第3例構成に必要な arithmetic/Ferrers certificate。
`deficit` の作り方自体は前段の Record 分解に任せ、この packet は最後の接続だけを担う。
-/
structure GapOneFerrersDeficitCertificate
    (w : Word)
    (p H Bcrit deficit gap m : ℕ) : Prop where
  valid : w.Valid
  oddSteps_eq : Word.oddSteps w = p
  twoSteps_eq : Word.twoSteps w = H
  affine_budget : Word.affineConst w + deficit = Bcrit
  deficit_equation :
    3 ^ p + Bcrit = 2 ^ H + deficit + m * gap
  next_gap_equation :
    3 ^ (p + 1) + gap = 2 ^ (H + 1)
  multiplier_pos : 0 < m

/-- Ferrers deficit certificate から whole affine realization を得る。 -/
theorem realizes_gapOne_of_ferrersDeficitEquation
    {w : Word}
    {p H Bcrit deficit gap m : ℕ}
    (C : GapOneFerrersDeficitCertificate
      w p H Bcrit deficit gap m) :
    Word.Realizes w (3 * m + 1) (2 * m + 1) := by
  have hBudgetWithDeficit :
      (3 ^ p + Word.affineConst w) + deficit =
        (2 ^ H + m * gap) + deficit := by
    calc
      (3 ^ p + Word.affineConst w) + deficit
          = 3 ^ p + (Word.affineConst w + deficit) := by ac_rfl
      _ = 3 ^ p + Bcrit := by rw [C.affine_budget]
      _ = 2 ^ H + deficit + m * gap := C.deficit_equation
      _ = (2 ^ H + m * gap) + deficit := by ac_rfl
  have hBudget :
      3 ^ p + Word.affineConst w = 2 ^ H + m * gap :=
    Nat.add_right_cancel hBudgetWithDeficit
  apply (Word.realizes_iff w (3 * m + 1) (2 * m + 1)).2
  rw [C.twoSteps_eq, C.oddSteps_eq]
  calc
    2 ^ H * (2 * m + 1)
        = 2 ^ H + m * 2 ^ (H + 1) := by
            rw [pow_succ]
            ring
    _ = 2 ^ H + m * (3 ^ (p + 1) + gap) := by
            rw [C.next_gap_equation]
    _ = (2 ^ H + m * gap) + 3 ^ p * (3 * m) := by
            rw [pow_succ]
            ring
    _ = (3 ^ p + Word.affineConst w) + 3 ^ p * (3 * m) := by
            rw [← hBudget]
    _ = 3 ^ p * (3 * m + 1) + Word.affineConst w := by
            ring

/--
Ferrers deficit 方程式から genuine `Runs` と gap-one return を同時に得る。

結論:

* `w` に沿って `3m+1 -> 2m+1` が actual normalized run。
* endpoint は start より strict に小さい。
* その直後の exponent-1 step は `2m+1 -> 3m+2 = start+1`。
-/
theorem gapOneParadoxical_of_ferrersDeficitEquation
    {w : Word}
    {p H Bcrit deficit gap m : ℕ}
    (C : GapOneFerrersDeficitCertificate
      w p H Bcrit deficit gap m) :
    Runs w (3 * m + 1) (2 * m + 1) ∧
      2 * m + 1 < 3 * m + 1 ∧
      Word.Realizes ([1] : Word) (2 * m + 1) (3 * m + 2) := by
  have hReal :
      Word.Realizes w (3 * m + 1) (2 * m + 1) :=
    realizes_gapOne_of_ferrersDeficitEquation C
  have hOdd : Odd (2 * m + 1) := by
    exact ⟨m, by omega⟩
  have hRun : Runs w (3 * m + 1) (2 * m + 1) :=
    Word.Realizes.toRuns_of_valid_of_end_odd hReal C.valid hOdd
  refine ⟨hRun, ?_, ?_⟩
  · have hmPos : 0 < m := C.multiplier_pos
    omega
  · apply (Word.realizes_singleton_iff 1 (2 * m + 1) (3 * m + 2)).2
    norm_num
    ring

end DoubleDecomposition
end CSTMicro
end Collatz2
