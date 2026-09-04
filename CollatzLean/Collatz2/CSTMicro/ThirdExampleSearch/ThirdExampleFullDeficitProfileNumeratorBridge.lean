import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleActualLast41Bridge
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ActualRecordFerrersDeficit
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ExactGapOneBeattyCertificate

/-!
# 第3例探索 2: certificate deficit と actual RecordFerrers deficit の同一化

`ExactCriticalGapOneFerrersCertificate.deficit` は任意の補助変数ではない。
minimal FirstCrossing word の actual Ferrers bands を全部足した deficit と exact に一致する。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition
open ExternalArithmetic

/--
Exact gap-one certificate の `deficit` は actual Ferrers bands の整数 deficit と一致する。
-/
theorem exactCriticalGapOne_deficit_eq_actualFerrersDeficitZ
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate w p H deficit gap m) :
    (deficit : ℤ) =
      integerFerrersDeficit p (actualFerrersBands w) := by
  have hBudget := congrArg (fun n : ℕ => (n : ℤ)) C.affine_budget
  push_cast at hBudget
  have hFerr :=
    criticalAffineConst_sub_affineConst_eq_integerFerrersDeficit C.minimal
  rw [C.oddSteps_eq] at hFerr
  linarith

/--
PureB profile numerator と certificate deficit を同一化するための proof-side predicate。
この predicate 自体は runtime row には持ち込まない。
-/
def ThirdExampleDeficitMatchesProfileNumerator
    (P : PureBProfileObstruction)
    (deficit : ℕ) : Prop :=
  (deficit : ℤ) =
    (profileDyadicCellNumerator P.m P.h : ℤ)

/-- profile numerator と同一なら certificate deficit は criticalization の exact 3-adic order を持つ。 -/
theorem exactCriticalGapOne_deficit_exactThreeAdicOrder
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    {deficit : ℕ}
    (hMatch : ThirdExampleDeficitMatchesProfileNumerator P deficit) :
    ExactThreeAdicOrder
      (deficit : ℤ)
      (P.m - P.criticalizationStart) := by
  rw [hMatch]
  exact P.profileNumerator_exactThreeAdicOrder_at_criticalization hStart

end ThirdExampleSearch
end CSTMicro
end Collatz2
