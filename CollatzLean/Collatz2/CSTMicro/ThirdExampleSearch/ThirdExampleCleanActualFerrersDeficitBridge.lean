import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ActualRecordFerrersDeficit
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ExactGapOneBeattyCertificate

/-!
# 第3例探索 clean D3-2: certificate deficit と actual Ferrers deficit

このファイルでは `ExactCriticalGapOneFerrersCertificate` の `deficit` が、
minimal FirstCrossing word 自身の critical defect から作った
`actualFerrersBands` の重み付き deficit と exact に一致することだけを取り出す。

Case II の profile obstruction や criticalization は使わない。
したがって第三例候補から `PureBProfileObstruction` を構成する必要はない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition

/--
真の gap-one certificate の deficit は actual Ferrers deficit そのものである。
-/
theorem cleanExactCriticalGapOne_deficit_eq_actualFerrersDeficitZ
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
上の exact identity を任意の modulus へ写した版。
高速 evaluator の soundness は最終的にこの右辺へ接続すればよい。
-/
theorem cleanExactCriticalGapOne_deficit_mod_eq_actualFerrersDeficitMod
    (M : ℕ)
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate w p H deficit gap m) :
    (deficit : ZMod M) =
      (integerFerrersDeficit p (actualFerrersBands w) : ZMod M) := by
  have h := congrArg (fun z : ℤ => (z : ZMod M))
    (cleanExactCriticalGapOne_deficit_eq_actualFerrersDeficitZ C)
  simpa using h

end ThirdExampleSearch
end CSTMicro
end Collatz2
