import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.GapOneSuffixHenselBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalAffineDefect

/-!
# 第3例探索: full defect と gap-one endpoint の exact affine compatibility

finite deficit evaluator が返す Ferrers deficit と、D0/D1 が返す full critical-prefix
defect を endpoint residue に接続するための整数恒等式を固定する。

重要なのは、`fullDefect = deficit` を仮定しないことである。
差 `fullDefect - deficit` に critical power `2^β` が掛かる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition
open ExternalArithmetic

/-- critical roof の Nat affine budget は critical prefix numerator の Int 版と一致する。 -/
theorem criticalPrefixPhiZ_eq_criticalAffineConst_cast
    (p : ℕ) :
    criticalPrefixPhiZ p = (Word.criticalAffineConst p : ℤ) := by
  classical
  unfold criticalPrefixPhiZ Word.criticalAffineConst
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hkLt : k < p := Finset.mem_range.mp hk
  unfold Word.criticalAffineTerm
  rw [DoubleDecomposition.criticalHeight_eq_beattyIndex]
  have hSub : p - (k + 1) = p - 1 - k := by
    omega
  rw [hSub]
  simp

/--
gap-one start を critical affine defect に代入した式を、critical budget で書いた補助量。
-/
def criticalBudgetGapOneDefectZ
    (p m : ℕ) : ℤ :=
  (Word.criticalAffineConst p : ℤ) -
    ((2 : ℤ) ^ beattyIndex p - (3 : ℤ) ^ p) *
      (gapOneStartValue m : ℤ)

/-- critical prefix defect と critical-budget 表現は exact に同じ。 -/
theorem criticalPrefixDefectZ_gapOne_eq_budget
    (p m : ℕ) :
    criticalPrefixDefectZ p (gapOneStartValue m : ℤ) =
      criticalBudgetGapOneDefectZ p m := by
  unfold criticalPrefixDefectZ criticalPrefixGapZ criticalBudgetGapOneDefectZ
  rw [criticalPrefixPhiZ_eq_criticalAffineConst_cast]

/--
Exact gap-one certificate では full critical defect は

  deficit + 2^β (m+1)

へ exact に整理できる。
-/
theorem criticalBudgetGapOneDefectZ_eq_deficit_add
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w p H deficit gap m) :
    criticalBudgetGapOneDefectZ p m =
      (deficit : ℤ) +
        (2 : ℤ) ^ beattyIndex p * ((m : ℤ) + 1) := by
  have hDef := congrArg (fun n : ℕ => (n : ℤ)) C.deficit_equation
  have hGap := congrArg (fun n : ℕ => (n : ℤ)) C.next_gap_equation
  push_cast at hDef hGap
  rw [C.terminalDepth_eq] at hDef hGap
  simp only [pow_succ] at hDef hGap
  unfold criticalBudgetGapOneDefectZ gapOneStartValue
  push_cast
  ring_nf at hDef hGap ⊢
  nlinarith [hDef, hGap]

/-- full critical-prefix defect の gap-one closed form。 -/
theorem criticalPrefixDefectZ_gapOne_eq_deficit_add
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w p H deficit gap m) :
    criticalPrefixDefectZ p (gapOneStartValue m : ℤ) =
      (deficit : ℤ) +
        (2 : ℤ) ^ beattyIndex p * ((m : ℤ) + 1) := by
  rw [criticalPrefixDefectZ_gapOne_eq_budget]
  exact criticalBudgetGapOneDefectZ_eq_deficit_add C

/--
endpoint `2m+1` を消去した verifier 向け exact compatibility。

  2^β (endpoint+1) = 2 (fullDefect-deficit).
-/
theorem gapOneEndpoint_fullDefect_affineCompatibility
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w p H deficit gap m) :
    (2 : ℤ) ^ beattyIndex p *
        ((gapOneEndpointValue m : ℤ) + 1) =
      2 *
        (criticalPrefixDefectZ p (gapOneStartValue m : ℤ) -
          (deficit : ℤ)) := by
  rw [criticalPrefixDefectZ_gapOne_eq_deficit_add C]
  unfold gapOneEndpointValue
  push_cast
  ring

/-- 上の exact identity は任意の modulus へ lossless に写せる。 -/
theorem gapOneEndpoint_fullDefect_affineCompatibility_mod
    (M : ℕ)
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w p H deficit gap m) :
    ((2 : ZMod M) ^ beattyIndex p) *
        ((gapOneEndpointValue m : ZMod M) + 1) =
      2 *
        ((criticalPrefixDefectZ p (gapOneStartValue m : ℤ) : ZMod M) -
          (deficit : ZMod M)) := by
  have h := congrArg (fun z : ℤ => (z : ZMod M))
    (gapOneEndpoint_fullDefect_affineCompatibility C)
  simpa using h

end ThirdExampleSearch
end CSTMicro
end Collatz2
