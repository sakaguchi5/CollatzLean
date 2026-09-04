import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.GapOneSuffixHenselBridge
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalAffineDefect

/-!
# 第3例探索 clean D3-1: gap-one と full critical defect の純算術 bridge

このファイルは Case II の machinery を使わない。
特に次の概念には依存しない。

* `PureBProfileObstruction`
* `criticalizationBoundary`
* Last41 / attached branch

D0/D1 の高速 modular fold が計算する
`criticalPrefixDefectZ p start` と、真の gap-one certificate が持つ
Ferrers deficit `deficit` の差から endpoint を読むための整数恒等式だけを置く。

重要な式は

  fullDefect = deficit + 2^beta * (m + 1)

および endpoint = 2m+1 を使った

  2^beta * (endpoint + 1)
    = 2 * (fullDefect - deficit)

である。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open DoubleDecomposition
open ExternalArithmetic

/--
critical roof の affine budget と critical prefix numerator は整数上で一致する。
この bridge は profile obstruction を一切使わない。
-/
theorem cleanCriticalPrefixPhiZ_eq_criticalAffineConst_cast
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

/-- gap-one start `3m+1` を critical affine defect に入れた補助量。 -/
def cleanCriticalBudgetGapOneDefectZ
    (p m : ℕ) : ℤ :=
  (Word.criticalAffineConst p : ℤ) -
    ((2 : ℤ) ^ beattyIndex p - (3 : ℤ) ^ p) *
      (gapOneStartValue m : ℤ)

/-- critical prefix defect と critical-budget 表現は exact に同じ。 -/
theorem cleanCriticalPrefixDefectZ_gapOne_eq_budget
    (p m : ℕ) :
    criticalPrefixDefectZ p (gapOneStartValue m : ℤ) =
      cleanCriticalBudgetGapOneDefectZ p m := by
  unfold criticalPrefixDefectZ criticalPrefixGapZ
    cleanCriticalBudgetGapOneDefectZ
  rw [cleanCriticalPrefixPhiZ_eq_criticalAffineConst_cast]

/--
真の gap-one certificate では full critical defect は

  deficit + 2^beta * (m+1)

に exact に整理できる。
-/
theorem cleanCriticalBudgetGapOneDefectZ_eq_deficit_add
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w p H deficit gap m) :
    cleanCriticalBudgetGapOneDefectZ p m =
      (deficit : ℤ) +
        (2 : ℤ) ^ beattyIndex p * ((m : ℤ) + 1) := by
  have hDef := congrArg (fun n : ℕ => (n : ℤ)) C.deficit_equation
  have hGap := congrArg (fun n : ℕ => (n : ℤ)) C.next_gap_equation
  push_cast at hDef hGap
  rw [C.terminalDepth_eq] at hDef hGap
  simp only [pow_succ] at hDef hGap
  unfold cleanCriticalBudgetGapOneDefectZ gapOneStartValue
  push_cast
  ring_nf at hDef hGap ⊢
  nlinarith [hDef, hGap]

/-- full critical-prefix defect の gap-one closed form。 -/
theorem cleanCriticalPrefixDefectZ_gapOne_eq_deficit_add
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w p H deficit gap m) :
    criticalPrefixDefectZ p (gapOneStartValue m : ℤ) =
      (deficit : ℤ) +
        (2 : ℤ) ^ beattyIndex p * ((m : ℤ) + 1) := by
  rw [cleanCriticalPrefixDefectZ_gapOne_eq_budget]
  exact cleanCriticalBudgetGapOneDefectZ_eq_deficit_add C

/--
endpoint `2m+1` を使った verifier 向けの exact compatibility。

  2^beta * (endpoint+1)
    = 2 * (fullDefect-deficit).
-/
theorem cleanGapOneEndpoint_fullDefect_affineCompatibility
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : ExactCriticalGapOneFerrersCertificate
      w p H deficit gap m) :
    (2 : ℤ) ^ beattyIndex p *
        ((gapOneEndpointValue m : ℤ) + 1) =
      2 *
        (criticalPrefixDefectZ p (gapOneStartValue m : ℤ) -
          (deficit : ℤ)) := by
  rw [cleanCriticalPrefixDefectZ_gapOne_eq_deficit_add C]
  unfold gapOneEndpointValue
  push_cast
  ring

/-- 上の整数恒等式を任意の modulus へ写した版。 -/
theorem cleanGapOneEndpoint_fullDefect_affineCompatibility_mod
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
    (cleanGapOneEndpoint_fullDefect_affineCompatibility C)
  simpa using h

end ThirdExampleSearch
end CSTMicro
end Collatz2
