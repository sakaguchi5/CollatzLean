import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.RecordJumpHenselBoundary
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RecordFerrersExposedProvenance

/-!
# 第3例探索 次段 4: 本物の RecordFerrers provenance を探索 jump へ接続

前段の `RecordJumpData` は探索器を既存 API から独立に保つための最小 interface だった。
ここでは実際の

  `MultiCorner.RecordFerrersCutProvenance`

からその interface を lossless に作る。

実 provenance が持つ

  P.h k = localDefect + glueCarry

をそのまま使うため、探索側の Hensel boundary gap は global profile depth `P.h k`
と exact に一致する。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic

/-- 実際の RecordFerrers cut provenance を探索用 jump data へ忘却する。 -/
def recordJumpDataOfProvenance
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : MultiCorner.RecordFerrersCutProvenance P k) :
    RecordJumpData :=
  { localDefect := Q.localDefect
    glueCarry := Q.glueCarry
    glueCarry_le_one := Q.glueCarry_le_one }

@[simp] theorem recordJumpDataOfProvenance_localDefect
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : MultiCorner.RecordFerrersCutProvenance P k) :
    (recordJumpDataOfProvenance Q).localDefect = Q.localDefect := rfl

@[simp] theorem recordJumpDataOfProvenance_glueCarry
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : MultiCorner.RecordFerrersCutProvenance P k) :
    (recordJumpDataOfProvenance Q).glueCarry = Q.glueCarry := rfl

/--
本物の provenance から得た探索 boundary gap は、global profile depth `P.h k` そのもの。
-/
theorem recordJumpDataOfProvenance_henselBoundaryGap_eq_profileDepth
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : MultiCorner.RecordFerrersCutProvenance P k) :
    (recordJumpDataOfProvenance Q).henselBoundaryGap = P.h k := by
  unfold recordJumpDataOfProvenance RecordJumpData.henselBoundaryGap
  exact Q.factorization.symm

/--
したがって実 provenance の boundary gap も、local defect または local defect+1 の二択。
-/
theorem recordJumpDataOfProvenance_boundary_cases
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : MultiCorner.RecordFerrersCutProvenance P k) :
    P.h k = Q.localDefect ∨
      P.h k = Q.localDefect + 1 := by
  rcases Q.glueCarry_eq_zero_or_one with h0 | h1
  · left
    rw [Q.factorization, h0]
    simp
  · right
    rw [Q.factorization, h1]

end ThirdExampleSearch
end CSTMicro
end Collatz2
