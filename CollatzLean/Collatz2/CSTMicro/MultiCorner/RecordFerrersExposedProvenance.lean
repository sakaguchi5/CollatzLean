import CollatzLean.Collatz2.Geometry.RecordFerrersFactorization
import CollatzLean.Collatz2.CSTMicro.MultiCorner.CarryNormalizedCheckpoint

/-!
# MultiCorner: Record--Ferrers exposed provenance

Record--Ferrers factorization が与える

  global defect = local Ferrers defect + deterministic critical carry

を CSTMicro の exposed-predecessor geometry から使うための bridge packet。

重要なのは `card E` を independent local defects の個数と同一視しないこと。
critical glue carry は `0/1` であり、local defect が zero の cut でも
`glueCarry = 1` によって global positive depth が生じうる。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

/--
一つの global cut における Record--Ferrers provenance。
既存 `Geometry.RecordFerrersFactorization` の exact identity を CSTMicro 側へ渡す最小 interface。
-/
structure RecordFerrersCutProvenance
    (P : PureBProfileObstruction)
    (k : ℕ) where
  localDefect : ℕ
  glueCarry : ℕ
  factorization :
    P.h k = localDefect + glueCarry
  glueCarry_le_one :
    glueCarry ≤ 1

namespace RecordFerrersCutProvenance

/-- exact factorization と `0/1` carry bound から bridge packet を作る。 -/
def ofFactorization
    (P : PureBProfileObstruction)
    (k localDefect glueCarry : ℕ)
    (hFactorization : P.h k = localDefect + glueCarry)
    (hCarry : glueCarry ≤ 1) :
    RecordFerrersCutProvenance P k :=
  { localDefect := localDefect
    glueCarry := glueCarry
    factorization := hFactorization
    glueCarry_le_one := hCarry }

/-- deterministic glue carry は `0` または `1`。 -/
theorem glueCarry_eq_zero_or_one
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k) :
    Q.glueCarry = 0 ∨ Q.glueCarry = 1 := by
  have hCarry : Q.glueCarry ≤ 1 :=
    Q.glueCarry_le_one
  omega

/--
positive global depth の生成源は genuine local defect または critical glue carry。
local defect と glue carry の両方が zero なのに global cell があることはない。
-/
theorem source_of_depth_pos
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k)
    (hPos : 0 < P.h k) :
    0 < Q.localDefect ∨ Q.glueCarry = 1 := by
  have hFactor := Q.factorization
  by_cases hLocal : Q.localDefect = 0
  · right
    rw [hLocal] at hFactor
    have hCarry : Q.glueCarry ≤ 1 :=
      Q.glueCarry_le_one
    omega
  · left
    omega

/-- exposed cut の positive column には local / glue の provenance が必ずある。 -/
theorem source_of_exposed
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k)
    (E : P.IsExposedPredecessorIndex k) :
    0 < Q.localDefect ∨ Q.glueCarry = 1 :=
  Q.source_of_depth_pos E.depth_pos

/-- exposed-set membership から直接 provenance dichotomy を読む形。 -/
theorem source_of_mem_exposedPredecessorSet
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k)
    (hk : k ∈ P.exposedPredecessorSet) :
    0 < Q.localDefect ∨ Q.glueCarry = 1 := by
  have E : P.IsExposedPredecessorIndex k :=
    (P.mem_exposedPredecessorSet_iff).1 hk
  exact Q.source_of_exposed E

/-- local defect が zero の exposed cut は純粋な glue-carry provenance を持つ。 -/
theorem glueCarry_eq_one_of_exposed_of_localDefect_eq_zero
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k)
    (E : P.IsExposedPredecessorIndex k)
    (hLocal : Q.localDefect = 0) :
    Q.glueCarry = 1 := by
  rcases Q.source_of_exposed E with hPos | hGlue
  · rw [hLocal] at hPos
    omega
  · exact hGlue

/-- glue carry が zero の exposed cut は genuine local Ferrers defect を持つ。 -/
theorem localDefect_pos_of_exposed_of_glueCarry_eq_zero
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k)
    (E : P.IsExposedPredecessorIndex k)
    (hGlue : Q.glueCarry = 0) :
    0 < Q.localDefect := by
  rcases Q.source_of_exposed E with hPos | hOne
  · exact hPos
  · rw [hGlue] at hOne
    omega

/-- local defect と glue carry が両方 zero なら、その cut は exposed ではない。 -/
theorem not_exposed_of_localDefect_eq_zero_of_glueCarry_eq_zero
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k)
    (hLocal : Q.localDefect = 0)
    (hGlue : Q.glueCarry = 0) :
    ¬ P.IsExposedPredecessorIndex k := by
  intro E
  have hPos := E.depth_pos
  have hFactor := Q.factorization
  rw [hLocal, hGlue] at hFactor
  omega

/--
local defect が zero なら global depth は glue carry そのものなので高々一。
175 の carry-generated global cell を表す基本形。
-/
theorem depth_le_one_of_localDefect_eq_zero
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k)
    (hLocal : Q.localDefect = 0) :
    P.h k ≤ 1 := by
  have hFactor := Q.factorization
  rw [hLocal] at hFactor
  have hCarry : Q.glueCarry ≤ 1 :=
    Q.glueCarry_le_one
  omega

/-- glue carry が zero なら global depth と genuine local defect は exact に一致する。 -/
theorem depth_eq_localDefect_of_glueCarry_eq_zero
    {P : PureBProfileObstruction}
    {k : ℕ}
    (Q : RecordFerrersCutProvenance P k)
    (hGlue : Q.glueCarry = 0) :
    P.h k = Q.localDefect := by
  have hFactor := Q.factorization
  rw [hGlue] at hFactor
  simpa using hFactor

end RecordFerrersCutProvenance

end MultiCorner
end CSTMicro
end Collatz2
