import Mathlib.Data.Nat.Factorization.Defs

/-!
# 第3例探索 5: Record jump から Hensel boundary への局所 bridge

RecordFerrers の cut provenance では、局所 defect と glue carry を分離して保持する。
探索器に必要なのは図形全体ではなく、Hensel 側へ渡す境界 gap

  localDefect + glueCarry

だけである。

このファイルでは、その最小 exact interface を独立構造として切り出す。
既存の `RecordFerrersCutProvenance` からこの構造を作る adapter を後から追加すれば、
探索核を既存 API に依存させず利用できる。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/--
1つの Record jump が Hensel 境界へ渡す最小データ。
`glueCarry` は 0 または 1 しか取らない。
-/
structure RecordJumpData where
  localDefect : ℕ
  glueCarry : ℕ
  glueCarry_le_one : glueCarry ≤ 1

/-- Record jump が Hensel 側へ渡す境界 gap。 -/
def RecordJumpData.henselBoundaryGap (J : RecordJumpData) : ℕ :=
  J.localDefect + J.glueCarry

/-- 0/1 carry 制約を明示的な二分岐へ変換する。 -/
theorem RecordJumpData.glueCarry_eq_zero_or_one
    (J : RecordJumpData) :
    J.glueCarry = 0 ∨ J.glueCarry = 1 := by
  have hCarry : J.glueCarry ≤ 1 :=
    J.glueCarry_le_one
  omega

/--
Record jump → Hensel boundary の exact bridge。
探索状態で保持すべき gap は `localDefect + glueCarry` そのものである。
-/
theorem recordJump_henselBoundary
    (J : RecordJumpData) :
    J.henselBoundaryGap = J.localDefect + J.glueCarry := rfl

/--
したがって Hensel boundary は、carry なしなら `localDefect`、
carry ありなら `localDefect + 1` の二択しかない。
-/
theorem recordJump_henselBoundary_cases
    (J : RecordJumpData) :
    J.henselBoundaryGap = J.localDefect ∨
      J.henselBoundaryGap = J.localDefect + 1 := by
  rcases J.glueCarry_eq_zero_or_one with h0 | h1
  · left
    simp [RecordJumpData.henselBoundaryGap, h0]
  · right
    simp [RecordJumpData.henselBoundaryGap, h1]

end ThirdExampleSearch
end CSTMicro
end Collatz2
