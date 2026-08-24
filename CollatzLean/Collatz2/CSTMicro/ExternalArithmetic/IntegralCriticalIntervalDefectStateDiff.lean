import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBIntegralCriticalTail
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.CriticalIntervalAffineDefect
import Mathlib.Tactic.LinearCombination

/-!
# Integral critical state における interval defect

integral critical tail state `Z_s` は arbitrary interval 上で

  2^(beta(s+r)-beta(s)) Z_(s+r)
    = 3^r Z_s + Phi[s,s+r]

を満たす。

したがって affine defect を base value `Z_s` で評価すると forcing は消え、

  F[s,s+r](Z_s)
    = 2^(beta(s+r)-beta(s)) (Z_(s+r) - Z_s)

という単純な state-difference になる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/--
integral critical state を base value に取った interval defect は、
endpoint state 差の dyadic multiple そのもの。
-/
theorem integralCriticalTail_intervalDefect_eq_pow_mul_state_sub
    (P : PureBProfileObstruction)
    {a s r : ℕ}
    (A : IsIntegralCriticalTail P a)
    (has : a ≤ s)
    (hend : s + r ≤ P.m) :
    criticalIntervalDefectZ
        s (s + r)
        (P.integralCriticalTailStateInt A s has (by omega)) =
      (2 : ℤ) ^ (beattyIndex (s + r) - beattyIndex s) *
        (P.integralCriticalTailStateInt A (s + r) (by omega) hend -
          P.integralCriticalTailStateInt A s has (by omega)) := by
  have hTransport :=
    P.integralCriticalTailStateInt_interval_transport
      A has hend
  unfold criticalIntervalDefectZ criticalIntervalGapZ
  have hLen : s + r - s = r := by omega
  rw [hLen]
  linear_combination -hTransport

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
