import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBIntegralCriticalTail

/-!
# Pure B: integral critical tail state と shifted affine defect

arithmetic critical tail の integer state transport

  2^(β(t)-β(s)) Z_t = 3^(t-s) Z_s + Φ[s,t]

を affine defect

  F[s,t](z) = Φ[s,t] - (2^(β(t)-β(s)) - 3^(t-s)) z

へ代入すると、同じ interval defect は左 endpoint state / 右 endpoint state で
それぞれ

  F[s,t](Z_s) = 2^(β(t)-β(s)) (Z_t - Z_s),
  F[s,t](Z_t) = 3^(t-s)              (Z_t - Z_s)

と exact に読める。

この2式は、同じ parameter を使う Wronskian elimination と high 3-adic depth を
同時に取れない理由を pure integer identity として固定する checkpoint である。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-- integral tail の interval defect を左 endpoint state で評価した exact form。 -/
theorem criticalIntervalDefectZ_at_integralLeftState
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
    P.integralCriticalTailStateInt_interval_transport A has hend
  have hLen : s + r - s = r := by omega
  unfold criticalIntervalDefectZ criticalIntervalGapZ
  rw [hLen]
  ring_nf at hTransport ⊢
  linarith

/-- integral tail の interval defect を右 endpoint state で評価した exact form。 -/
theorem criticalIntervalDefectZ_at_integralRightState
    (P : PureBProfileObstruction)
    {a s r : ℕ}
    (A : IsIntegralCriticalTail P a)
    (has : a ≤ s)
    (hend : s + r ≤ P.m) :
    criticalIntervalDefectZ
        s (s + r)
        (P.integralCriticalTailStateInt A (s + r) (by omega) hend) =
      (3 : ℤ) ^ r *
        (P.integralCriticalTailStateInt A (s + r) (by omega) hend -
          P.integralCriticalTailStateInt A s has (by omega)) := by
  have hTransport :=
    P.integralCriticalTailStateInt_interval_transport A has hend
  have hLen : s + r - s = r := by omega
  unfold criticalIntervalDefectZ criticalIntervalGapZ
  rw [hLen]
  ring_nf at hTransport ⊢
  linarith

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
