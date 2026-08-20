import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBRelativeShiftedStateCollapse
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBShiftedWronskianElimination

/-!
# Pure B relative bridge 6: integral-state relative Wronskian

Stage 5 で variable state `Z_l` は canonical start state `Z_a` へ collapse した。
このファイルでは、その collapse を consecutive standard blocks に同時適用し、
local adjacent cross を canonical start `a` の adjacent cross へ exact に輸送する。

canonical block defect を

  B_j(a) := F[a,a+P_j](Z_a)

と置くと、まず parity を消去した unified collapse

  2^(β_l-β_a) F[l,l+P_j](Z_l)
    = 3^(l-a) B_j(a)

を得る。さらに consecutive pair では

  2^(β_l-β_a)
    [Γ_(j+1) F_j(l,Z_l) - Γ_j F_(j+1)(l,Z_l)]
  =
  3^(l-a)
    [Γ_(j+1) B_j(a) - Γ_j B_(j+1)(a)].

最後に `l=a` の既存 shifted Wronskian elimination を使うと

  2^β_a [Γ_(j+1) B_j(a) - Γ_j B_(j+1)(a)]
    = 3^(a-1) Wcorr_j

となる。これが Stage 7 の exact 3-adic propagation の入力。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/--
integral critical tail の canonical start `a` から読む standard block defect。
-/
noncomputable def integralCanonicalBlockDefect
    (P : PureBProfileObstruction)
    {a : ℕ}
    (A : IsIntegralCriticalTail P a)
    (j : ℕ) : ℤ :=
  criticalIntervalDefectZ
    a (a + criticalPowerP j)
    (P.integralCriticalTailStateInt A a le_rfl A.1)

/--
Stage 5 の odd/even collapse を parity-free に束ねる。

`a>0` は even branch を含めるために置く。
-/
theorem integralState_relativeShiftedDefectCollapse
    (P : PureBProfileObstruction)
    {a l j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hal : a ≤ l)
    (hBlockEnd : l + criticalPowerP j ≤ P.m)
    (hj : 9 ≤ j)
    (hRange :
      l + criticalPowerP j <
        criticalPowerP (j + 1)) :
    (2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
        criticalIntervalDefectZ
          l (l + criticalPowerP j)
          (P.integralCriticalTailStateInt A l hal (by omega)) =
      (3 : ℤ) ^ (l - a) *
        P.integralCanonicalBlockDefect A j := by
  have hmod : j % 2 < 2 :=
    Nat.mod_lt j (by decide)
  by_cases hjOdd : j % 2 = 1
  · simpa [integralCanonicalBlockDefect] using
      P.integralState_relativeShiftedDefectCollapse_of_odd
        (A := A)
        (hal := hal)
        (hBlockEnd := hBlockEnd)
        hj
        hjOdd
        hRange
  · have hjEven : j % 2 = 0 := by
      omega
    simpa [integralCanonicalBlockDefect] using
      P.integralState_relativeShiftedDefectCollapse_of_even
        (A := A)
        haPos
        hal
        hBlockEnd
        hj
        hjEven
        hRange

/--
consecutive local blocks の cross を canonical start `a` の cross へ輸送する。

両 block に同じ `Z_l` が入り、Stage 5 の collapse 後は同じ `Z_a` に戻る。
-/
theorem integralState_relativeAdjacentCrossTransport
    (P : PureBProfileObstruction)
    {a l j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hal : a ≤ l)
    (hBlockEndJ : l + criticalPowerP j ≤ P.m)
    (hBlockEndNext : l + criticalPowerP (j + 1) ≤ P.m)
    (hj : 9 ≤ j)
    (hRangeJ :
      l + criticalPowerP j <
        criticalPowerP (j + 1))
    (hRangeNext :
      l + criticalPowerP (j + 1) <
        criticalPowerP (j + 2)) :
    (2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
        (
          actualCriticalRawPowerGap (j + 1) *
              criticalIntervalDefectZ
                l (l + criticalPowerP j)
                (P.integralCriticalTailStateInt A l hal (by omega)) -
            actualCriticalRawPowerGap j *
              criticalIntervalDefectZ
                l (l + criticalPowerP (j + 1))
                (P.integralCriticalTailStateInt A l hal (by omega))
        ) =
      (3 : ℤ) ^ (l - a) *
        (
          actualCriticalRawPowerGap (j + 1) *
              P.integralCanonicalBlockDefect A j -
            actualCriticalRawPowerGap j *
              P.integralCanonicalBlockDefect A (j + 1)
        ) := by
  have hJ :=
    P.integralState_relativeShiftedDefectCollapse
      (A := A)
      haPos
      hal
      hBlockEndJ
      hj
      hRangeJ
  have hNext :=
    P.integralState_relativeShiftedDefectCollapse
      (A := A)
      (j := j + 1)
      haPos
      hal
      hBlockEndNext
      (by omega)
      (by
        simpa [Nat.add_assoc] using hRangeNext)
  have hJScaled :=
    congrArg
      (fun z : ℤ =>
        actualCriticalRawPowerGap (j + 1) * z)
      hJ
  have hNextScaled :=
    congrArg
      (fun z : ℤ =>
        actualCriticalRawPowerGap j * z)
      hNext
  ring_nf at hJScaled hNextScaled ⊢
  linarith

/--
canonical start state `Z_a` で読む consecutive standard blocks の
corrected Wronskian elimination。

ここでは absolute shift は `a` だけになり、RHS の 3-adic factor は exact に
`3^(a-1)`。
-/
theorem integralCanonicalBlockDefect_adjacentWronskian
    (P : PureBProfileObstruction)
    {a j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hj : 9 ≤ j)
    (hRangeJ :
      a + criticalPowerP j <
        criticalPowerP (j + 1))
    (hRangeNext :
      a + criticalPowerP (j + 1) <
        criticalPowerP (j + 2)) :
    (2 : ℤ) ^ beattyIndex a *
        (
          actualCriticalRawPowerGap (j + 1) *
              P.integralCanonicalBlockDefect A j -
            actualCriticalRawPowerGap j *
              P.integralCanonicalBlockDefect A (j + 1)
        ) =
      (3 : ℤ) ^ (a - 1) *
        correctedChristoffelWronskianNext
          actualCriticalContinuedFractionData j := by
  unfold integralCanonicalBlockDefect
  exact
    shiftedAdjacentCorrectedWronskianElimination
      hj
      haPos
      hRangeJ
      hRangeNext
      (P.integralCriticalTailStateInt A a le_rfl A.1)

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
