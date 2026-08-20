import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBRelativeShiftedDictionaryEven

/-!
# Pure B relative bridge 5: integral state による common-parameter collapse

relative shifted dictionary に `y = Z_l` を入れる。
endpoint-state identity により

  F[a,l](Z_l) = 3^(l-a) (Z_l - Z_a),

一方 standard block gap は `Γ_j` なので

  F[a,a+P_j](Z_l) + Γ_j (Z_l-Z_a)
    = F[a,a+P_j](Z_a).

従って odd/even の両 branch で

  2^(β(l)-β(a)) F[l,l+P_j](Z_l)
    = 3^(l-a) F[a,a+P_j](Z_a).

可変 state `Z_l` が canonical start state `Z_a` 一個へ exact に collapse する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace PureBProfileObstruction

/-- odd branch の integral-state relative collapse。 -/
theorem integralState_relativeShiftedDefectCollapse_of_odd
    (P : PureBProfileObstruction)
    {a l j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (hal : a ≤ l)
    (hBlockEnd : l + criticalPowerP j ≤ P.m)
    (hj : 9 ≤ j)
    (hjOdd : j % 2 = 1)
    (hRange :
      l + criticalPowerP j <
        criticalPowerP (j + 1)) :
    (2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
        criticalIntervalDefectZ
          l (l + criticalPowerP j)
          (P.integralCriticalTailStateInt A l hal (by omega)) =
      (3 : ℤ) ^ (l - a) *
        criticalIntervalDefectZ
          a (a + criticalPowerP j)
          (P.integralCriticalTailStateInt A a le_rfl A.1) := by
  have hlm : l ≤ P.m := by
    omega
  let Za :=
    P.integralCriticalTailStateInt A a le_rfl A.1
  let Zl :=
    P.integralCriticalTailStateInt A l hal hlm
  change
    (2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
        criticalIntervalDefectZ
          l (l + criticalPowerP j) Zl =
      (3 : ℤ) ^ (l - a) *
        criticalIntervalDefectZ
          a (a + criticalPowerP j) Za
  have hRel :=
    relativeShiftedDefectDictionary_of_odd
      hj hjOdd hal hRange Zl
  have hState0 :=
    P.criticalIntervalDefectZ_eq_endpointStateDifference
      (A := A)
      (s := a)
      (t := l)
      le_rfl
      hal
      hlm
      Zl
  have hState0 :=
    P.criticalIntervalDefectZ_eq_endpointStateDifference
      (A := A)
      (s := a)
      (t := l)
      le_rfl
      hal
      hlm
      Zl
  have hZaEq :
      P.integralCriticalTailStateInt A a
          le_rfl
          (le_trans hal hlm) =
        Za := by
    dsimp [Za]
  have hZlEq :
      P.integralCriticalTailStateInt A l
          (le_trans le_rfl hal)
          hlm =
        Zl := by
    dsimp [Zl]
  have hState :
      criticalIntervalDefectZ a l Zl =
        (3 : ℤ) ^ (l - a) * (Zl - Za) := by
    rw [hState0]
    rw [hZaEq, hZlEq]
    ring
  have hRangeA :
      a + criticalPowerP j <
        criticalPowerP (j + 1) := by
    omega
  have hGap :=
    criticalIntervalGapZ_add_currentP_eq_rawGap_of_odd
      hj hjOdd hRangeA
  have hAffine :
      criticalIntervalDefectZ
          a (a + criticalPowerP j) Zl +
        actualCriticalRawPowerGap j * (Zl - Za) =
      criticalIntervalDefectZ
          a (a + criticalPowerP j) Za := by
    unfold criticalIntervalDefectZ
    rw [hGap]
    ring
  calc
    (2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
        criticalIntervalDefectZ
          l (l + criticalPowerP j) Zl =
      (3 : ℤ) ^ (l - a) *
          criticalIntervalDefectZ
            a (a + criticalPowerP j) Zl +
        actualCriticalRawPowerGap j *
          criticalIntervalDefectZ a l Zl := hRel
    _ =
      (3 : ℤ) ^ (l - a) *
        (criticalIntervalDefectZ
            a (a + criticalPowerP j) Zl +
          actualCriticalRawPowerGap j * (Zl - Za)) := by
            rw [hState]
            ring
    _ =
      (3 : ℤ) ^ (l - a) *
        criticalIntervalDefectZ
          a (a + criticalPowerP j) Za := by
            rw [hAffine]

/-- even branch の integral-state relative collapse。 -/
theorem integralState_relativeShiftedDefectCollapse_of_even
    (P : PureBProfileObstruction)
    {a l j : ℕ}
    (A : IsIntegralCriticalTail P a)
    (haPos : 0 < a)
    (hal : a ≤ l)
    (hBlockEnd : l + criticalPowerP j ≤ P.m)
    (hj : 9 ≤ j)
    (hjEven : j % 2 = 0)
    (hRange :
      l + criticalPowerP j <
        criticalPowerP (j + 1)) :
    (2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
        criticalIntervalDefectZ
          l (l + criticalPowerP j)
          (P.integralCriticalTailStateInt A l hal (by omega)) =
      (3 : ℤ) ^ (l - a) *
        criticalIntervalDefectZ
          a (a + criticalPowerP j)
          (P.integralCriticalTailStateInt A a le_rfl A.1) := by
  have hlm : l ≤ P.m := by
    omega
  let Za :=
    P.integralCriticalTailStateInt A a le_rfl A.1
  let Zl :=
    P.integralCriticalTailStateInt A l hal hlm
  change
    (2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
        criticalIntervalDefectZ
          l (l + criticalPowerP j) Zl =
      (3 : ℤ) ^ (l - a) *
        criticalIntervalDefectZ
          a (a + criticalPowerP j) Za
  have hRel :=
    relativeShiftedDefectDictionary_of_even
      hj hjEven haPos hal hRange Zl
  have hState0 :=
    P.criticalIntervalDefectZ_eq_endpointStateDifference
      (A := A)
      (s := a)
      (t := l)
      le_rfl
      hal
      hlm
      Zl
  have hState0 :=
    P.criticalIntervalDefectZ_eq_endpointStateDifference
      (A := A)
      (s := a)
      (t := l)
      le_rfl
      hal
      hlm
      Zl
  have hZaEq :
      P.integralCriticalTailStateInt A a
          le_rfl
          (le_trans hal hlm) =
        Za := by
    dsimp [Za]
  have hZlEq :
      P.integralCriticalTailStateInt A l
          (le_trans le_rfl hal)
          hlm =
        Zl := by
    dsimp [Zl]
  have hState :
      criticalIntervalDefectZ a l Zl =
        (3 : ℤ) ^ (l - a) * (Zl - Za) := by
    rw [hState0]
    rw [hZaEq, hZlEq]
    ring
  have hRangeA :
      a + criticalPowerP j <
        criticalPowerP (j + 1) := by
    omega
  have hGap :=
    criticalIntervalGapZ_add_currentP_eq_rawGap_of_even
      hj hjEven haPos hRangeA
  have hAffine :
      criticalIntervalDefectZ
          a (a + criticalPowerP j) Zl +
        actualCriticalRawPowerGap j * (Zl - Za) =
      criticalIntervalDefectZ
          a (a + criticalPowerP j) Za := by
    unfold criticalIntervalDefectZ
    rw [hGap]
    ring
  calc
    (2 : ℤ) ^ (beattyIndex l - beattyIndex a) *
        criticalIntervalDefectZ
          l (l + criticalPowerP j) Zl =
      (3 : ℤ) ^ (l - a) *
          criticalIntervalDefectZ
            a (a + criticalPowerP j) Zl +
        actualCriticalRawPowerGap j *
          criticalIntervalDefectZ a l Zl := hRel
    _ =
      (3 : ℤ) ^ (l - a) *
        (criticalIntervalDefectZ
            a (a + criticalPowerP j) Zl +
          actualCriticalRawPowerGap j * (Zl - Za)) := by
            rw [hState]
            ring
    _ =
      (3 : ℤ) ^ (l - a) *
        criticalIntervalDefectZ
          a (a + criticalPowerP j) Za := by
            rw [hAffine]

end PureBProfileObstruction

end ExternalArithmetic
end CSTMicro
end Collatz2
