import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFiniteDeficitBranch
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBProfileNumeratorValuation
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedCanonicalHenselBridge

/-!
# 第3例探索 1: actual attached data から最後41列座標へ

このファイルでは `last41` を単なる座標 field として扱わず、
profile numerator の exact 3-adic order と `3^42` 非整除から導く。

残る外部入力は `3^42 ∤ N(h)` だけである。これは後段の有限 residue
checker が供給すべき固定精度の排除条件であり、ここでは捏造しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

open ExternalArithmetic
open MultiCorner

/-- 第3例 target で「42段以上の criticalization depth」を排除する固定精度条件。 -/
def ThirdExampleProfileNumeratorNotDivisible42
    (P : PureBProfileObstruction) : Prop :=
  ¬ (3 : ℤ) ^ 42 ∣
    (profileDyadicCellNumerator P.m P.h : ℤ)

/--
positive criticalization start と `3^42` 非整除から、criticalization depth は42未満。
exact 3-adic order を使うので情報損失はない。
-/
theorem criticalizationDepth_lt_42_of_notDivisible42
    (P : PureBProfileObstruction)
    (hStart : 0 < P.criticalizationStart)
    (h42 : ThirdExampleProfileNumeratorNotDivisible42 P) :
    P.m - P.criticalizationStart < 42 := by
  have hExact :=
    P.profileNumerator_exactThreeAdicOrder_at_criticalization hStart
  by_contra hNot
  have hLe : 42 ≤ P.m - P.criticalizationStart := by omega
  have hPow :
      (3 : ℤ) ^ 42 ∣
        (3 : ℤ) ^ (P.m - P.criticalizationStart) := by
    refine ⟨(3 : ℤ) ^ ((P.m - P.criticalizationStart) - 42), ?_⟩
    have hExp :
        42 + ((P.m - P.criticalizationStart) - 42) =
          P.m - P.criticalizationStart := by
      omega
    rw [← pow_add, hExp]
  exact h42 (hPow.trans hExact.1)

/--
actual attached packet から executable last-41 座標を構成する。

`c` は terminal critical start、`s` は criticalization start、
`w` は attached straight width とする。
-/
def thirdExampleLast41Coordinates_of_actualAttached
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hTarget : P.m = thirdExampleTargetP)
    (hStart : 0 < P.criticalizationStart)
    (h42 : ThirdExampleProfileNumeratorNotDivisible42 P) :
    ThirdExampleLast41TailCoordinates := by
  let c := P.terminalCriticalStart
  let s := P.criticalizationStart
  let r := thirdExampleTargetP - c
  let d := c - s
  let w := A.straightHenselWidth
  have hsc : s ≤ c := by
    dsimp [s, c]
    exact P.criticalizationStart_le_terminalCriticalStart
  have hcm : c ≤ P.m := by
    dsimp [c]
    exact P.terminalCriticalStart_spec.1
  have hct : c ≤ thirdExampleTargetP := by
    rw [← hTarget]
    exact hcm
  have hLastP :
      P.m - P.criticalizationStart < 42 :=
    criticalizationDepth_lt_42_of_notDivisible42
      P hStart h42
  have hLast :
      thirdExampleTargetP - s < 42 := by
    dsimp [s]
    rw [← hTarget]
    exact hLastP
  have hPrev : s ≤ A.normalForm.previous := by
    dsimp [s]
    exact A.criticalization_le_previous
  have hEnd := A.straightHenselStart_add_width
  have hWidth : w + 1 ≤ d := by
    dsimp [w, d, c, s]
    unfold AttachedTwoCornerPacket.straightHenselStart at hEnd
    omega
  exact {
    c := c
    s := s
    r := r
    d := d
    w := w
    s_le_c := hsc
    c_le_target := hct
    r_eq := rfl
    d_eq := rfl
    last41 := hLast
    attached_width := hWidth
  }
/-- actual attached packet の `(r,d,w)` は12,341枝の有限 domain に必ず入る。 -/
theorem thirdExampleActualAttached_RDW_mem
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hTarget : P.m = thirdExampleTargetP)
    (hStart : 0 < P.criticalizationStart)
    (h42 : ThirdExampleProfileNumeratorNotDivisible42 P) :
    thirdExampleRDWOfLast41
        (thirdExampleLast41Coordinates_of_actualAttached A hTarget hStart h42) ∈
      thirdExampleFiniteDeficitBranches := by
  exact thirdExampleRDWOfLast41_mem _

end ThirdExampleSearch
end CSTMicro
end Collatz2
