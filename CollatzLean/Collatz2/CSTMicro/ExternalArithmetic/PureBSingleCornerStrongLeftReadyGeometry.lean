import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerLeftLocalizationLog14
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerLargeMReduction
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerBeattyTwoStep

/-!
# Pure B single-corner: Beatty lower slope -> sharpened StrongLeftReady

Beatty two-step theorem

  beta(k+2) >= beta(k)+3

を反復し、

  k + floor(k/2) <= beta(k)

を得る。

`t=m-b` と置くと `3t+1<=m` は `2t<=b-1` を意味するため

  beta(b-1) >= m-1.

Xi threshold が 118 へ下がったので、`m>=119` なら

  118 <= beta(b-1),
  m+1 <= beta(b-1)+2

が同時に成立する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/-- critical Beatty index の explicit `3/2` 型 lower slope。 -/
theorem beattyIndex_ge_index_add_half
    (k : ℕ) :
    k + k / 2 ≤ beattyIndex k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp [beattyIndex_zero]
      by_cases hk1 : k = 1
      · subst k
        have hStep := beattyIndex_add_le 0 1
        simpa [beattyIndex_zero] using hStep
      let n := k - 2
      have hnLt : n < k := by
        dsimp [n]
        omega
      have hkEq : n + 2 = k := by
        dsimp [n]
        omega
      have hIH := ih n hnLt
      have hTwo := beattyIndex_add_two_ge_add_three n
      rw [hkEq] at hTwo
      omega

namespace PureBProfileObstruction.SingleExposedCornerRigidityPacket

/-- `3*(m-b)+1<=m` なら left precision は `m-1` 以上。 -/
theorem m_pred_le_strongLeftPrecision_of_three_tail
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    (hThird : 3 * (P.m - S.b) + 1 ≤ P.m) :
    P.m - 1 ≤ S.strongLeftPrecision := by
  have hbLeM : S.b ≤ P.m :=
    le_trans (Nat.le_of_lt S.b_lt_c) P.terminalCriticalStart_spec.1
  have hDecomp : S.b + (P.m - S.b) = P.m :=
    Nat.add_sub_of_le hbLeM
  have hTwoTail : 2 * (P.m - S.b) ≤ S.b - 1 := by
    omega
  have hHalf : P.m - S.b ≤ (S.b - 1) / 2 := by
    omega
  have hBeat := beattyIndex_ge_index_add_half (S.b - 1)
  unfold strongLeftPrecision
  have hbPos := S.b_pos
  have hSum :
      P.m - 1 = (S.b - 1) + (P.m - S.b) := by
    omega
  rw [hSum]
  exact le_trans (Nat.add_le_add_left hHalf _) hBeat

/-- `m>=119` と terminal-third condition から sharpened StrongLeftReady。 -/
theorem strongLeftReady_of_large_and_three_tail
    {P : PureBProfileObstruction}
    (S : P.SingleExposedCornerRigidityPacket)
    (hmLarge : 119 ≤ P.m)
    (hThird : 3 * (P.m - S.b) + 1 ≤ P.m) :
    S.StrongLeftReady := by
  have hPrec := S.m_pred_le_strongLeftPrecision_of_three_tail hThird
  constructor
  · exact le_trans (by omega : 118 ≤ P.m - 1) hPrec
  · omega

end PureBProfileObstruction.SingleExposedCornerRigidityPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
