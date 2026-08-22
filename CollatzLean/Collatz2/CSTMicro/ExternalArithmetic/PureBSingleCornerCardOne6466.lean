import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerExactBHZFiniteBands
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerLog196EventualThreshold
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerStrongLeftReadyGeometry
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerActualLeftPrefix

set_option linter.style.emptyLine false
set_option exponentiation.threshold 300

/-!
# Pure B single-corner: `m >= 6466` の threshold-free card-one elimination

canonical dyadic scale

  ell = log_2(m+1) + 1

を選ぶ。`m >= 6466` なら `ell >= 13`。

* ell = 13        : exact BHZ width `m-b <= 2155`
* 14 <= ell <= 19 : exact BHZ width `m-b <= 2245`
* 20 <= ell <= 43 : exact BHZ width `m-b <= 33195`
* 44 <= ell <= 5287 : exact BHZ width `m-b <= 460397`
* ell >= 5288     : degree-196 route の eventual threshold

に分ける。

前4領域ではすべて `3*(m-b)+1 <= m` を直接得て StrongLeftReady と Xi contradiction
へ接続する。最後の領域だけ既存 BHZ196 closure を遠方 fallback として使う。

従って card-one actual branch は追加の dyadic threshold 仮定なしで

  6466 <= m -> False

まで閉じる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MinimalActualABObstructionPacket

/--
明示 width `B` が `m/3` 以下なら、既存 StrongLeftReady + actual left divisibility + Xi
contradiction を一括して適用する補助定理。
-/
theorem singleCorner_impossible_of_explicit_width
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (S :
      (M.toPureBProfileObstruction hL).SingleExposedCornerRigidityPacket)
    {B : ℕ}
    (hmLarge : 119 <= (M.toPureBProfileObstruction hL).m)
    (hWidth :
      (M.toPureBProfileObstruction hL).m - S.b <= B)
    (hThreshold :
      3 * B + 1 <= (M.toPureBProfileObstruction hL).m) :
    False := by
  let P := M.toPureBProfileObstruction hL
  have hThird :
      3 * (P.m - S.b) + 1 <= P.m := by
    have hMul :
        3 * (P.m - S.b) <= 3 * B :=
      Nat.mul_le_mul_left 3 (by simpa [P] using hWidth)
    have hThreshold' : 3 * B + 1 <= P.m := by
      simpa [P] using hThreshold
    omega
  have hReady : S.StrongLeftReady :=
    S.strongLeftReady_of_large_and_three_tail
      (by simpa [P] using hmLarge)
      hThird
  have hDivRaw := M.singleCorner_leftPrefixDivisibility hL S
  have hDiv : M.SingleCornerLeftPrefixDivisibility hL S := by
    simpa [MinimalActualABObstructionPacket.SingleCornerLeftPrefixDivisibility]
      using hDivRaw
  exact M.singleCorner_impossible_of_strongLeftReady R hL S hDiv hReady

/--
actual card-one branch は `m >= 6466` なら不可能。

この theorem の statement には `ell` も polynomial threshold も現れない。
-/
theorem singleCorner_card_one_impossible_of_m_ge_6466
    (R : RhinLinearForm14)
    {L : ℕ}
    (M : MinimalActualABObstructionPacket L)
    (hL : 2 < L)
    (hCard :
      (M.toPureBProfileObstruction hL).exposedPredecessorSet.card = 1)
    (hm :
      6466 <= (M.toPureBProfileObstruction hL).m) :
    False := by
  let P := M.toPureBProfileObstruction hL
  let S := M.toSingleExposedCornerRigidityPacket R hL hCard
  let ell : ℕ := Nat.log 2 (P.m + 1) + 1

  have hmLarge : 119 <= P.m := by
    simpa [P] using le_trans (by norm_num : 119 <= 6466) hm

  have hmSize : P.m + 1 <= 2 ^ ell := by
    have hlt :
        P.m + 1 < 2 ^ (Nat.log 2 (P.m + 1) + 1) := by
      simpa using
        Nat.lt_pow_succ_log_self
          (by decide : 1 < (2 : ℕ))
          (P.m + 1)
    dsimp [ell]
    exact Nat.le_of_lt hlt

  have hmLogLower :
      2 ^ (ell - 1) <= P.m + 1 := by
    have h :=
      Nat.pow_log_le_self 2
        (show P.m + 1 ≠ 0 by omega)
    dsimp [ell]
    simpa using h

  have hellThirteen : 13 <= ell := by
    have hPow12 : 2 ^ 12 <= P.m + 1 := by
      have hm' : 6466 <= P.m := by simpa [P] using hm
      norm_num
      omega
    have hLog12 :
        12 <= Nat.log 2 (P.m + 1) :=
      Nat.le_log_of_pow_le
        (by decide : 1 < (2 : ℕ)) hPow12
    dsimp [ell]
    omega

  by_cases h13 : ell = 13
  · have hmSize13 : P.m + 1 <= 2 ^ 13 := by
      simpa [h13] using hmSize
    have hWidth : P.m - S.b <= 2155 := by
      simpa [P] using
        M.singleCorner_m_sub_b_le_2155_of_ell_thirteen
          R hL S (by simpa [P] using hmSize13)
    have hThreshold : 3 * 2155 + 1 <= P.m := by
      have hm' : 6466 <= P.m := by simpa [P] using hm
      norm_num
      exact hm'
    exact
      M.singleCorner_impossible_of_explicit_width
        R hL S
        (by simpa [P] using hmLarge)
        (by simpa [P] using hWidth)
        (by simpa [P] using hThreshold)

  have hellFourteen : 14 <= ell := by
    omega

  by_cases h19 : ell <= 19
  · have hWidth : P.m - S.b <= 2245 := by
      simpa [P] using
        M.singleCorner_m_sub_b_le_2245_of_ell_fourteen_nineteen
          R hL S
          (by simpa [P] using hmSize)
          hellFourteen h19
    have hPow13 : 2 ^ 13 <= 2 ^ (ell - 1) :=
      Nat.pow_le_pow_right
        (by omega : 0 < (2 : ℕ))
        (by omega)
    have hm8191 : 8191 <= P.m := by
      have h := le_trans hPow13 hmLogLower
      norm_num at h
      omega
    have hThreshold : 3 * 2245 + 1 <= P.m := by
      norm_num
      omega
    exact
      M.singleCorner_impossible_of_explicit_width
        R hL S
        (by simpa [P] using hmLarge)
        (by simpa [P] using hWidth)
        (by simpa [P] using hThreshold)

  have hellTwenty : 20 <= ell := by
    omega

  by_cases h43 : ell <= 43
  · have hWidth : P.m - S.b <= 33195 := by
      simpa [P] using
        M.singleCorner_m_sub_b_le_33195_of_ell_twenty_fortythree
          R hL S
          (by simpa [P] using hmSize)
          hellTwenty h43
    have hPow19 : 2 ^ 19 <= 2 ^ (ell - 1) :=
      Nat.pow_le_pow_right
        (by omega : 0 < (2 : ℕ))
        (by omega)
    have hm524287 : 524287 <= P.m := by
      have h := le_trans hPow19 hmLogLower
      norm_num at h
      omega
    have hThreshold : 3 * 33195 + 1 <= P.m := by
      norm_num
      omega
    exact
      M.singleCorner_impossible_of_explicit_width
        R hL S
        (by simpa [P] using hmLarge)
        (by simpa [P] using hWidth)
        (by simpa [P] using hThreshold)

  have hellFortyFour : 44 <= ell := by
    omega

  by_cases h5287 : ell <= 5287
  · have hWidth : P.m - S.b <= 460397 := by
      simpa [P] using
        M.singleCorner_m_sub_b_le_460397_of_ell_fortyfour_5287
          R hL S
          (by simpa [P] using hmSize)
          hellFortyFour h5287
    have hPow43 : 2 ^ 43 <= 2 ^ (ell - 1) :=
      Nat.pow_le_pow_right
        (by omega : 0 < (2 : ℕ))
        (by omega)
    have hmHuge : 8796093022207 <= P.m := by
      have h := le_trans hPow43 hmLogLower
      norm_num at h
      omega
    have hThreshold : 3 * 460397 + 1 <= P.m := by
      norm_num
      omega
    exact
      M.singleCorner_impossible_of_explicit_width
        R hL S
        (by simpa [P] using hmLarge)
        (by simpa [P] using hWidth)
        (by simpa [P] using hThreshold)

  have hell5288 : 5288 <= ell := by
    omega
  have hEventual :=
    actual_singleCornerDyadicLog196Width_eventual_threshold
      R hell5288
  have hThreshold :
      3 * singleCornerDyadicLog196Width
            (actualCriticalSturmianOneShortSquareWindow196 R) ell + 1 <=
        P.m := by
    have hToM1 :
        3 * singleCornerDyadicLog196Width
              (actualCriticalSturmianOneShortSquareWindow196 R) ell + 2 <=
          P.m + 1 :=
      le_trans hEventual hmLogLower
    omega
  exact
    M.singleCorner_card_one_impossible_of_actualBHZ196_strongThreshold
      R hL hCard
      (by simpa [P] using hmSize)
      (by simpa [P] using hmLarge)
      (by simpa [P] using hThreshold)

end MinimalActualABObstructionPacket

end ExternalArithmetic
end CSTMicro
end Collatz2
