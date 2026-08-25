import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedFreeBaseQOneBound
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedShiftedRepeatStateDifference

/-!
# Attached nonzero repeat の width-vs-entrance-depth budget

free-base chain の repeated block では

  2^m | M_0

なので `M_0 != 0` なら `|M_0| >= 2^m`。
一方、attached actual qOne の線形上界と repeat start `j` の depth estimate

  3 * Q_j <= (4W+3) * 2^(delta_j-1),
  2^(delta_j-1) * 2^j <= 2^(delta_0) * 3^j

を組み合わせると、nonzero repeat が生き残るためには exact に

  2 * 4^m <= (4W+3) * 2^(delta_0) * 3^m

が必要になる。

これは restarted branch の

  4^m <= (4W+3) * 3^m

に対応する free-base 版であり、restart 固有の `delta_0=1` が
明示的な entrance-depth budget として残った形である。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
`delta_j = delta_i + Delta` のとき、`i` 側 qOne の共通幅上界を
`2^Delta` 倍して `j` 側 depth scale に揃える。
-/
theorem straight_scaled_qOne_width_upper_of_delta_eq
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i j Delta : ℕ}
    (hi : i < A.straightHenselWidth)
    (hj : j < A.straightHenselWidth)
    (hDelta :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.delta j = C.delta i + Delta) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    3 * ((2 : ℤ) ^ Delta * C.qOne i) <=
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta j - 1) := by
  let C := A.toFreeBaseMonotoneHenselChain hStart
  dsimp only at hDelta
  have hBiW := A.straight_qOne_width_upper hStart hi
  change
    3 * C.qOne i <=
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta i - 1)
    at hBiW
  have hDPosI : 0 < C.delta i := C.delta_pos i hi
  have hDPosJ : 0 < C.delta j := C.delta_pos j hj
  have hDeltaC :
      C.delta j = C.delta i + Delta := by
    simpa [C] using hDelta
  have hPowShift :
      (2 : ℤ) ^ Delta * (2 : ℤ) ^ (C.delta i - 1) =
        (2 : ℤ) ^ (C.delta j - 1) := by
    have hNat :
        Delta + (C.delta i - 1) = C.delta j - 1 := by
      omega
    rw [← pow_add, hNat]
  have hScaleNonneg : 0 <= (2 : ℤ) ^ Delta := by positivity
  have hScaled := mul_le_mul_of_nonneg_left hBiW hScaleNonneg
  change
    3 * ((2 : ℤ) ^ Delta * C.qOne i) <=
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta j - 1)
  calc
    3 * ((2 : ℤ) ^ Delta * C.qOne i)
        = (2 : ℤ) ^ Delta * (3 * C.qOne i) := by ring
    _ <=
      (2 : ℤ) ^ Delta *
        ((4 * (A.straightHenselWidth : ℤ) + 3) *
          (2 : ℤ) ^ (C.delta i - 1)) := hScaled
    _ =
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        ((2 : ℤ) ^ Delta * (2 : ℤ) ^ (C.delta i - 1)) := by ring
    _ =
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta j - 1) := by rw [hPowShift]

/--
length `m` の repeated block の entrance scaled difference が nonzero なら、
`2^m` divisibility と qOne 上界から

  3*2^m <= (4W+3)*2^(delta_j-1)

を得る。
-/
theorem three_mul_twoPow_le_width_deltaPow_of_nonzero_attached_repeat
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {m i j Delta : ℕ}
    (hmPos : 0 < m)
    (hiEnd : i + m <= A.straightHenselWidth)
    (hjEnd : j + m <= A.straightHenselWidth)
    (hBlock :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.SameDeltaOffsetBlock i j m Delta)
    (hNonzero :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.scaledDifference i j Delta 0 ≠ 0) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    3 * (2 : ℤ) ^ m <=
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta j - 1) := by
  let C := A.toFreeBaseMonotoneHenselChain hStart
  dsimp only at hBlock hNonzero
  have hiW : i < A.straightHenselWidth := by omega
  have hjW : j < A.straightHenselWidth := by omega
  have hDelta := hBlock 0 (by omega)
  simp only [Nat.add_zero] at hDelta
  have hDiv :
      (2 : ℤ) ^ m ∣ C.scaledDifference i j Delta 0 :=
    C.twoPow_dvd_scaledDifference_zero hiEnd hjEnd hBlock
  rcases hDiv with ⟨z, hz⟩
  have hzNe : z ≠ 0 := by
    intro hz0
    rw [hz0, mul_zero] at hz
    exact hNonzero hz
  have hQiPos := A.straight_qOne_pos_of_lt_width hStart hiW
  have hQjPos := A.straight_qOne_pos_of_lt_width hStart hjW
  change 0 < C.qOne i at hQiPos
  change 0 < C.qOne j at hQjPos
  have hBiScaled :=
    A.straight_scaled_qOne_width_upper_of_delta_eq
      hStart hiW hjW hDelta
  change
    3 * ((2 : ℤ) ^ Delta * C.qOne i) <=
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta j - 1)
    at hBiScaled
  have hBjW := A.straight_qOne_width_upper hStart hjW
  change
    3 * C.qOne j <=
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta j - 1)
    at hBjW
  change
    3 * (2 : ℤ) ^ m <=
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta j - 1)
  have hzCases : z < 0 ∨ 0 < z := lt_or_gt_of_ne hzNe
  rcases hzCases with hzNeg | hzPos
  · have hzLe : z <= -1 := by omega
    have hPowPos : 0 < (2 : ℤ) ^ m := by positivity
    have hMle :
        C.scaledDifference i j Delta 0 <= -(2 : ℤ) ^ m := by
      rw [hz]
      have hmul := mul_le_mul_of_nonneg_left hzLe (le_of_lt hPowPos)
      simpa using hmul
    unfold FreeBaseMonotoneHenselChain.scaledDifference at hMle
    simp only [Nat.add_zero] at hMle
    have hToScaled :
        3 * (2 : ℤ) ^ m <=
          3 * ((2 : ℤ) ^ Delta * C.qOne i) := by
      have hQjNonneg : 0 <= 3 * C.qOne j := by
        have : 0 <= C.qOne j := le_of_lt hQjPos
        positivity
      linarith
    exact le_trans hToScaled hBiScaled
  · have hzGe : 1 <= z := by omega
    have hPowPos : 0 < (2 : ℤ) ^ m := by positivity
    have hMge :
        (2 : ℤ) ^ m <= C.scaledDifference i j Delta 0 := by
      rw [hz]
      have hmul := mul_le_mul_of_nonneg_left hzGe (le_of_lt hPowPos)
      simpa using hmul
    unfold FreeBaseMonotoneHenselChain.scaledDifference at hMge
    simp only [Nat.add_zero] at hMge
    have hToJ :
        3 * (2 : ℤ) ^ m <= 3 * C.qOne j := by
      have hQiScaledNonneg :
          0 <= 3 * ((2 : ℤ) ^ Delta * C.qOne i) := by
        positivity
      linarith
    exact le_trans hToJ hBjW

/--
純粋な冪比較 bridge。

  3*2^m <= B*2^e,
  2^e*2^j <= D*3^j,
  j <= m+1

なら

  2*4^m <= B*D*3^m.

`D=2` を入れると restarted branch の `4^m <= B*3^m` に戻る。
-/
private theorem two_mul_fourPow_le_mul_depthBudget_mul_threePow_bridge
    {m j e : ℕ}
    {B D : ℤ}
    (hjBound : j <= m + 1)
    (hBNonneg : 0 <= B)
    (hDNonneg : 0 <= D)
    (hPowerLower :
      3 * (2 : ℤ) ^ m <= B * (2 : ℤ) ^ e)
    (hDeltaPow :
      (2 : ℤ) ^ e * (2 : ℤ) ^ j <= D * (3 : ℤ) ^ j) :
    2 * (4 : ℤ) ^ m <= B * D * (3 : ℤ) ^ m := by
  have hTwoJNonneg : 0 <= (2 : ℤ) ^ j := by positivity
  have hMulJ := mul_le_mul_of_nonneg_right hPowerLower hTwoJNonneg
  have hBDNonneg : 0 <= B * D := mul_nonneg hBNonneg hDNonneg
  have hUseDelta := mul_le_mul_of_nonneg_left hDeltaPow hBNonneg
  have hMid :
      3 * (2 : ℤ) ^ (m + j) <= B * D * (3 : ℤ) ^ j := by
    calc
      3 * (2 : ℤ) ^ (m + j)
          = (3 * (2 : ℤ) ^ m) * (2 : ℤ) ^ j := by
              rw [pow_add]
              ring
      _ <= (B * (2 : ℤ) ^ e) * (2 : ℤ) ^ j := hMulJ
      _ <= B * (D * (3 : ℤ) ^ j) := by
            simpa [mul_assoc] using hUseDelta
      _ = B * D * (3 : ℤ) ^ j := by ring
  let d := m + 1 - j
  have hdEq : j + d = m + 1 := by
    dsimp [d]
    omega
  have hTwoDNonneg : 0 <= (2 : ℤ) ^ d := by positivity
  have hMidScaled := mul_le_mul_of_nonneg_right hMid hTwoDNonneg
  have hTwoLeThree : (2 : ℤ) ^ d <= (3 : ℤ) ^ d := by
    exact_mod_cast
      Nat.pow_le_pow_left (by norm_num : 2 <= (3 : ℕ)) d
  have hScaleNonneg : 0 <= B * D * (3 : ℤ) ^ j := by positivity
  have hRightScale :
      B * D * (3 : ℤ) ^ j * (2 : ℤ) ^ d <=
        B * D * (3 : ℤ) ^ j * (3 : ℤ) ^ d :=
    mul_le_mul_of_nonneg_left hTwoLeThree hScaleNonneg
  have hTwoProd :
      (2 : ℤ) ^ (m + j) * (2 : ℤ) ^ d =
        (2 : ℤ) ^ (2 * m + 1) := by
    rw [← pow_add]
    have hExp : m + j + d = 2 * m + 1 := by omega
    rw [hExp]
  have hPowFour :
      (2 : ℤ) ^ (2 * m + 1) = 2 * (4 : ℤ) ^ m := by
    calc
      (2 : ℤ) ^ (2 * m + 1) = (2 : ℤ) ^ (2 * m) * 2 := by
        rw [pow_succ]
      _ = ((2 : ℤ) ^ 2) ^ m * 2 := by rw [pow_mul]
      _ = (4 : ℤ) ^ m * 2 := by norm_num
      _ = 2 * (4 : ℤ) ^ m := by ring
  have hThreeProd :
      (3 : ℤ) ^ j * (3 : ℤ) ^ d = (3 : ℤ) ^ (m + 1) := by
    rw [← pow_add, hdEq]
  have hFinal :
      6 * (4 : ℤ) ^ m <= 3 * B * D * (3 : ℤ) ^ m := by
    calc
      6 * (4 : ℤ) ^ m
          = 3 * ((2 : ℤ) ^ (m + j) * (2 : ℤ) ^ d) := by
              rw [hTwoProd, hPowFour]
              ring
      _ = 3 * (2 : ℤ) ^ (m + j) * (2 : ℤ) ^ d := by ring
      _ <= B * D * (3 : ℤ) ^ j * (2 : ℤ) ^ d := by
            simpa [mul_assoc] using hMidScaled
      _ <= B * D * (3 : ℤ) ^ j * (3 : ℤ) ^ d := hRightScale
      _ = B * D * ((3 : ℤ) ^ j * (3 : ℤ) ^ d) := by ring
      _ = B * D * (3 : ℤ) ^ (m + 1) := by rw [hThreeProd]
      _ = 3 * B * D * (3 : ℤ) ^ m := by
            rw [pow_succ]
            ring
  nlinarith [hFinal]

/--
attached nonzero repeat が生き残るための exact width-vs-entrance-depth inequality。

`delta_0 = P.h straightHenselStart` と書けば

  2 * 4^m <= (4W+3) * 2^delta_0 * 3^m.

従って `m` が width に比例して大きく、entrance depth が十分小さい場合は
restarted と同じ指数成長比較で nonzero branch を排除できる。
-/
theorem two_mul_fourPow_le_width_mul_baseDepth_mul_threePow_of_nonzero_repeat
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {m i j Delta : ℕ}
    (hjBound : j <= m + 1)
    (hiEnd : i + m <= A.straightHenselWidth)
    (hjEnd : j + m <= A.straightHenselWidth)
    (hBlock :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.SameDeltaOffsetBlock i j m Delta)
    (hNonzero :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.scaledDifference i j Delta 0 ≠ 0) :
    2 * 4 ^ m <=
      (4 * A.straightHenselWidth + 3) *
        2 ^ P.h A.straightHenselStart * 3 ^ m := by
  let C := A.toFreeBaseMonotoneHenselChain hStart
  dsimp only at hBlock hNonzero
  by_cases hmZero : m = 0
  · subst m
    have hDepthPosC : 0 < C.delta 0 :=
      C.delta_pos 0 C.width_pos
    have hDepthPos :
        0 < P.h A.straightHenselStart := by
      simpa [C, toFreeBaseMonotoneHenselChain] using hDepthPosC
    norm_num
    have hExp :
        1 ≤ P.h A.straightHenselStart := by
      omega
    have hPow :
        2 ≤ 2 ^ P.h A.straightHenselStart := by
      have h :=
        Nat.pow_le_pow_right
          (by norm_num : 0 < (2 : ℕ))
          hExp
      simpa using h
    have hCoeff :
        1 ≤ 4 * A.straightHenselWidth + 3 := by
      omega
    nlinarith
  have hmPos : 0 < m := Nat.pos_of_ne_zero hmZero
  have hPowerLower :=
    A.three_mul_twoPow_le_width_deltaPow_of_nonzero_attached_repeat
      hStart hmPos hiEnd hjEnd hBlock hNonzero
  change
    3 * (2 : ℤ) ^ m <=
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta j - 1)
    at hPowerLower
  have hjW : j < A.straightHenselWidth := by omega
  have hDeltaPowNat :=
    A.straight_delta_pow_mul_twoPow_le_baseDepth hStart hjW
  change
    2 ^ (C.delta j - 1) * 2 ^ j <=
      2 ^ C.delta 0 * 3 ^ j
    at hDeltaPowNat
  have hDeltaPow :
      (2 : ℤ) ^ (C.delta j - 1) * (2 : ℤ) ^ j <=
        (2 : ℤ) ^ C.delta 0 * (3 : ℤ) ^ j := by
    exact_mod_cast hDeltaPowNat
  have hBNonneg : 0 <= 4 * (A.straightHenselWidth : ℤ) + 3 := by positivity
  have hDNonneg : 0 <= (2 : ℤ) ^ C.delta 0 := by positivity
  have hInt :
      2 * (4 : ℤ) ^ m <=
        (4 * (A.straightHenselWidth : ℤ) + 3) *
          (2 : ℤ) ^ C.delta 0 * (3 : ℤ) ^ m :=
    two_mul_fourPow_le_mul_depthBudget_mul_threePow_bridge
      (m := m) (j := j) (e := C.delta j - 1)
      (B := 4 * (A.straightHenselWidth : ℤ) + 3)
      (D := (2 : ℤ) ^ C.delta 0)
      hjBound hBNonneg hDNonneg hPowerLower hDeltaPow
  change
    2 * (4 : ℤ) ^ m <=
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ P.h (A.straightHenselStart + 0) * (3 : ℤ) ^ m
    at hInt
  simp only [Nat.add_zero] at hInt
  exact_mod_cast hInt

/--
最大 half-width に近い forced repeat を一つ選ぶと、
zero repeat であるか、上の entrance-depth budget を満たすかの二択になる。

attached では terminal `delta_width=0` を block に混ぜないため
`m=(W-2)/2` を採用する。
-/
theorem exists_halfWidth_repeat_zero_or_depthBudget
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hWidth : 2 <= A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    let m := (A.straightHenselWidth - 2) / 2
    ∃ i j Delta : ℕ,
      i < j ∧
      j <= m + 1 ∧
      j + m < C.width ∧
      C.SameDeltaOffsetBlock i j m Delta ∧
      (C.scaledDifference i j Delta 0 = 0 ∨
        2 * 4 ^ m <=
          (4 * A.straightHenselWidth + 3) *
            2 ^ P.h A.straightHenselStart * 3 ^ m) := by
  dsimp
  let m := (A.straightHenselWidth - 2) / 2
  have hFit : 2 * m + 2 <= A.straightHenselWidth := by
    dsimp [m]
    omega
  rcases
      A.exists_sameDeltaOffsetBlock_of_two_mul_add_two_le_width
        hStart m hFit with
    ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock⟩
  have hiEnd : i + m <= A.straightHenselWidth := by omega
  have hjEndLe : j + m <= A.straightHenselWidth := by omega
  refine ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock, ?_⟩
  by_cases hZero :
      (A.toFreeBaseMonotoneHenselChain hStart).scaledDifference
        i j Delta 0 = 0
  · exact Or.inl hZero
  · exact Or.inr
      (A.two_mul_fourPow_le_width_mul_baseDepth_mul_threePow_of_nonzero_repeat
        hStart hjBound hiEnd hjEndLe hBlock hZero)

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
