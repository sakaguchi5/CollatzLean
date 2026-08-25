import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedHenselFactorRepeat
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselZeroRepeatArithmetic

/-!
# Attached free-base Hensel chain の qOne 線形上界

restarted branch では入口 depth `delta 0 = 1` を使って

  3 * Q_i <= (4*(W-i)+3) * 2^(delta_i-1)

を得ていた。

attached branch の canonical free-base chainでも、straight corridor 上の
actual depth は Beatty displacement に exact に従うため、同じ local qOne 上界が成立する。
入口 depth を固定する必要が出るのは、その後 `delta_j` を entrance scale へ戻す段階だけである。

このファイルではさらに

  2^(delta_j-1) * 2^j <= 2^(delta_0) * 3^j

を証明し、restarted の `delta_0=1` が attached では
`2^(delta_0)` という明示的な budget に置き換わることを固定する。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
attached straight suffix の depth growth は、一段の Beatty carry を除けば
entrance depth と Beatty displacement だけで抑えられる。

  r + delta_(i+r) <= delta_i + beta(r) + 1.
-/
theorem straightHenselDelta_add_offset_le
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i r : ℕ}
    (hi : i < A.straightHenselWidth)
    (hir : i + r < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    r + C.delta (i + r) <=
      C.delta i + beattyIndex r + 1 := by
  dsimp
  have hRel :=
    A.straightHenselDelta_relative_exact hStart hi hir
  dsimp at hRel
  rcases
      beattyIndex_add_eq_add_or_add_one
        (A.straightHenselStart + i) r with hNo | hCarry
  · have hBeatty :
        beattyIndex (A.straightHenselStart + i + r) =
          beattyIndex (A.straightHenselStart + i) + beattyIndex r := by
      simpa [Nat.add_assoc] using hNo
    rw [hBeatty] at hRel
    omega
  · have hBeatty :
        beattyIndex (A.straightHenselStart + i + r) =
          beattyIndex (A.straightHenselStart + i) + beattyIndex r + 1 := by
      simpa [Nat.add_assoc] using hCarry
    rw [hBeatty] at hRel
    omega

/--
qOne finite expansion の一つの weighted forcing term を entrance depth で抑える。
-/
theorem straightHenselWeightedPow_le
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i r : ℕ}
    (hi : i < A.straightHenselWidth)
    (hir : i + r < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    (2 : ℤ) ^ r * (2 : ℤ) ^ C.delta (i + r) <=
      4 * (2 : ℤ) ^ (C.delta i - 1) * (3 : ℤ) ^ r := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  have hDeltaPos : 0 < C.delta i := C.delta_pos i hi
  have hExp := A.straightHenselDelta_add_offset_le hStart hi hir
  change
    r + C.delta (i + r) <= C.delta i + beattyIndex r + 1
    at hExp
  have hPowMonoNat :
      2 ^ (r + C.delta (i + r)) <=
        2 ^ (C.delta i + beattyIndex r + 1) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hExp
  have hBeta := beattyIndex_lower r
  have hRightNat :
      2 ^ (C.delta i + beattyIndex r + 1) <=
        4 * 2 ^ (C.delta i - 1) * 3 ^ r := by
    have hPowId :
        2 ^ (C.delta i + beattyIndex r + 1) =
          4 * 2 ^ (C.delta i - 1) * 2 ^ beattyIndex r := by
      have hDeltaId : C.delta i = (C.delta i - 1) + 1 := by omega
      calc
        2 ^ (C.delta i + beattyIndex r + 1)
            = 2 ^ (((C.delta i - 1) + 1) + beattyIndex r + 1) := by
                rw [hDeltaId]
                simp
        _ = 2 ^ ((C.delta i - 1) + (beattyIndex r + 2)) := by
              congr 1
              omega
        _ = 2 ^ (C.delta i - 1) * 2 ^ (beattyIndex r + 2) := by
              rw [pow_add]
        _ = 2 ^ (C.delta i - 1) * (2 ^ beattyIndex r * 2 ^ 2) := by
              rw [pow_add]
        _ = 4 * 2 ^ (C.delta i - 1) * 2 ^ beattyIndex r := by
              norm_num
              ring
    rw [hPowId]
    exact Nat.mul_le_mul_left (4 * 2 ^ (C.delta i - 1)) hBeta
  have hPowNat :
      2 ^ r * 2 ^ C.delta (i + r) <=
        4 * 2 ^ (C.delta i - 1) * 3 ^ r := by
    rw [← pow_add]
    exact le_trans hPowMonoNat hRightNat
  exact_mod_cast hPowNat

/--
`qOneBlockNumerator` の長さ `r+1` 展開は

  4*(r+1)*2^(delta_i-1)*3^r

以下であり、同時に nonnegative。
-/
theorem qOneBlockNumerator_succ_nonneg_and_le
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i r : ℕ}
    (hEnd : i + (r + 1) <= A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    0 <= C.qOneBlockNumerator i (r + 1) ∧
    C.qOneBlockNumerator i (r + 1) <=
      4 * (r + 1 : ℤ) *
        (2 : ℤ) ^ (C.delta i - 1) * (3 : ℤ) ^ r := by
  let C := A.toFreeBaseMonotoneHenselChain hStart
  change
    0 <= C.qOneBlockNumerator i (r + 1) ∧
    C.qOneBlockNumerator i (r + 1) <=
      4 * (r + 1 : ℤ) *
        (2 : ℤ) ^ (C.delta i - 1) * (3 : ℤ) ^ r
  revert hEnd
  induction r with
  | zero =>
      intro hEnd
      have hi : i < A.straightHenselWidth := by omega
      have hTerm :=
        A.straightHenselWeightedPow_le
          hStart (i := i) (r := 0) hi (by simpa using hi)
      change
        (2 : ℤ) ^ 0 * (2 : ℤ) ^ C.delta (i + 0) <=
          4 * (2 : ℤ) ^ (C.delta i - 1) * (3 : ℤ) ^ 0
        at hTerm
      have hRec :
          C.qOneBlockNumerator i 1 =
            3 * C.qOneBlockNumerator i 0 +
              (2 : ℤ) ^ 0 * (2 : ℤ) ^ C.delta i := rfl
      rw [hRec]
      simp only [FreeBaseMonotoneHenselChain.qOneBlockNumerator_zero,
        mul_zero, zero_add, pow_zero, one_mul]
      constructor
      · positivity
      · simpa using hTerm
  | succ r ih =>
      intro hEnd
      have hPrevEnd : i + (r + 1) <= A.straightHenselWidth := by omega
      have hIH := ih hPrevEnd
      have hi : i < A.straightHenselWidth := by omega
      have hir : i + (r + 1) < A.straightHenselWidth := by omega
      have hTerm :=
        A.straightHenselWeightedPow_le
          hStart (i := i) (r := r + 1) hi hir
      change
        (2 : ℤ) ^ (r + 1) * (2 : ℤ) ^ C.delta (i + (r + 1)) <=
          4 * (2 : ℤ) ^ (C.delta i - 1) * (3 : ℤ) ^ (r + 1)
        at hTerm
      have hRec :
          C.qOneBlockNumerator i ((r + 1) + 1) =
            3 * C.qOneBlockNumerator i (r + 1) +
              (2 : ℤ) ^ (r + 1) *
                (2 : ℤ) ^ C.delta (i + (r + 1)) := rfl
      rw [hRec]
      constructor
      · exact add_nonneg
          (mul_nonneg (by norm_num) hIH.1)
          (by positivity)
      · calc
          3 * C.qOneBlockNumerator i (r + 1) +
              (2 : ℤ) ^ (r + 1) *
                (2 : ℤ) ^ C.delta (i + (r + 1)) <=
            3 *
                (4 * (r + 1 : ℤ) *
                  (2 : ℤ) ^ (C.delta i - 1) * (3 : ℤ) ^ r) +
              4 * (2 : ℤ) ^ (C.delta i - 1) *
                (3 : ℤ) ^ (r + 1) := by
                  exact add_le_add
                    (mul_le_mul_of_nonneg_left hIH.2 (by norm_num))
                    hTerm
          _ =
            4 * (r + 2 : ℤ) *
              (2 : ℤ) ^ (C.delta i - 1) * (3 : ℤ) ^ (r + 1) := by
                rw [pow_succ]
                ring

/-- free-base chain の terminal shifted quotient は exact に `1`。 -/
@[simp] theorem straight_qOne_terminal
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    C.qOne C.width = 1 := by
  dsimp
  unfold FreeBaseMonotoneHenselChain.qOne
  rw [(A.toFreeBaseMonotoneHenselChain hStart).q_terminal]
  norm_num

/--
attached canonical free-base chain の shifted quotient `Q_i=q_i+1` に対する
restarted と同型の normalized linear upper bound。
-/
theorem straight_qOne_linear_upper
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    3 * C.qOne i <=
      (4 * (A.straightHenselWidth - i : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta i - 1) := by
  let C := A.toFreeBaseMonotoneHenselChain hStart
  change
    3 * C.qOne i <=
      (4 * (A.straightHenselWidth - i : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta i - 1)
  let n := A.straightHenselWidth - i
  have hnPos : 0 < n := by
    dsimp [n]
    omega
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnPos)
  have hr' : A.straightHenselWidth - i = r + 1 := by
    simpa [n, Nat.succ_eq_add_one] using hr
  have hEndEq : i + (r + 1) = A.straightHenselWidth := by omega
  have hUnit :=
    A.qOneBlockNumerator_succ_nonneg_and_le
      hStart (i := i) (r := r) (by omega)
  change
    0 <= C.qOneBlockNumerator i (r + 1) ∧
      C.qOneBlockNumerator i (r + 1) <=
        4 * (r + 1 : ℤ) * (2 : ℤ) ^ (C.delta i - 1) * (3 : ℤ) ^ r
    at hUnit
  have hEndC : i + (r + 1) ≤ C.width := by
    rw [hEndEq]
    dsimp [C, toFreeBaseMonotoneHenselChain]
    simp
  have hIter :=
    C.qOne_iterate
      (i := i)
      (n := r + 1)
      hEndC
  have hQTerminal : C.qOne (i + (r + 1)) = 1 := by
    rw [hEndEq]
    exact A.straight_qOne_terminal hStart
  rw [hQTerminal, mul_one] at hIter
  let E : ℤ := (2 : ℤ) ^ (C.delta i - 1)
  have hEOne : 1 <= E := by
    dsimp [E]
    have hp : 0 < (2 : ℤ) ^ (C.delta i - 1) := by positivity
    omega
  have hTwoThreeNat :
      2 ^ (r + 1) <= 3 ^ (r + 1) :=
    Nat.pow_le_pow_left (by norm_num : 2 <= (3 : ℕ)) (r + 1)
  have hTwoThree :
      (2 : ℤ) ^ (r + 1) <= (3 : ℤ) ^ (r + 1) := by
    exact_mod_cast hTwoThreeNat
  have hTermBound :
      (2 : ℤ) ^ (r + 1) <= (3 : ℤ) ^ (r + 1) * E := by
    have hThreeNonneg : 0 <= (3 : ℤ) ^ (r + 1) := by positivity
    exact le_trans hTwoThree
      (by
        have := mul_le_mul_of_nonneg_left hEOne hThreeNonneg
        simpa using this)
  have hBound :
      (3 : ℤ) ^ r * (3 * C.qOne i) <=
        (3 : ℤ) ^ r *
          ((4 * (r + 1 : ℤ) + 3) * E) := by
    calc
      (3 : ℤ) ^ r * (3 * C.qOne i)
          = (3 : ℤ) ^ (r + 1) * C.qOne i := by
              rw [pow_succ]
              ring
      _ = (2 : ℤ) ^ (r + 1) + C.qOneBlockNumerator i (r + 1) := hIter
      _ <=
        (3 : ℤ) ^ (r + 1) * E +
          4 * (r + 1 : ℤ) * E * (3 : ℤ) ^ r :=
            add_le_add hTermBound hUnit.2
      _ =
        (3 : ℤ) ^ r * ((4 * (r + 1 : ℤ) + 3) * E) := by
          rw [pow_succ]
          ring
  have hPowPos : 0 < (3 : ℤ) ^ r := by positivity
  have hLocal :
      3 * C.qOne i <= (4 * (r + 1 : ℤ) + 3) * E := by
    nlinarith [hBound]
  have hrInt :
      (A.straightHenselWidth : ℤ) - (i : ℤ) = (r + 1 : ℤ) := by
    have hiLe : i ≤ A.straightHenselWidth := Nat.le_of_lt hi
    rw [← Nat.cast_sub hiLe]
    exact_mod_cast hr'
  dsimp [E] at hLocal ⊢
  rw [hrInt]
  exact hLocal

/-- 位置依存係数を共通係数 `4*W+3` まで粗くした qOne 上界。 -/
theorem straight_qOne_width_upper
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    3 * C.qOne i <=
      (4 * (A.straightHenselWidth : ℤ) + 3) *
        (2 : ℤ) ^ (C.delta i - 1) := by
  have hLocal := A.straight_qOne_linear_upper hStart hi
  dsimp only at hLocal ⊢
  have hCoeff :
      4 * (A.straightHenselWidth - i : ℤ) + 3 <=
        4 * (A.straightHenselWidth : ℤ) + 3 := by
    omega
  have hPowNonneg :
      0 <= (2 : ℤ) ^
        ((A.toFreeBaseMonotoneHenselChain hStart).delta i - 1) := by
    positivity
  exact le_trans hLocal
    (mul_le_mul_of_nonneg_right hCoeff hPowNonneg)

/-- attached actual quotient は nonnegative なので `Q_i=q_i+1` は正。 -/
theorem straight_qOne_pos_of_lt_width
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i : ℕ}
    (hi : i < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    0 < C.qOne i := by
  let k := A.straightHenselStart + i
  have hEnd := A.straightHenselStart_add_width
  have hsk : P.criticalizationStart ≤ k := by
    dsimp [k]
    have hCrit := A.criticalization_le_previous
    unfold straightHenselStart
    omega
  have hkc : k ≤ P.terminalCriticalStart := by
    dsimp [k]
    omega
  have hQ :=
    terminalCarryTailQuotient_nonneg P hStart hsk hkc
  have hQ' :
      0 ≤ terminalCarryTailQuotient
        P hStart (A.straightHenselStart + i) := by
    simpa [k] using hQ
  dsimp [
    FreeBaseMonotoneHenselChain.qOne,
    AttachedTwoCornerPacket.toFreeBaseMonotoneHenselChain
  ]
  exact add_pos_of_nonneg_of_pos hQ' (by norm_num)

/--
repeat start `j` の depth scale を free-base entrance depth `delta_0` へ戻す。
restarted の定数 `2` は attached では exact に `2^(delta_0)` へ置き換わる。
-/
theorem straight_delta_pow_mul_twoPow_le_baseDepth
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {j : ℕ}
    (hj : j < A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    2 ^ (C.delta j - 1) * 2 ^ j <=
      2 ^ C.delta 0 * 3 ^ j := by
  let C := A.toFreeBaseMonotoneHenselChain hStart
  change
    2 ^ (C.delta j - 1) * 2 ^ j <= 2 ^ C.delta 0 * 3 ^ j
  have h0 : 0 < A.straightHenselWidth :=
    A.straightHenselWidth_pos
  have hExp :=
    A.straightHenselDelta_add_offset_le
      hStart (i := 0) (r := j) h0 (by simpa using hj)
  have hExp' :
      j + C.delta j <=
        C.delta 0 + beattyIndex j + 1 := by
    simpa [C] using hExp
  have hjC : j < C.width := by
    simpa [C, toFreeBaseMonotoneHenselChain] using hj
  have hDjPos : 0 < C.delta j :=
    C.delta_pos j hjC
  have hExpPred :
      C.delta j - 1 + j <=
        C.delta 0 + beattyIndex j := by
    omega
  have hDjPos : 0 < C.delta j := C.delta_pos j hj
  have hExp' : C.delta j - 1 + j <= C.delta 0 + beattyIndex j := by
    omega
  have hPowMono :
      2 ^ (C.delta j - 1 + j) <=
        2 ^ (C.delta 0 + beattyIndex j) :=
    Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hExp'
  have hBeta := beattyIndex_lower j
  calc
    2 ^ (C.delta j - 1) * 2 ^ j =
        2 ^ (C.delta j - 1 + j) := by rw [pow_add]
    _ <= 2 ^ (C.delta 0 + beattyIndex j) := hPowMono
    _ = 2 ^ C.delta 0 * 2 ^ beattyIndex j := by rw [pow_add]
    _ <= 2 ^ C.delta 0 * 3 ^ j :=
      Nat.mul_le_mul_left (2 ^ C.delta 0) hBeta

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
