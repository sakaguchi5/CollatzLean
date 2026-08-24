import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedHenselZeroCycleBridge
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Attached Hensel: 唯一残す nonzero-repeat smallness obligation

ここまでで attached branch について

* actual object -> canonical free-base Hensel chain,
* Beatty factor repeat -> parallel exponent block,
* scaled difference transport `2^m M_m = 3^m M_0`,
* zero repeat -> pure Beatty cycle equation,

までは theorem として接続済みである。

このファイルでは、現在未解決の一点を隠さず Prop として明示する。

## 未解決点

forced repeated block の入口 scaled difference

  M_0 = Q_j - 2^Delta Q_i

が nonzero であるとき、attached の Farey/minimality/terminal constraints から

  -2^m < M_0 < 2^m

を導くこと。

一方 repeated-block arithmetic からは `2^m | M_0` が既に証明済みなので、
この strict smallness が得られれば `M_0 = 0` となり nonzero branch は消える。

このファイルはその smallness 自体を axiom として追加しない。
`AttachedNonzeroRepeatSmallnessObligation` を theorem の仮定として露出し、
それ以外の reduction を証明する。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/--
attached の未解決 arithmetic obligation。

必要なのは Beatty complexity から強制される repeat だけなので、任意 repeat に対する
過剰に強い仮定にはせず、`i<j`, `j<=m+1`, `2*m+2<=width` を持つ forced window に限定する。
-/
def AttachedNonzeroRepeatSmallnessObligation
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart) : Prop :=
  let C := A.toFreeBaseMonotoneHenselChain hStart
  ∀ (m i j Delta : ℕ),
    2 * m + 2 ≤ C.width →
    i < j →
    j ≤ m + 1 →
    j + m < C.width →
    C.SameDeltaOffsetBlock i j m Delta →
    C.scaledDifference i j Delta 0 ≠ 0 →
      -((2 : ℤ) ^ m) < C.scaledDifference i j Delta 0 ∧
        C.scaledDifference i j Delta 0 < (2 : ℤ) ^ m

/--
`2^m` の倍数が open interval `(-2^m,2^m)` に入るなら zero しかない。
-/
private theorem eq_zero_of_twoPow_dvd_of_strict_between
    {m : ℕ}
    {z : ℤ}
    (hDvd : (2 : ℤ) ^ m ∣ z)
    (hLower : -((2 : ℤ) ^ m) < z)
    (hUpper : z < (2 : ℤ) ^ m) :
    z = 0 := by
  rcases hDvd with ⟨k, hk⟩
  have hPowPos : 0 < (2 : ℤ) ^ m := by positivity
  by_contra hz
  have hkNe : k ≠ 0 := by
    intro hk0
    rw [hk0, mul_zero] at hk
    exact hz hk
  rcases lt_or_gt_of_ne hkNe with hkNeg | hkPos
  · have hkLe : k ≤ -1 := by omega
    have hMulLe :
        (2 : ℤ) ^ m * k ≤ -((2 : ℤ) ^ m) := by
      calc
        (2 : ℤ) ^ m * k
            ≤ (2 : ℤ) ^ m * (-1) :=
          mul_le_mul_of_nonneg_left hkLe (le_of_lt hPowPos)
        _ = -((2 : ℤ) ^ m) := by ring
    have hzLe : z ≤ -((2 : ℤ) ^ m) := by
      rw [hk]
      exact hMulLe
    linarith
  · have hkGe : 1 ≤ k := by omega
    have hMulGe :
        (2 : ℤ) ^ m ≤ (2 : ℤ) ^ m * k := by
      calc
        (2 : ℤ) ^ m = (2 : ℤ) ^ m * 1 := by ring
        _ ≤ (2 : ℤ) ^ m * k :=
          mul_le_mul_of_nonneg_left hkGe (le_of_lt hPowPos)
    have hzGe : (2 : ℤ) ^ m ≤ z := by
      rw [hk]
      exact hMulGe
    linarith

/--
未解決 smallness が得られれば、forced repeat の nonzero branch は自動的に消える。
-/
theorem exists_forced_zero_scaledDifference_of_smallness
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hSmall : A.AttachedNonzeroRepeatSmallnessObligation hStart)
    (m : ℕ)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i j Delta : ℕ,
      i < j ∧
      j ≤ m + 1 ∧
      j + m < C.width ∧
      C.SameDeltaOffsetBlock i j m Delta ∧
      C.scaledDifference i j Delta 0 = 0 := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  rcases
      A.exists_sameDeltaOffsetBlock_of_two_mul_add_two_le_width
        hStart m hWidth with
    ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock⟩
  have hWidthC : 2 * m + 2 ≤ C.width := by
    change 2 * m + 2 ≤ A.straightHenselWidth
    exact hWidth
  have hiEnd : i + m ≤ C.width := by omega
  have hjEndLe : j + m ≤ C.width := by omega
  have hDvd :=
    C.twoPow_dvd_scaledDifference_zero hiEnd hjEndLe hBlock
  have hZero : C.scaledDifference i j Delta 0 = 0 := by
    by_contra hNe
    have hBounds :=
      hSmall m i j Delta hWidthC hij hjBound hjEnd hBlock hNe
    exact hNe
      (eq_zero_of_twoPow_dvd_of_strict_between
        hDvd hBounds.1 hBounds.2)
  exact ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock, hZero⟩

/--
smallness を仮定した forced zero repeat を、そのまま outer scaled state へ持ち上げる。
-/
theorem exists_forced_zero_scaledState_of_smallness
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hSmall : A.AttachedNonzeroRepeatSmallnessObligation hStart)
    (m : ℕ)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i j Delta : ℕ,
      i < j ∧
      j ≤ m + 1 ∧
      j + m < C.width ∧
      C.SameDeltaOffsetBlock i j m Delta ∧
      C.ScaledState i j Delta := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  rcases
      A.exists_forced_zero_scaledDifference_of_smallness
        hStart hSmall m hWidth with
    ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock, hZero⟩
  have hDelta0 := hBlock 0 (by omega)
  have hQ :=
    (C.scaledDifference_zero_eq_zero_iff
      (i := i) (j := j) (Delta := Delta)).1 hZero
  exact
    ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock,
      ⟨by simpa using hDelta0, hQ⟩⟩

/--
未解決 smallness を仮定すると、forced repeat は pure Beatty zero-cycle equation まで到達する。
この theorem の仮定のうち未証明なのは `AttachedNonzeroRepeatSmallnessObligation` だけである。
-/
theorem exists_forced_zero_cycleEquation_of_smallness
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hSmall : A.AttachedNonzeroRepeatSmallnessObligation hStart)
    (m : ℕ)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i p Delta : ℕ,
      0 < p ∧
      i + p < C.width ∧
      ((3 : ℤ) ^ p - (2 : ℤ) ^ (p + Delta)) * C.qOne i =
        (2 : ℤ) ^ C.delta i *
          beattyCyclePhi (A.straightHenselStart + i) p := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  rcases
      A.exists_forced_zero_scaledState_of_smallness
        hStart hSmall m hWidth with
    ⟨i, j, Delta, hij, hjBound, hjEnd, hBlock, hState⟩
  let p := j - i
  have hp : 0 < p := by
    dsimp [p]
    omega
  have hIp : i + p = j := by
    dsimp [p]
    omega
  have hjWidth : j < C.width := by
    dsimp [C, toFreeBaseMonotoneHenselChain]
    dsimp [toFreeBaseMonotoneHenselChain] at hjEnd
    omega
  have hEndC : i + p ≤ A.straightHenselWidth := by
    change i + p ≤ C.width
    rw [hIp]
    exact Nat.le_of_lt hjWidth
  have hStateP : C.ScaledState i (i + p) Delta := by
    rw [hIp]
    exact hState
  have hEq :=
    A.zeroScaledState_cycleEquation
      hStart hEndC hStateP
  dsimp [C] at hEq
  refine ⟨i, p, Delta, hp, ?_, ?_⟩
  · rw [hIp]
    exact hjWidth
  · exact hEq

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
