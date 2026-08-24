import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedTerminalNearRepeat
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedHenselZeroCycleBridge


/-!
# Attached Hensel: right-end smallness target

repeated-block transport は

  2^m M_m = 3^m M_0

である。従って entrance smallness

  |M_0| < 2^m

を直接示す代わりに、right-end smallness

  |M_m| < 3^m

を示せば十分である。

このファイルでは

* right-end smallness -> entrance smallness,
* `3^m | M_m` と strict smallness -> `M_m=0`,
* terminal-near forced repeat に対する新しい end-smallness obligation,
* その obligation から zero scaled state / Beatty cycle equation までの reduction,

を theorem として固定する。

未解決なのは `AttachedTerminalNearEndSmallnessObligation` 自体の証明だけであり、
ここでは axiom にしない。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace FreeBaseMonotoneHenselChain

/--
right-end open bound `(-3^m,3^m)` は transport を通して entrance open bound
`(-2^m,2^m)` を与える。
-/
theorem scaledDifference_zero_small_of_end_small
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta)
    (hLower :
      -((3 : ℤ) ^ m) < C.scaledDifference i j Delta m)
    (hUpper :
      C.scaledDifference i j Delta m < (3 : ℤ) ^ m) :
    -((2 : ℤ) ^ m) < C.scaledDifference i j Delta 0 ∧
      C.scaledDifference i j Delta 0 < (2 : ℤ) ^ m := by
  have hTransport := C.scaledDifference_transport hiEnd hjEnd hBlock
  have hTwoPos : 0 < (2 : ℤ) ^ m := by positivity
  have hThreePos : 0 < (3 : ℤ) ^ m := by positivity
  have hLowerScaled :
      (2 : ℤ) ^ m * (-((3 : ℤ) ^ m)) <
        (2 : ℤ) ^ m * C.scaledDifference i j Delta m :=
    (Int.mul_lt_mul_left hTwoPos).2 hLower
  have hLowerTransport :
      (3 : ℤ) ^ m * (-((2 : ℤ) ^ m)) <
        (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 := by
    calc
      (3 : ℤ) ^ m * (-((2 : ℤ) ^ m))
          = (2 : ℤ) ^ m * (-((3 : ℤ) ^ m)) := by ring
      _ < (2 : ℤ) ^ m * C.scaledDifference i j Delta m :=
        hLowerScaled
      _ = (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 :=
        hTransport
  have hLower0 :
      -((2 : ℤ) ^ m) < C.scaledDifference i j Delta 0 :=
    (Int.mul_lt_mul_left hThreePos).1 hLowerTransport
  have hUpperScaled :
      (2 : ℤ) ^ m * C.scaledDifference i j Delta m <
        (2 : ℤ) ^ m * (3 : ℤ) ^ m :=
    (Int.mul_lt_mul_left hTwoPos).2 hUpper
  have hUpperTransport :
      (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 <
        (3 : ℤ) ^ m * (2 : ℤ) ^ m := by
    calc
      (3 : ℤ) ^ m * C.scaledDifference i j Delta 0
          = (2 : ℤ) ^ m * C.scaledDifference i j Delta m :=
        hTransport.symm
      _ < (2 : ℤ) ^ m * (3 : ℤ) ^ m := hUpperScaled
      _ = (3 : ℤ) ^ m * (2 : ℤ) ^ m := by ring
  have hUpper0 :
      C.scaledDifference i j Delta 0 < (2 : ℤ) ^ m :=
    (Int.mul_lt_mul_left hThreePos).1 hUpperTransport
  exact ⟨hLower0, hUpper0⟩

/-- `3^m` の倍数が open interval `(-3^m,3^m)` に入るなら zero。 -/
theorem eq_zero_of_threePow_dvd_of_strict_between
    {m : ℕ}
    {z : ℤ}
    (hDvd : (3 : ℤ) ^ m ∣ z)
    (hLower : -((3 : ℤ) ^ m) < z)
    (hUpper : z < (3 : ℤ) ^ m) :
    z = 0 := by
  rcases hDvd with ⟨k, hk⟩
  have hPowPos : 0 < (3 : ℤ) ^ m := by positivity
  by_contra hz
  have hkNe : k ≠ 0 := by
    intro hk0
    rw [hk0, mul_zero] at hk
    exact hz hk
  rcases lt_or_gt_of_ne hkNe with hkNeg | hkPos
  · have hkLe : k ≤ -1 := by omega
    have hMulLe :
        (3 : ℤ) ^ m * k ≤ -((3 : ℤ) ^ m) := by
      calc
        (3 : ℤ) ^ m * k
            ≤ (3 : ℤ) ^ m * (-1) :=
          mul_le_mul_of_nonneg_left hkLe (le_of_lt hPowPos)
        _ = -((3 : ℤ) ^ m) := by ring
    rw [← hk] at hMulLe
    linarith
  · have hkGe : 1 ≤ k := by omega
    have hMulGe :
        (3 : ℤ) ^ m ≤ (3 : ℤ) ^ m * k := by
      calc
        (3 : ℤ) ^ m = (3 : ℤ) ^ m * 1 := by ring
        _ ≤ (3 : ℤ) ^ m * k :=
          mul_le_mul_of_nonneg_left hkGe (le_of_lt hPowPos)
    rw [← hk] at hMulGe
    linarith

end FreeBaseMonotoneHenselChain

namespace AttachedTwoCornerPacket

/--
terminal-near repeat にだけ要求する新しい right-end smallness obligation。

旧 obligation のように forced left window の全 repeat を入口で評価せず、
terminal-near theorem が供給する band 内 repeat の `M_m` だけを評価する。
-/
def AttachedTerminalNearEndSmallnessObligation
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart) : Prop :=
  let C := A.toFreeBaseMonotoneHenselChain hStart
  ∀ (m i j Delta : ℕ),
    2 * m + 2 ≤ C.width →
    C.width - (2 * m + 2) ≤ i →
    i < j →
    j + m < C.width →
    C.SameDeltaOffsetBlock i j m Delta →
    C.scaledDifference i j Delta 0 ≠ 0 →
      -((3 : ℤ) ^ m) < C.scaledDifference i j Delta m ∧
        C.scaledDifference i j Delta m < (3 : ℤ) ^ m

/--
right-end smallness があれば terminal-near forced repeat は zero difference を持つ。
-/
theorem exists_terminalNear_zero_scaledDifference_of_endSmallness
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hSmall : A.AttachedTerminalNearEndSmallnessObligation hStart)
    (m : ℕ)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i j Delta : ℕ,
      C.width - (2 * m + 2) ≤ i ∧
      i < j ∧
      j + m < C.width ∧
      C.SameDeltaOffsetBlock i j m Delta ∧
      C.scaledDifference i j Delta 0 = 0 := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  rcases
      A.exists_terminalNear_sameDeltaOffsetBlock
        hStart m hWidth with
    ⟨i, j, Delta, hiNear, hij, hjBand, hjEnd, hBlock⟩
  have hWidthC : 2 * m + 2 ≤ C.width := by
    change 2 * m + 2 ≤ A.straightHenselWidth
    exact hWidth
  by_cases hZero : C.scaledDifference i j Delta 0 = 0
  · exact ⟨i, j, Delta, hiNear, hij, hjEnd, hBlock, hZero⟩
  · have hBounds :=
      hSmall m i j Delta hWidthC hiNear hij hjEnd hBlock hZero
    have hjEndC : j + m < C.width := by
      simpa [C, toFreeBaseMonotoneHenselChain] using hjEnd
    have hiEnd : i + m ≤ C.width := by
      omega
    have hjEndLe : j + m ≤ C.width :=
      Nat.le_of_lt hjEndC
    have hDvdEnd :=
      C.threePow_dvd_scaledDifference_end hiEnd hjEndLe hBlock
    have hEndZero : C.scaledDifference i j Delta m = 0 :=
      FreeBaseMonotoneHenselChain.eq_zero_of_threePow_dvd_of_strict_between
        hDvdEnd hBounds.1 hBounds.2
    have hTransport := C.scaledDifference_transport hiEnd hjEndLe hBlock
    rw [hEndZero, mul_zero] at hTransport
    have hThreeNe : (3 : ℤ) ^ m ≠ 0 := by positivity
    have hEntryZero : C.scaledDifference i j Delta 0 = 0 := by
      have hProd :
          (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 = 0 := by
        simpa using hTransport.symm
      exact (mul_eq_zero.mp hProd).resolve_left hThreeNe
    exact ⟨i, j, Delta, hiNear, hij, hjEnd, hBlock, hEntryZero⟩

/--
新しい right-end obligation から zero scaled state まで到達する。
-/
theorem exists_terminalNear_zero_scaledState_of_endSmallness
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hSmall : A.AttachedTerminalNearEndSmallnessObligation hStart)
    (m : ℕ)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i j Delta : ℕ,
      C.width - (2 * m + 2) ≤ i ∧
      i < j ∧
      j + m < C.width ∧
      C.SameDeltaOffsetBlock i j m Delta ∧
      C.ScaledState i j Delta := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  rcases
      A.exists_terminalNear_zero_scaledDifference_of_endSmallness
        hStart hSmall m hWidth with
    ⟨i, j, Delta, hiNear, hij, hjEnd, hBlock, hZero⟩
  have hDelta := hBlock 0 (by omega)
  have hQ :=
    (C.scaledDifference_zero_eq_zero_iff
      (i := i) (j := j) (Delta := Delta)).1 hZero
  exact
    ⟨i, j, Delta, hiNear, hij, hjEnd, hBlock,
      ⟨by simpa using hDelta, hQ⟩⟩

/--
新しい right-end obligation でも従来と同じ pure Beatty zero-cycle equation まで到達する。
-/
theorem exists_terminalNear_zero_cycleEquation_of_endSmallness
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    (hSmall : A.AttachedTerminalNearEndSmallnessObligation hStart)
    (m : ℕ)
    (hWidth : 2 * m + 2 ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ∃ i p Delta : ℕ,
      C.width - (2 * m + 2) ≤ i ∧
      0 < p ∧
      i + p < C.width ∧
      ((3 : ℤ) ^ p - (2 : ℤ) ^ (p + Delta)) * C.qOne i =
        (2 : ℤ) ^ C.delta i *
          beattyCyclePhi (A.straightHenselStart + i) p := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  rcases
      A.exists_terminalNear_zero_scaledState_of_endSmallness
        hStart hSmall m hWidth with
    ⟨i, j, Delta, hiNear, hij, hjEnd, hBlock, hState⟩
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
  have hEndA : i + p ≤ A.straightHenselWidth := by
    change i + p ≤ C.width
    rw [hIp]
    exact Nat.le_of_lt hjWidth
  have hStateP : C.ScaledState i (i + p) Delta := by
    rw [hIp]
    exact hState
  have hEq := A.zeroScaledState_cycleEquation hStart hEndA hStateP
  dsimp [C] at hEq
  refine ⟨i, p, Delta, hiNear, hp, ?_, ?_⟩
  · rw [hIp]
    exact hjWidth
  · exact hEq

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
