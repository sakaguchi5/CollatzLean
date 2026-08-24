import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BeattyCyclicCarryArithmetic
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselZeroRepeatArithmetic
import CollatzLean.Collatz2.CSTMicro.MultiCorner.AttachedHenselFactorRepeat

/-!
# Attached Hensel: zero repeat から pure Beatty cycle equation への橋

free-base repeated block の scaled difference が zero になった後は、
入口指数の絶対値を固定する必要はない。

このファイルでは attached straight suffix の relative depth formula を使い、
`Q=q+1` の block numerator を pure Beatty cycle numerator

  beattyCyclePhi(start+i, n)

へ exact に変換する。

これにより zero scaled state は

  (3^p - 2^(p+Delta)) Q_i
    = 2^(delta_i) * beattyCyclePhi(start+i,p)

という Collatz 非依存の cycle equation を満たす。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace AttachedTwoCornerPacket

/-- attached actual `Q` block numerator は common dyadic factor と Beatty cycle numerator の積。 -/
theorem qOneBlockNumerator_eq_pow_mul_beattyCyclePhi
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i n : ℕ}
    (hEnd : i + n ≤ A.straightHenselWidth) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    C.qOneBlockNumerator i n =
      (2 : ℤ) ^ C.delta i *
        beattyCyclePhi (A.straightHenselStart + i) n := by
  dsimp
  let C := A.toFreeBaseMonotoneHenselChain hStart
  revert hEnd
  induction n with
  | zero =>
      intro hEnd
      simp [FreeBaseMonotoneHenselChain.qOneBlockNumerator,
        beattyCyclePhi]
  | succ n ih =>
      intro hEnd
      have hPrev : i + n ≤ A.straightHenselWidth := by omega
      have hOccI : i < A.straightHenselWidth := by omega
      have hOccN : i + n < A.straightHenselWidth := by omega
      have hIH := ih hPrev
      have hPhi := beattyCyclePhi_succ (A.straightHenselStart + i) n
      have hExp :=
        A.straightHenselDelta_relative_exact
          hStart hOccI hOccN
      dsimp [C] at hExp
      have hPow :
          (2 : ℤ) ^ n * (2 : ℤ) ^ C.delta (i + n) =
            (2 : ℤ) ^ C.delta i *
              (2 : ℤ) ^
                (beattyIndex (A.straightHenselStart + i + n) -
                  beattyIndex (A.straightHenselStart + i)) := by
        rw [← pow_add, ← pow_add]
        congr 1
      change
        3 * C.qOneBlockNumerator i n +
            (2 : ℤ) ^ n * (2 : ℤ) ^ C.delta (i + n) =
          (2 : ℤ) ^ C.delta i *
            beattyCyclePhi (A.straightHenselStart + i) (n + 1)
      rw [hIH, hPow, hPhi]
      ring

/-- zero scaled state の period `p` に対する exact Beatty cycle equation。 -/
theorem zeroScaledState_cycleEquation
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i p Delta : ℕ}
    (hEnd : i + p ≤ A.straightHenselWidth)
    (hState :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.ScaledState i (i + p) Delta) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    ((3 : ℤ) ^ p - (2 : ℤ) ^ (p + Delta)) * C.qOne i =
      (2 : ℤ) ^ C.delta i *
        beattyCyclePhi (A.straightHenselStart + i) p := by
  dsimp at hState ⊢
  let C := A.toFreeBaseMonotoneHenselChain hStart
  have hEndC : i + p ≤ C.width := by
    change i + p ≤ A.straightHenselWidth
    exact hEnd
  have hIter := C.qOne_iterate (i := i) (n := p) hEndC
  have hNum :=
    A.qOneBlockNumerator_eq_pow_mul_beattyCyclePhi hStart hEnd
  dsimp [C] at hNum
  have hQ :
      C.qOne (i + p) = (2 : ℤ) ^ Delta * C.qOne i :=
    hState.2
  rw [hQ, hNum] at hIter
  rw [pow_add]
  ring_nf at hIter ⊢
  linarith

/-- zero repeat の各 rotation でも同じ scaled state が保たれる。 -/
theorem zeroRepeat_rotation_scaledState
    {P : PureBProfileObstruction}
    (A : AttachedTwoCornerPacket P)
    (hStart : 0 < P.criticalizationStart)
    {i p m Delta r : ℕ}
    (hiEnd : i + m ≤ A.straightHenselWidth)
    (hjEnd : i + p + m ≤ A.straightHenselWidth)
    (hBlock :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.SameDeltaOffsetBlock i (i + p) m Delta)
    (hZero :
      let C := A.toFreeBaseMonotoneHenselChain hStart
      C.scaledDifference i (i + p) Delta 0 = 0)
    (hr : r ≤ m) :
    let C := A.toFreeBaseMonotoneHenselChain hStart
    C.ScaledState (i + r) (i + p + r) Delta := by
  dsimp only at hBlock hZero ⊢
  let C := A.toFreeBaseMonotoneHenselChain hStart
  have hiEndC : i + m ≤ C.width := by
    change i + m ≤ A.straightHenselWidth
    exact hiEnd
  have hjEndC : i + p + m ≤ C.width := by
    change i + p + m ≤ A.straightHenselWidth
    exact hjEnd
  have hState :=
    C.scaledState_at_of_zero_repeat
      (i := i)
      (j := i + p)
      (m := m)
      (Delta := Delta)
      (r := r)
      hiEndC hjEndC hBlock hZero hr
  simpa [Nat.add_assoc] using hState

end AttachedTwoCornerPacket

end MultiCorner
end CSTMicro
end Collatz2
