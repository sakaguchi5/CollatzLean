import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselRepeatArithmetic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Free-base monotone Hensel chain: zero-repeat arithmetic

repeated block の入口 scaled difference が zero なら、

  Q_j = 2^Delta Q_i

という scaled state は repeated block の全 offset に伝播する。
また `Q=q+1` recurrence の有限展開を定義し、zero-cycle equation を作るための
pure arithmetic を free-base chain 上に用意する。

ここにも入口条件 `delta 0 = 1` は現れない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace FreeBaseMonotoneHenselChain

/-- `qOne` recurrence を `n` 段展開したときの forcing numerator。 -/
def qOneBlockNumerator
    (C : FreeBaseMonotoneHenselChain)
    (i : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 =>
      3 * C.qOneBlockNumerator i n +
        (2 : ℤ) ^ n * (2 : ℤ) ^ C.delta (i + n)

@[simp] theorem qOneBlockNumerator_zero
    (C : FreeBaseMonotoneHenselChain)
    (i : ℕ) :
    C.qOneBlockNumerator i 0 = 0 := rfl

/-- `Q` recurrence の exact `n`-step 展開。 -/
theorem qOne_iterate
    (C : FreeBaseMonotoneHenselChain)
    {i n : ℕ}
    (hEnd : i + n ≤ C.width) :
    (3 : ℤ) ^ n * C.qOne i =
      (2 : ℤ) ^ n * C.qOne (i + n) +
        C.qOneBlockNumerator i n := by
  revert hEnd
  induction n with
  | zero =>
      intro hEnd
      simp
  | succ n ih =>
      intro hEnd
      have hPrev : i + n ≤ C.width := by omega
      have hiN : i + n < C.width := by omega
      have hIH := ih hPrev
      have hRec := C.qOne_recurrence (i := i + n) hiN
      have hIdx : i + n + 1 = i + (n + 1) := by omega
      rw [hIdx] at hRec
      change
        (3 : ℤ) ^ (n + 1) * C.qOne i =
          (2 : ℤ) ^ (n + 1) * C.qOne (i + (n + 1)) +
            (3 * C.qOneBlockNumerator i n +
              (2 : ℤ) ^ n * (2 : ℤ) ^ C.delta (i + n))
      rw [pow_succ, pow_succ]
      calc
        (3 : ℤ) ^ n * 3 * C.qOne i
            = 3 * ((3 : ℤ) ^ n * C.qOne i) := by ring
        _ = 3 *
            ((2 : ℤ) ^ n * C.qOne (i + n) +
              C.qOneBlockNumerator i n) := by rw [hIH]
        _ =
            (2 : ℤ) ^ n * (3 * C.qOne (i + n)) +
              3 * C.qOneBlockNumerator i n := by ring
        _ =
            (2 : ℤ) ^ n *
                (2 * C.qOne (i + (n + 1)) +
                  (2 : ℤ) ^ C.delta (i + n)) +
              3 * C.qOneBlockNumerator i n := by rw [hRec]
        _ =
            (2 : ℤ) ^ n * 2 * C.qOne (i + (n + 1)) +
              (3 * C.qOneBlockNumerator i n +
                (2 : ℤ) ^ n *
                  (2 : ℤ) ^ C.delta (i + n)) := by ring

/-- zero repeat は repeated block の全 intermediate offset に伝播する。 -/
theorem scaledDifference_eq_zero_of_zero_repeat
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta)
    (hZero : C.scaledDifference i j Delta 0 = 0) :
    ∀ r : ℕ, r ≤ m →
      C.scaledDifference i j Delta r = 0 := by
  intro r
  induction r with
  | zero =>
      intro hr
      exact hZero
  | succ r ih =>
      intro hr
      have hrLt : r < m := by omega
      have hi : i + r < C.width := by omega
      have hj : j + r < C.width := by omega
      have hStep :=
        C.scaledDifference_step
          (i := i) (j := j) (Delta := Delta) (r := r)
          hi hj (hBlock r (by omega))
      have hPrev := ih (by omega)
      rw [hPrev] at hStep
      linarith

/-- zero repeat の各 offset は scaled state そのものになる。 -/
theorem scaledState_at_of_zero_repeat
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta r : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta)
    (hZero : C.scaledDifference i j Delta 0 = 0)
    (hr : r ≤ m) :
    C.ScaledState (i + r) (j + r) Delta := by
  constructor
  · exact hBlock r hr
  · have hMr :=
      C.scaledDifference_eq_zero_of_zero_repeat
        hiEnd hjEnd hBlock hZero r hr
    have hEq :=
      (C.scaledDifference_zero_eq_zero_iff
        (i := i + r) (j := j + r) (Delta := Delta)).1
        (by simpa [scaledDifference, Nat.add_assoc] using hMr)
    exact hEq

end FreeBaseMonotoneHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
