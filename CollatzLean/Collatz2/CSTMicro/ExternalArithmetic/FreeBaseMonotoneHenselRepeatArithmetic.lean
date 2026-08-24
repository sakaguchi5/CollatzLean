import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselChain
import Mathlib.Tactic.Positivity
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Free-base monotone Hensel chain: repeated-block arithmetic

attached branch では restarted branch と異なり入口指数 `delta 0 = 1` を持たない。
一方、repeated exponent block 上で forcing を消去する局所算術には入口値は不要である。

このファイルでは free-base chain

  3 q_i = 2 q_(i+1) + 2^(delta_i) - 1

を `Q_i = q_i + 1` に持ち上げ、二つの exponent profile が一定 offset `Delta` だけ
平行移動しているときの scaled difference

  M_r = Q_(j+r) - 2^Delta Q_(i+r)

について

  2 M_(r+1) = 3 M_r,
  2^m M_m = 3^m M_0

を証明する。

ここには `delta 0 = 1` を一切仮定しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace FreeBaseMonotoneHenselChain

/-- occupied interval 上では `delta` は右へ進んでも減らない。 -/
theorem delta_mono_add
    (C : FreeBaseMonotoneHenselChain)
    {i r : ℕ}
    (hEnd : i + r < C.width) :
    C.delta i ≤ C.delta (i + r) := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      have hPrevEnd : i + r < C.width := by
        omega
      have hIH := ih hPrevEnd
      have hStep :=
        C.delta_step (i + r) (by omega)
      simp only [Nat.add_assoc] at hStep ⊢
      rcases hStep with hSame | hUp
      · rw [hSame]
        exact hIH
      · rw [hUp]
        omega

/-- occupied interval上の任意の二点で `delta` は単調。 -/
theorem delta_mono_of_le
    (C : FreeBaseMonotoneHenselChain)
    {i j : ℕ}
    (hij : i ≤ j)
    (hj : j < C.width) :
    C.delta i ≤ C.delta j := by
  let r := j - i
  have hIdx : i + r = j := by
    dsimp [r]
    omega
  have hEnd : i + r < C.width := by
    rw [hIdx]
    exact hj
  have h := C.delta_mono_add hEnd
  rw [hIdx] at h
  exact h

/--
二つの区間で exponent profile が一定量 `Delta` だけ平行移動していること。
endpoint `r = m` まで含める。
-/
def SameDeltaOffsetBlock
    (C : FreeBaseMonotoneHenselChain)
    (i j m Delta : ℕ) : Prop :=
  ∀ r : ℕ, r ≤ m →
    C.delta (j + r) = C.delta (i + r) + Delta

/-- repeated block に対応する shifted quotient の差。 -/
def scaledDifference
    (C : FreeBaseMonotoneHenselChain)
    (i j Delta r : ℕ) : ℤ :=
  C.qOne (j + r) -
    (2 : ℤ) ^ Delta * C.qOne (i + r)

/--
parallel exponent profile の一段では forcing が exact に消え、
scaled difference は `2 M_(r+1) = 3 M_r` を満たす。
-/
theorem scaledDifference_step
    (C : FreeBaseMonotoneHenselChain)
    {i j Delta r : ℕ}
    (hi : i + r < C.width)
    (hj : j + r < C.width)
    (hDelta :
      C.delta (j + r) =
        C.delta (i + r) + Delta) :
    2 * C.scaledDifference i j Delta (r + 1) =
      3 * C.scaledDifference i j Delta r := by
  have hLeft := C.qOne_recurrence (i := i + r) hi
  have hRight := C.qOne_recurrence (i := j + r) hj
  have hPow :
      (2 : ℤ) ^ C.delta (j + r) =
        (2 : ℤ) ^ Delta *
          (2 : ℤ) ^ C.delta (i + r) := by
    rw [hDelta, pow_add]
    ring
  unfold scaledDifference
  have hIndexI : i + r + 1 = i + (r + 1) := by omega
  have hIndexJ : j + r + 1 = j + (r + 1) := by omega
  rw [hIndexI] at hLeft
  rw [hIndexJ] at hRight
  rw [hPow] at hRight
  have hLeftScaled :=
    congrArg
      (fun z : ℤ => (2 : ℤ) ^ Delta * z)
      hLeft
  ring_nf at hLeftScaled hRight ⊢
  linarith

/--
長さ `m` の parallel block 全体では

  2^m M_m = 3^m M_0

が成立する。
-/
theorem scaledDifference_transport
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta) :
    (2 : ℤ) ^ m * C.scaledDifference i j Delta m =
      (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 := by
  have hAll :
      ∀ r : ℕ, r ≤ m →
        (2 : ℤ) ^ r * C.scaledDifference i j Delta r =
          (3 : ℤ) ^ r * C.scaledDifference i j Delta 0 := by
    intro r hr
    induction r with
    | zero =>
        simp
    | succ r ih =>
        have hrLt : r < m := by omega
        have hi : i + r < C.width := by omega
        have hj : j + r < C.width := by omega
        have hStep :=
          C.scaledDifference_step
            (i := i) (j := j) (Delta := Delta) (r := r)
            hi hj (hBlock r (by omega))
        have hIH := ih (by omega)
        rw [pow_succ, pow_succ]
        calc
          (2 : ℤ) ^ r * 2 * C.scaledDifference i j Delta (r + 1)
              = (2 : ℤ) ^ r *
                  (2 * C.scaledDifference i j Delta (r + 1)) := by ring
          _ = (2 : ℤ) ^ r *
                (3 * C.scaledDifference i j Delta r) := by rw [hStep]
          _ = 3 *
                ((2 : ℤ) ^ r * C.scaledDifference i j Delta r) := by ring
          _ = 3 *
                ((3 : ℤ) ^ r * C.scaledDifference i j Delta 0) := by rw [hIH]
          _ = (3 : ℤ) ^ r * 3 * C.scaledDifference i j Delta 0 := by ring
  exact hAll m le_rfl

/-- repeated block の入口 difference は `2^m` で割れる。 -/
theorem twoPow_dvd_scaledDifference_zero
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta) :
    (2 : ℤ) ^ m ∣ C.scaledDifference i j Delta 0 := by
  have hTransport := C.scaledDifference_transport hiEnd hjEnd hBlock
  have hDiv :
      (2 : ℤ) ^ m ∣
        (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 := by
    refine ⟨C.scaledDifference i j Delta m, ?_⟩
    exact hTransport.symm
  have hTwoThree : IsCoprime (2 : ℤ) (3 : ℤ) := by
    refine ⟨-1, 1, ?_⟩
    norm_num
  have hCoprime :
      IsCoprime ((2 : ℤ) ^ m) ((3 : ℤ) ^ m) :=
    hTwoThree.pow
  exact hCoprime.dvd_of_dvd_mul_left hDiv

/-- repeated block の右端 difference は `3^m` で割れる。 -/
theorem threePow_dvd_scaledDifference_end
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta) :
    (3 : ℤ) ^ m ∣ C.scaledDifference i j Delta m := by
  have hTransport := C.scaledDifference_transport hiEnd hjEnd hBlock
  have hDiv :
      (3 : ℤ) ^ m ∣
        (2 : ℤ) ^ m * C.scaledDifference i j Delta m := by
    refine ⟨C.scaledDifference i j Delta 0, ?_⟩
    exact hTransport
  have hThreeTwo : IsCoprime (3 : ℤ) (2 : ℤ) := by
    refine ⟨1, -1, ?_⟩
    norm_num
  have hCoprime :
      IsCoprime ((3 : ℤ) ^ m) ((2 : ℤ) ^ m) :=
    hThreeTwo.pow
  exact hCoprime.dvd_of_dvd_mul_left hDiv

/-- exponent shift と shifted quotient scaling が同時に一致する state。 -/
def ScaledState
    (C : FreeBaseMonotoneHenselChain)
    (i j Delta : ℕ) : Prop :=
  C.delta j = C.delta i + Delta ∧
    C.qOne j = (2 : ℤ) ^ Delta * C.qOne i

/-- offset `0` の scaled difference が zero であることの言い換え。 -/
theorem scaledDifference_zero_eq_zero_iff
    (C : FreeBaseMonotoneHenselChain)
    {i j Delta : ℕ} :
    C.scaledDifference i j Delta 0 = 0 ↔
      C.qOne j = (2 : ℤ) ^ Delta * C.qOne i := by
  unfold scaledDifference
  simp only [Nat.add_zero]
  constructor <;> intro h <;> linarith

/-- repeated block transport は scaled difference の正符号を保存する。 -/
theorem scaledDifference_pos_of_pos_zero
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta r : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta)
    (hPos : 0 < C.scaledDifference i j Delta 0)
    (hr : r ≤ m) :
    0 < C.scaledDifference i j Delta r := by
  have hTransport :=
    C.scaledDifference_transport
      (i := i) (j := j) (m := r) (Delta := Delta)
      (by omega) (by omega)
      (fun t ht => hBlock t (le_trans ht hr))
  have hTwoPos : 0 < (2 : ℤ) ^ r := by positivity
  have hThreePos : 0 < (3 : ℤ) ^ r := by positivity
  nlinarith

/-- repeated block transport は scaled difference の負符号を保存する。 -/
theorem scaledDifference_neg_of_neg_zero
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta r : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta)
    (hNeg : C.scaledDifference i j Delta 0 < 0)
    (hr : r ≤ m) :
    C.scaledDifference i j Delta r < 0 := by
  have hTransport :=
    C.scaledDifference_transport
      (i := i) (j := j) (m := r) (Delta := Delta)
      (by omega) (by omega)
      (fun t ht => hBlock t (le_trans ht hr))
  have hTwoPos : 0 < (2 : ℤ) ^ r := by positivity
  have hThreePos : 0 < (3 : ℤ) ^ r := by positivity
  nlinarith

end FreeBaseMonotoneHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
