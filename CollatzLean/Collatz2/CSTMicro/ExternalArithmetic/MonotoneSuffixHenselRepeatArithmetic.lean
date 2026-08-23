import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselChain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Monotone suffix Hensel chain: repeated-block arithmetic

`MonotoneSuffixHenselChain` の recurrence

  3 q_i = 2 q_(i+1) + 2^(delta_i) - 1

を `Q_i := q_i + 1` に持ち上げると

  3 Q_i = 2 Q_(i+1) + 2^(delta_i)

となる。

二つの index 区間で exponent profile が一定量 `Delta` だけ平行移動していると、
対応する scaled difference

  M_r = Q_(j+r) - 2^Delta Q_(i+r)

では forcing term が exact に消え、

  2 M_(r+1) = 3 M_r

を満たす。従って block 長 `m` について

  2^m M_m = 3^m M_0

となる。

また scaled state が途中で exact に一致した場合、その一致は
backward predecessor の一意性により entrance 側へ伝播する。

ここでは repeated factor の存在や large-width termination は主張しない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MonotoneSuffixHenselChain

/-- shifted quotient `Q_i = q_i + 1`。 -/
def qOne
    (C : MonotoneSuffixHenselChain)
    (i : ℕ) : ℤ :=
  C.q i + 1

/-- `q` recurrence を `Q=q+1` へ持ち上げた exact recurrence。 -/
theorem qOne_recurrence
    (C : MonotoneSuffixHenselChain)
    {i : ℕ}
    (hi : i < C.width) :
    3 * C.qOne i =
      2 * C.qOne (i + 1) + (2 : ℤ) ^ C.delta i := by
  unfold qOne
  have h := C.recurrence i hi
  linarith

/--
二つの区間で exponent profile が一定量 `Delta` だけ平行移動していること。

endpoint `r = m` まで含めて持つ。
-/
def SameDeltaOffsetBlock
    (C : MonotoneSuffixHenselChain)
    (i j m Delta : ℕ) : Prop :=
  ∀ r : ℕ, r ≤ m →
    C.delta (j + r) = C.delta (i + r) + Delta

/-- repeated block に対応する scaled quotient difference。 -/
def scaledDifference
    (C : MonotoneSuffixHenselChain)
    (i j Delta r : ℕ) : ℤ :=
  C.qOne (j + r) -
    (2 : ℤ) ^ Delta * C.qOne (i + r)

/--
parallel exponent profile の一段では forcing が消え、
scaled difference は exact に `2 M_(r+1) = 3 M_r` を満たす。
-/
theorem scaledDifference_step
    (C : MonotoneSuffixHenselChain)
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
  have hIndexI :
      i + r + 1 = i + (r + 1) := by
    omega
  have hIndexJ :
      j + r + 1 = j + (r + 1) := by
    omega
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
長さ `m` の parallel block 全体で

  2^m M_m = 3^m M_0

が成立する。
-/
theorem scaledDifference_transport
    (C : MonotoneSuffixHenselChain)
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

/-- nonzero repeat の入口 difference は `2^m` で割れる。 -/
theorem twoPow_dvd_scaledDifference_zero
    (C : MonotoneSuffixHenselChain)
    {i j m Delta : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta) :
    (2 : ℤ) ^ m ∣ C.scaledDifference i j Delta 0 := by
  have hTransport :=
    C.scaledDifference_transport hiEnd hjEnd hBlock
  have hDiv :
      (2 : ℤ) ^ m ∣
        (3 : ℤ) ^ m * C.scaledDifference i j Delta 0 := by
    refine ⟨C.scaledDifference i j Delta m, ?_⟩
    exact hTransport.symm
  have hTwoThree : IsCoprime (2 : ℤ) (3 : ℤ) := by
    refine ⟨-1, 1, ?_⟩
    norm_num
  have hCoprime :
      IsCoprime ((2 : ℤ) ^ m) ((3 : ℤ) ^ m) := by
    exact hTwoThree.pow
  exact hCoprime.dvd_of_dvd_mul_left hDiv

/-- block endpoint difference は `3^m` で割れる。 -/
theorem threePow_dvd_scaledDifference_end
    (C : MonotoneSuffixHenselChain)
    {i j m Delta : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetBlock i j m Delta) :
    (3 : ℤ) ^ m ∣ C.scaledDifference i j Delta m := by
  have hTransport :=
    C.scaledDifference_transport hiEnd hjEnd hBlock
  have hDiv :
      (3 : ℤ) ^ m ∣
        (2 : ℤ) ^ m * C.scaledDifference i j Delta m := by
    refine ⟨C.scaledDifference i j Delta 0, ?_⟩
    exact hTransport
  have hThreeTwo : IsCoprime (3 : ℤ) (2 : ℤ) := by
    refine ⟨1, -1, ?_⟩
    norm_num
  have hCoprime :
      IsCoprime ((3 : ℤ) ^ m) ((2 : ℤ) ^ m) := by
    exact hThreeTwo.pow
  exact hCoprime.dvd_of_dvd_mul_left hDiv

/--
index `i,j` の state が exponent shift `Delta` と dyadic scaling で一致すること。
-/
def ScaledState
    (C : MonotoneSuffixHenselChain)
    (i j Delta : ℕ) : Prop :=
  C.delta j = C.delta i + Delta ∧
    C.qOne j = (2 : ℤ) ^ Delta * C.qOne i

/--
scaled state が内部で一致しているなら、一段左の actual predecessor も
同じ exponent shift / dyadic scaling で一致する。
-/
theorem scaledState_pred
    (C : MonotoneSuffixHenselChain)
    {i j Delta : ℕ}
    (hiPos : 0 < i)
    (hij : i ≤ j)
    (hj : j < C.width)
    (hState : C.ScaledState i j Delta) :
    C.ScaledState (i - 1) (j - 1) Delta := by
  have hi : i < C.width := by omega
  have hjPos : 0 < j := by omega
  have hiPred : i - 1 + 1 = i := by omega
  have hjPred : j - 1 + 1 = j := by omega
  let dCand : ℕ := C.delta (i - 1) + Delta
  let qCand : ℤ :=
    (2 : ℤ) ^ Delta * C.qOne (i - 1) - 1
  have hStepI := C.delta_step (i - 1) (by omega)
  have hStair :
      dCand = C.delta j ∨ dCand + 1 = C.delta j := by
    rcases hStepI with hSame | hUp
    · left
      dsimp [dCand]
      rw [hiPred] at hSame
      rw [hState.1]
      omega
    · right
      dsimp [dCand]
      rw [hiPred] at hUp
      rw [hState.1]
      omega
  have hRecPred := C.qOne_recurrence (i := i - 1) (by omega)
  rw [hiPred] at hRecPred
  have hPowCand :
      (2 : ℤ) ^ dCand =
        (2 : ℤ) ^ Delta *
          (2 : ℤ) ^ C.delta (i - 1) := by
    dsimp [dCand]
    rw [pow_add]
    ring
  have hCandSucc :
      qCand + 1 =
        (2 : ℤ) ^ Delta * C.qOne (i - 1) := by
    dsimp [qCand]
    ring
  have hCandQ :
      3 * (qCand + 1) =
        2 * (C.q j + 1) + (2 : ℤ) ^ dCand := by
    rw [hCandSucc, hPowCand]
    calc
      3 * ((2 : ℤ) ^ Delta * C.qOne (i - 1))
          = (2 : ℤ) ^ Delta * (3 * C.qOne (i - 1)) := by ring
      _ = (2 : ℤ) ^ Delta *
            (2 * C.qOne i + (2 : ℤ) ^ C.delta (i - 1)) := by
              rw [hRecPred]
      _ = 2 * ((2 : ℤ) ^ Delta * C.qOne i) +
            (2 : ℤ) ^ Delta * (2 : ℤ) ^ C.delta (i - 1) := by ring
      _ = 2 * C.qOne j +
            (2 : ℤ) ^ Delta * (2 : ℤ) ^ C.delta (i - 1) := by
              rw [← hState.2]
      _ = 2 * (C.q j + 1) +
            (2 : ℤ) ^ Delta * (2 : ℤ) ^ C.delta (i - 1) := by
              rfl
  have hCand :
      IsBackwardPredecessor
        (C.q j) (C.delta j) dCand qCand := by
    constructor
    · exact hStair
    · linarith [hCandQ]
  have hActual0 :=
    C.actual_isBackwardPredecessor
      (i := j - 1) (by omega)
  have hActual :
      IsBackwardPredecessor
        (C.q j) (C.delta j)
        (C.delta (j - 1)) (C.q (j - 1)) := by
    simpa [hjPred] using hActual0
  have hUnique := backwardPredecessor_unique hCand hActual
  constructor
  · dsimp [dCand] at hUnique
    exact hUnique.1.symm
  · have hQ := hUnique.2
    dsimp [qCand] at hQ
    unfold qOne at hQ ⊢
    calc
      C.q (j - 1) + 1
          =
        ((2 : ℤ) ^ Delta *
            (C.q (i - 1) + 1) - 1) + 1 := by
              rw [← hQ]
      _ =
        (2 : ℤ) ^ Delta *
          (C.q (i - 1) + 1) := by
            ring

/--
途中の scaled-state equality は entrance まで自動的に引き戻せる。

`i <= j < width` で

  delta_j = delta_i + Delta,
  Q_j = 2^Delta Q_i

なら、shift `j-i` の位置と entrance `0` の間でも同じ equality が成立する。
-/
theorem scaledState_propagate_to_zero
    (C : MonotoneSuffixHenselChain)
    {i j Delta : ℕ}
    (hij : i ≤ j)
    (hj : j < C.width)
    (hState : C.ScaledState i j Delta) :
    C.ScaledState 0 (j - i) Delta := by
  induction i generalizing j with
  | zero =>
      simpa using hState
  | succ i ih =>
      have hPred :=
        C.scaledState_pred
          (i := i + 1) (j := j) (Delta := Delta)
          (by omega) hij hj hState
      have hJPred : j - 1 < C.width := by omega
      have hIJPred : i ≤ j - 1 := by omega
      have hPred' : C.ScaledState i (j - 1) Delta := by
        simpa using hPred
      have hIH := ih hIJPred hJPred hPred'
      have hShift : (j - 1) - i = j - (i + 1) := by omega
      rw [hShift] at hIH
      exact hIH

/-- zero scaled difference は `ScaledState` の quotient 側 equality と同値。 -/
theorem scaledDifference_zero_eq_zero_iff
    (C : MonotoneSuffixHenselChain)
    {i j Delta : ℕ} :
    C.scaledDifference i j Delta 0 = 0 ↔
      C.qOne j = (2 : ℤ) ^ Delta * C.qOne i := by
  unfold scaledDifference
  simp only [Nat.add_zero]
  constructor <;> intro h <;> linarith

end MonotoneSuffixHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
