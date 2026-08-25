import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.FreeBaseMonotoneHenselAdjacentReturn
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.ChristoffelDefectValuation


/-!
# Free-base Hensel return: terminal 到達時の exact 3-adic order

既存 `SameDeltaOffsetBlock` は endpoint `r = m` の delta equality まで要求する。
しかし terminal では `q width = 0` であり、attached geometry では terminal delta reset が起こるため、
terminal に到達する transport には endpoint の delta equality を要求してはいけない。

そこで step に本当に必要な

  0 ≤ r < m

だけの open block を導入し、

  2^m M_m = 3^m M_0

を endpoint delta を使わずに証明する。

さらに maximal-left stop から `3 ∤ M_0` を受け取ると、terminal endpoint の `Q_width = 1` により

  1 - 2^Delta Q_(i+m)

が exact に 3^m まで割れることが分かる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace FreeBaseMonotoneHenselChain

/--
endpoint を含めない constant-offset block。
transport の各 step `r -> r+1` に必要なのは `r < m` の exponent equality だけである。
-/
def SameDeltaOffsetOpenBlock
    (C : FreeBaseMonotoneHenselChain)
    (i j m Delta : ℕ) : Prop :=
  ∀ r : ℕ, r < m →
    C.delta (j + r) = C.delta (i + r) + Delta

/-- closed block から open block へ忘却する。 -/
theorem sameDeltaOffsetOpenBlock_of_sameDeltaOffsetBlock
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta : ℕ}
    (hBlock : C.SameDeltaOffsetBlock i j m Delta) :
    C.SameDeltaOffsetOpenBlock i j m Delta := by
  intro r hr
  exact hBlock r (Nat.le_of_lt hr)

/--
open block 全体でも exact transport

  2^m M_m = 3^m M_0

が成立する。endpoint `delta (i+m), delta (j+m)` は一切使わない。
-/
theorem scaledDifference_transport_open
    (C : FreeBaseMonotoneHenselChain)
    {i j m Delta : ℕ}
    (hiEnd : i + m ≤ C.width)
    (hjEnd : j + m ≤ C.width)
    (hBlock : C.SameDeltaOffsetOpenBlock i j m Delta) :
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
            hi hj (hBlock r hrLt)
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

/-- terminal quotient `q width = 0` を `Q = q+1` に持ち上げると `Q_width = 1`。 -/
theorem qOne_terminal
    (C : FreeBaseMonotoneHenselChain) :
    C.qOne C.width = 1 := by
  unfold qOne
  rw [C.q_terminal]
  norm_num

/--
`2^t y = 3^t x` かつ `x` が mod 3 unit なら、`y` の 3-adic order は exact に `t`。
Collatz geometry を含まない pure arithmetic lemma。
-/
theorem exactThreeAdicOrder_of_twoPow_transport
    {t : ℕ}
    {x y : ℤ}
    (hTransport :
      (2 : ℤ) ^ t * y = (3 : ℤ) ^ t * x)
    (hUnit : ¬ (3 : ℤ) ∣ x) :
    ExactThreeAdicOrder y t := by
  constructor
  · have hDivProd :
        (3 : ℤ) ^ t ∣ (2 : ℤ) ^ t * y := by
      exact ⟨x, hTransport⟩
    have hThreeTwo : IsCoprime (3 : ℤ) (2 : ℤ) := by
      refine ⟨1, -1, ?_⟩
      norm_num
    have hCoprime :
        IsCoprime ((3 : ℤ) ^ t) ((2 : ℤ) ^ t) :=
      hThreeTwo.pow
    exact hCoprime.dvd_of_dvd_mul_left hDivProd
  · intro hDeep
    rcases hDeep with ⟨u, hu⟩
    have hPowNe : (3 : ℤ) ^ t ≠ 0 := by positivity
    have hCancelEq :
        (3 : ℤ) ^ t * x =
          (3 : ℤ) ^ t * (3 * ((2 : ℤ) ^ t * u)) := by
      calc
        (3 : ℤ) ^ t * x
            = (2 : ℤ) ^ t * y := hTransport.symm
        _ = (2 : ℤ) ^ t * ((3 : ℤ) ^ (t + 1) * u) := by rw [hu]
        _ = (3 : ℤ) ^ t * (3 * ((2 : ℤ) ^ t * u)) := by
              rw [pow_succ]
              ring
    have hx : x = 3 * ((2 : ℤ) ^ t * u) :=
      mul_left_cancel₀ hPowNe hCancelEq
    apply hUnit
    exact ⟨(2 : ℤ) ^ t * u, hx⟩

/--
open repeat の右 occurrence が terminal に到達し、左 predecessor で offset が壊れているなら、
terminal qOne difference は exact に `3^T` まで割れる。

右 endpoint では `Q_width = 1` なので結論は

  ExactThreeAdicOrder (1 - 2^Delta * Q_(i+T)) T

という terminal-local certificate になる。
-/
theorem terminalReachedReturn_exactThreeAdicOrder_qOne
    (C : FreeBaseMonotoneHenselChain)
    {i j Delta T : ℕ}
    (hiPos : 0 < i)
    (hij : i < j)
    (hTPos : 0 < T)
    (hjTerminal : j + T = C.width)
    (hBlock : C.SameDeltaOffsetOpenBlock i j T Delta)
    (hStop : C.delta (j - 1) ≠ C.delta (i - 1) + Delta) :
    ExactThreeAdicOrder
      (1 - (2 : ℤ) ^ Delta * C.qOne (i + T)) T := by
  have hjPos : 0 < j := by omega
  have hj : j < C.width := by omega
  have hi : i < C.width := by omega
  have hiEnd : i + T ≤ C.width := by omega
  have hjEnd : j + T ≤ C.width := by omega
  have hDelta : C.delta j = C.delta i + Delta := by
    have h := hBlock 0 hTPos
    simpa using h
  have hUnit :
      ¬ (3 : ℤ) ∣ C.scaledDifference i j Delta 0 :=
    C.three_not_dvd_scaledDifference_zero_of_not_leftExtendable
      hiPos hjPos hi hj hDelta hStop
  have hTransport :=
    C.scaledDifference_transport_open
      (i := i) (j := j) (m := T) (Delta := Delta)
      hiEnd hjEnd hBlock
  have hExact :
      ExactThreeAdicOrder
        (C.scaledDifference i j Delta T) T :=
    exactThreeAdicOrder_of_twoPow_transport hTransport hUnit
  have hTerminal : C.qOne C.width = 1 := C.qOne_terminal
  have hEndEq :
      C.scaledDifference i j Delta T =
        1 - (2 : ℤ) ^ Delta * C.qOne (i + T) := by
    unfold scaledDifference
    rw [hjTerminal, hTerminal]
  rw [hEndEq] at hExact
  exact hExact

end FreeBaseMonotoneHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
