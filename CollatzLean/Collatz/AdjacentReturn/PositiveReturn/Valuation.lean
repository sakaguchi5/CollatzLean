import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.BiCanonical
import CollatzLean.Collatz.AdjacentReturn.GapDepthDichotomy

/-!
# positive return chain の full 2-adic recurrence

valuation triangle を depth だけでなく odd part まで保持する。
start-lower / equal-cancellation / next-lower の三枝で exact recurrence を与える。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace CanonicalChain

/-- adjacent block の三つの exact factorization を加法式として同時に書く。 -/
theorem valuation_full_recurrence
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    2 ^ (C.core.valuationData n).nextDepth *
        (C.core.valuationData n).nextOddPart =
      2 ^ (C.core.valuationData n).startDepth *
          (C.core.valuationData n).startOddPart +
        2 ^ (C.core.valuationData n).gapDepth *
          (C.core.valuationData n).gapOddPart := by
  let V := C.core.valuationData n
  have hnext :
      2 ^ V.nextDepth * V.nextOddPart =
        (C.state n).nextValue + 1 := V.nextFactor.1.symm
  have hstart :
      (C.state n).startValue + 1 =
        2 ^ V.startDepth * V.startOddPart := V.startFactor.1
  have hgap :
      (C.state n).valueGap =
        2 ^ V.gapDepth * V.gapOddPart := V.gapFactor.1
  calc
    2 ^ V.nextDepth * V.nextOddPart
        = (C.state n).nextValue + 1 := hnext
    _ = ((C.state n).startValue + 1) + (C.state n).valueGap := by
      rw [(C.state n).nextValue_eq_startValue_add_valueGap]
      omega
    _ = 2 ^ V.startDepth * V.startOddPart +
          2 ^ V.gapDepth * V.gapOddPart := by rw [hstart, hgap]

/-- start-lower 枝の odd-part recurrence。 -/
theorem valuation_startLower_oddPart_recurrence
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ)
    (h :
      (C.core.valuationData n).startDepth <
        (C.core.valuationData n).nextDepth) :
    2 ^ ((C.core.valuationData n).nextDepth -
          (C.core.valuationData n).startDepth) *
        (C.core.valuationData n).nextOddPart =
      (C.core.valuationData n).startOddPart +
        (C.core.valuationData n).gapOddPart := by
  let V := C.core.valuationData n
  have hV : V.startDepth < V.nextDepth := by simpa [V] using h
  have hgap : V.gapDepth = V.startDepth :=
    V.gapDepth_eq_startDepth_of_lt hV
  have hsplit :
      V.nextDepth = V.startDepth + (V.nextDepth - V.startDepth) :=
    (Nat.add_sub_of_le (Nat.le_of_lt hV)).symm
  have hfull := C.valuation_full_recurrence n
  change
    2 ^ V.nextDepth * V.nextOddPart =
      2 ^ V.startDepth * V.startOddPart +
        2 ^ V.gapDepth * V.gapOddPart at hfull
  rw [hgap, hsplit, pow_add] at hfull
  have hscaled :
      2 ^ V.startDepth *
          (2 ^ (V.nextDepth - V.startDepth) * V.nextOddPart) =
        2 ^ V.startDepth * (V.startOddPart + V.gapOddPart) := by
    calc
      2 ^ V.startDepth *
          (2 ^ (V.nextDepth - V.startDepth) * V.nextOddPart)
          = (2 ^ V.startDepth *
              2 ^ (V.nextDepth - V.startDepth)) * V.nextOddPart := by ring
      _ = 2 ^ V.startDepth * V.startOddPart +
            2 ^ V.startDepth * V.gapOddPart := hfull
      _ = 2 ^ V.startDepth * (V.startOddPart + V.gapOddPart) := by ring
  exact Nat.mul_left_cancel (Nat.pow_pos (by omega)) hscaled

/-- next-lower 枝の odd-part recurrence。 -/
theorem valuation_nextLower_oddPart_recurrence
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ)
    (h :
      (C.core.valuationData n).nextDepth <
        (C.core.valuationData n).startDepth) :
    (C.core.valuationData n).nextOddPart =
      2 ^ ((C.core.valuationData n).startDepth -
            (C.core.valuationData n).nextDepth) *
          (C.core.valuationData n).startOddPart +
        (C.core.valuationData n).gapOddPart := by
  let V := C.core.valuationData n
  have hV : V.nextDepth < V.startDepth := by simpa [V] using h
  have hgap : V.gapDepth = V.nextDepth :=
    V.gapDepth_eq_nextDepth_of_lt hV
  have hsplit :
      V.startDepth = V.nextDepth + (V.startDepth - V.nextDepth) :=
    (Nat.add_sub_of_le (Nat.le_of_lt hV)).symm
  have hfull := C.valuation_full_recurrence n
  change
    2 ^ V.nextDepth * V.nextOddPart =
      2 ^ V.startDepth * V.startOddPart +
        2 ^ V.gapDepth * V.gapOddPart at hfull
  rw [hgap, hsplit, pow_add] at hfull
  have hscaled :
      2 ^ V.nextDepth * V.nextOddPart =
        2 ^ V.nextDepth *
          (2 ^ (V.startDepth - V.nextDepth) * V.startOddPart +
            V.gapOddPart) := by
    calc
      2 ^ V.nextDepth * V.nextOddPart
          = (2 ^ V.nextDepth *
              2 ^ (V.startDepth - V.nextDepth)) * V.startOddPart +
              2 ^ V.nextDepth * V.gapOddPart := hfull
      _ = 2 ^ V.nextDepth *
          (2 ^ (V.startDepth - V.nextDepth) * V.startOddPart +
            V.gapOddPart) := by ring
  exact Nat.mul_left_cancel (Nat.pow_pos (by omega)) hscaled

/-- equal-cancellation 枝の odd-part recurrence。 -/
theorem valuation_equalCancellation_oddPart_recurrence
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ)
    (h :
      (C.core.valuationData n).startDepth =
        (C.core.valuationData n).nextDepth) :
    (C.core.valuationData n).nextOddPart =
      (C.core.valuationData n).startOddPart +
        2 ^ ((C.core.valuationData n).gapDepth -
              (C.core.valuationData n).startDepth) *
          (C.core.valuationData n).gapOddPart := by
  let V := C.core.valuationData n
  have hV : V.startDepth = V.nextDepth := by simpa [V] using h
  have hlt : V.startDepth < V.gapDepth :=
    V.startDepth_lt_gapDepth_of_eq hV
  have hsplit :
      V.gapDepth = V.startDepth + (V.gapDepth - V.startDepth) :=
    (Nat.add_sub_of_le (Nat.le_of_lt hlt)).symm
  have hfull := C.valuation_full_recurrence n
  change
    2 ^ V.nextDepth * V.nextOddPart =
      2 ^ V.startDepth * V.startOddPart +
        2 ^ V.gapDepth * V.gapOddPart at hfull
  rw [← hV, hsplit, pow_add] at hfull
  have hscaled :
      2 ^ V.startDepth * V.nextOddPart =
        2 ^ V.startDepth *
          (V.startOddPart +
            2 ^ (V.gapDepth - V.startDepth) * V.gapOddPart) := by
    calc
      2 ^ V.startDepth * V.nextOddPart
          = 2 ^ V.startDepth * V.startOddPart +
              (2 ^ V.startDepth *
                2 ^ (V.gapDepth - V.startDepth)) * V.gapOddPart := hfull
      _ = 2 ^ V.startDepth *
          (V.startOddPart +
            2 ^ (V.gapDepth - V.startDepth) * V.gapOddPart) := by ring
  exact Nat.mul_left_cancel (Nat.pow_pos (by omega)) hscaled

/-- first-crossing return gap の exact depth は length に指数的制約を与える。 -/
theorem firstCrossing_returnDepth_bound
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ)
    {D u : ℕ}
    (hD : TwoAdic.ExactFactor (C.firstCrossing n).returnGap D u) :
    3 * 2 ^ D < (C.firstCrossing n).length :=
  (C.firstCrossing n).three_mul_twoPow_returnDepth_lt_length hD

/-- adjacent valuation depth は chain 上で正確に接続する。 -/
theorem valuationDepth_coherent
    {O : OddOrbit} (C : CanonicalChain O) (n : ℕ) :
    (C.core.valuationData n).nextDepth =
      (C.core.valuationData (n + 1)).startDepth :=
  C.core.valuationDepth_coherent n

end CanonicalChain
end PositiveReturn
end AdjacentReturn
end Collatz
