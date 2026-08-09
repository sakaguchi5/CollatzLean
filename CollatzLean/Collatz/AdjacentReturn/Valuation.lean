import CollatzLean.Collatz.AdjacentReturn.Geometry
import CollatzLean.Collatz.TwoAdic.Valuation

/-!
# adjacent future-minimum valuation triangle

`A = v2(x+1)`, `C = v2(y+1)`, `D = v2(y-x)`を
選択関数ではなく明示Typeデータとして保持する。
future-minimum性はStateの公開APIから取得する。
-/

namespace Collatz
namespace AdjacentReturn
namespace State

/-- 一つのadjacent stateに対する三つの完全2進分解。 -/
structure ValuationData {O : OddOrbit} (R : State O) where
  startDepth : ℕ
  startOddPart : ℕ
  startFactor : TwoAdic.ExactFactor (R.startValue + 1) startDepth startOddPart
  nextDepth : ℕ
  nextOddPart : ℕ
  nextFactor : TwoAdic.ExactFactor (R.nextValue + 1) nextDepth nextOddPart
  gapDepth : ℕ
  gapOddPart : ℕ
  gapFactor : TwoAdic.ExactFactor R.valueGap gapDepth gapOddPart

/-- ValuationDataは常に存在する。値を選択してAPIへ固定はしない。 -/
theorem existsValuationData
    {O : OddOrbit} (R : State O) : Nonempty (ValuationData R) := by
  obtain ⟨A, u, hA⟩ := TwoAdic.exists_of_pos (R.startValue + 1) (by omega)
  obtain ⟨C, v, hC⟩ := TwoAdic.exists_of_pos (R.nextValue + 1) (by omega)
  obtain ⟨D, t, hD⟩ := TwoAdic.exists_of_pos R.valueGap R.valueGap_pos
  exact ⟨⟨A, u, hA, C, v, hC, D, t, hD⟩⟩

namespace ValuationData

/-- current future-minimumの`x+1` depthは2以上。 -/
theorem startDepth_two_le
    {O : OddOrbit} {R : State O} (V : ValuationData R) :
    2 ≤ V.startDepth := by
  exact R.startFutureMinimum.value_add_one_depth_two_le
    R.unbounded V.startFactor

/-- next future-minimumの`y+1` depthも2以上。 -/
theorem nextDepth_two_le
    {O : OddOrbit} {R : State O} (V : ValuationData R) :
    2 ≤ V.nextDepth := by
  exact R.nextFutureMinimum.value_add_one_depth_two_le
    R.unbounded V.nextFactor

/-- `A<C`なら`D=A`。 -/
theorem gapDepth_eq_startDepth_of_lt
    {O : OddOrbit} {R : State O} (V : ValuationData R)
    (hAC : V.startDepth < V.nextDepth) :
    V.gapDepth = V.startDepth := by
  have hXY : R.startValue + 1 < R.nextValue + 1 := by
    exact Nat.add_lt_add_right R.startValue_lt_nextValue 1
  have hD :
      TwoAdic.ExactFactor
        ((R.nextValue + 1) - (R.startValue + 1)) V.gapDepth V.gapOddPart := by
    have hgap : (R.nextValue + 1) - (R.startValue + 1) = R.valueGap := by
      rw [R.nextValue_eq_startValue_add_valueGap]
      omega
    rw [hgap]
    exact V.gapFactor
  exact TwoAdic.sub_depth_eq_left_of_lt
    V.startFactor V.nextFactor hD hXY hAC

/-- `C<A`なら`D=C`。 -/
theorem gapDepth_eq_nextDepth_of_lt
    {O : OddOrbit} {R : State O} (V : ValuationData R)
    (hCA : V.nextDepth < V.startDepth) :
    V.gapDepth = V.nextDepth := by
  have hXY : R.startValue + 1 < R.nextValue + 1 := by
    exact Nat.add_lt_add_right R.startValue_lt_nextValue 1
  have hD :
      TwoAdic.ExactFactor
        ((R.nextValue + 1) - (R.startValue + 1)) V.gapDepth V.gapOddPart := by
    have hgap : (R.nextValue + 1) - (R.startValue + 1) = R.valueGap := by
      rw [R.nextValue_eq_startValue_add_valueGap]
      omega
    rw [hgap]
    exact V.gapFactor
  exact TwoAdic.sub_depth_eq_right_of_lt
    V.startFactor V.nextFactor hD hXY hCA

/-- `A=C`なら`A<D`。 -/
theorem startDepth_lt_gapDepth_of_eq
    {O : OddOrbit} {R : State O} (V : ValuationData R)
    (hEq : V.startDepth = V.nextDepth) :
    V.startDepth < V.gapDepth := by
  have hXY : R.startValue + 1 < R.nextValue + 1 := by
    exact Nat.add_lt_add_right R.startValue_lt_nextValue 1
  have hNext :
      TwoAdic.ExactFactor (R.nextValue + 1) V.startDepth V.nextOddPart := by
    rw [hEq]
    exact V.nextFactor
  have hD :
      TwoAdic.ExactFactor
        ((R.nextValue + 1) - (R.startValue + 1)) V.gapDepth V.gapOddPart := by
    have hgap : (R.nextValue + 1) - (R.startValue + 1) = R.valueGap := by
      rw [R.nextValue_eq_startValue_add_valueGap]
      omega
    rw [hgap]
    exact V.gapFactor
  exact TwoAdic.depth_lt_sub_depth_of_eq V.startFactor hNext hD hXY

/-- adjacent値差のexact depthは常に2以上。 -/
theorem gapDepth_two_le
    {O : OddOrbit} {R : State O} (V : ValuationData R) :
    2 ≤ V.gapDepth := by
  rcases lt_trichotomy V.startDepth V.nextDepth with hAC | hEq | hCA
  · rw [V.gapDepth_eq_startDepth_of_lt hAC]
    exact V.startDepth_two_le
  · exact le_trans V.startDepth_two_le
      (Nat.le_of_lt (V.startDepth_lt_gapDepth_of_eq hEq))
  · rw [V.gapDepth_eq_nextDepth_of_lt hCA]
    exact V.nextDepth_two_le

end ValuationData
end State
end AdjacentReturn
end Collatz
