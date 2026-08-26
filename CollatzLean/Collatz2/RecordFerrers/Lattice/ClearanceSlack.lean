import CollatzLean.Collatz2.RecordFerrers.Lattice.PrefixCoordinates

/-!
# Record–Ferrers RF-B3: 臨界境界までの余裕 = 整数制約の余裕

累積整数座標が critical roof の下にあるとき、
上限制約との差を自然数 `criticalSlack` として定義する。

universal FirstCrossing object を任意の contracting depth に実現した場合、
この整数の余裕が既存の signed `criticalDefectInt` と exact に一致することまで戻す。
-/

namespace Collatz2
namespace RecordFerrers
open Word
namespace PrefixCoordinates

/-- cut `i` における critical roof までの自然数の余裕。 -/
def criticalSlack
    {p : ℕ}
    (C : PrefixCoordinates p)
    (i : Fin p) : ℕ :=
  criticalExcess i.1 - C.cumulative i

end PrefixCoordinates

namespace CriticalSubshape

/-- critical subshape では「高さ + 余裕 = critical height excess」が exact に成り立つ。 -/
theorem cumulative_add_criticalSlack
    {p : ℕ}
    (S : CriticalSubshape p)
    (i : Fin p) :
    S.shape.toPrefixCoordinates.cumulative i +
        S.shape.toPrefixCoordinates.criticalSlack i =
      criticalExcess i.1 := by
  have hle : S.shape.column i ≤ criticalExcess i.1 := by
    simpa [criticalShape] using S.below i
  change
    S.shape.column i +
        (criticalExcess i.1 - S.shape.column i) =
      criticalExcess i.1
  omega

/-- 余裕が 0 であることは、その cut が critical roof に接触することと同値。 -/
theorem criticalSlack_eq_zero_iff_contact
    {p : ℕ}
    (S : CriticalSubshape p)
    (i : Fin p) :
    S.shape.toPrefixCoordinates.criticalSlack i = 0 ↔
      S.shape.column i = (criticalShape p).column i := by
  have hle : S.shape.column i ≤ criticalExcess i.1 := by
    simpa [criticalShape] using S.below i
  change
    criticalExcess i.1 - S.shape.column i = 0 ↔
      S.shape.column i = criticalExcess i.1
  omega

/--
整数座標の余裕は、任意の contracting terminal depth で実現したときの
既存 `criticalDefectInt` と exact に一致する。
-/
theorem criticalDefectInt_eq_criticalSlack
    {p H : ℕ}
    (S : CriticalSubshape p)
    (hp : 0 < p)
    (hContract : ContractingChord p H)
    {k : ℕ}
    (hk : k < p) :
    criticalDefectInt (S.toFiberPoint H hp hContract) k =
      (S.shape.toPrefixCoordinates.criticalSlack ⟨k, hk⟩ : ℤ) := by
  let x : FiberPoint p H := S.toFiberPoint H hp hContract
  let i : Fin p := ⟨k, hk⟩
  have hShape := S.toFiberPoint_toFerrersShape H hp hContract
  have hCol :=
    congrArg (fun T : FerrersShape p => T.column i) hShape
  have hExcess : x.excessAt k = S.shape.column i := by
    change x.toFerrersShape.column i = S.shape.column i
    exact hCol
  have hHeight := x.height_eq_index_add_excess (Nat.le_of_lt hk)
  have hCritBase := index_le_criticalHeight k
  have hCritHeight : criticalHeight k = k + criticalExcess k := by
    unfold criticalExcess
    omega
  have hBelow : S.shape.column i ≤ criticalExcess k := by
    simpa [criticalShape, i] using S.below i
  unfold criticalDefectInt PrefixCoordinates.criticalSlack
  change
    (criticalHeight k : ℤ) - (x.height k : ℤ) =
      ((criticalExcess k - S.shape.column i : ℕ) : ℤ)
  rw [hHeight, hExcess, hCritHeight]
  rw [Nat.cast_sub hBelow]
  push_cast
  ring

end CriticalSubshape

end RecordFerrers
end Collatz2
