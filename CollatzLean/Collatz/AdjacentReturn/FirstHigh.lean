import CollatzLean.Collatz.AdjacentReturn.FirstCrossingArithmetic
import CollatzLean.Collatz.OddOrbit.HighExponent
import CollatzLean.Collatz.OddOrbit.FutureMinimumArithmetic
import CollatzLean.Collatz.TwoAdic.Valuation

/-!
# first crossing直後の最初のhigh event

旧high-event towerは戻さず、一つの`FirstCrossingData`に必要な局所情報だけを保持する。

* `offset` : crossing endpointから最初のhigh eventまでの距離
* `beforeHigh_one` : それ以前の指数はすべて1
* `high` : endpoint + offsetはhigh event

return gapのexact depthを`D`とすると
`D = 1 ↔ offset = 0`。
従って`D=1`ではcrossing endpoint自身がhigh eventとなり、
`startValue ≤ 3 * returnGap + 1`を得る。
-/

namespace Collatz
namespace AdjacentReturn

/-- first crossing終点以後の最初のhigh event。 -/
structure FirstHighData
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) where
  offset : ℕ
  beforeHigh_one : ∀ k : ℕ, k < offset →
    O.exponent (R.startIndex + F.length + k) = 1
  high : O.HighExponentAt (R.startIndex + F.length + offset)

namespace FirstHighData

/-- crossing endpoint位置。 -/
def crossingEndIndex
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (_H : FirstHighData F) : ℕ :=
  R.startIndex + F.length

/-- 最初のhigh event位置。 -/
def highIndex
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (H : FirstHighData F) : ℕ :=
  H.crossingEndIndex + H.offset

/-- crossing endpointの`value+1` depthはexactに`offset+1`。 -/
theorem endpointValue_add_one_exactFactor
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (H : FirstHighData F) :
    ∃ u : ℕ,
      TwoAdic.ExactFactor (F.endpointValue + 1) (H.offset + 1) u := by
  have h := O.value_add_one_exactFactor_of_one_run_to_high
    (start := R.startIndex + F.length)
    (L := H.offset)
    (by
      intro k hk
      simpa [Nat.add_assoc] using H.beforeHigh_one k hk)
    (by
      simpa [Nat.add_assoc] using H.high)
  simpa [FirstCrossingData.endpointValue] using h

/-- `(+1)`した両端の差は元のreturn gap。 -/
theorem addOneDifference_eq_returnGap
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (_H : FirstHighData F) :
    (F.endpointValue + 1) - (R.startValue + 1) = F.returnGap := by
  unfold FirstCrossingData.returnGap
  have hlt := F.start_lt_endpoint
  omega

/-- return gapのdepthが1なら最初のhigh eventはcrossing endpoint自身。 -/
theorem highOffset_eq_zero_of_returnDepth_eq_one
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (H : FirstHighData F)
    {u : ℕ}
    (hD : TwoAdic.ExactFactor F.returnGap 1 u) :
    H.offset = 0 := by
  obtain ⟨A, a, hA⟩ :=
    TwoAdic.exists_of_pos (R.startValue + 1) (by
      have := O.value_pos R.startIndex
      unfold State.startValue
      omega)
  have hA2 : 2 ≤ A := by
    exact R.startFutureMinimum.value_add_one_depth_two_le
      R.unbounded (by simpa [State.startValue] using hA)
  obtain ⟨v, hC⟩ :=
    H.endpointValue_add_one_exactFactor
  have hDiff :
      TwoAdic.ExactFactor
        ((F.endpointValue + 1) - (R.startValue + 1)) 1 u := by
    rw [H.addOneDifference_eq_returnGap]
    exact hD
  have huPos : 0 < u := by
    rcases hD.2 with ⟨k, hk⟩
    omega
  have hGapPos : 0 < F.returnGap := by
    have hFactor := hD.1
    change F.returnGap = 2 ^ 1 * u at hFactor
    rw [hFactor]
    omega
  have hEndpointGt :
      R.startValue < F.endpointValue := by
    have hle := F.start_le_endpoint
    unfold FirstCrossingData.returnGap at hGapPos
    omega
  have hXY :
      R.startValue + 1 < F.endpointValue + 1 := by
    omega
  rcases lt_trichotomy A (H.offset + 1) with hAC | hEq | hCA
  · have hDepth :=
      TwoAdic.sub_depth_eq_left_of_lt hA hC hDiff hXY hAC
    omega
  · have hC' :
        TwoAdic.ExactFactor (F.endpointValue + 1) A v := by
      simpa [← hEq] using hC
    have hDepth :=
      TwoAdic.depth_lt_sub_depth_of_eq hA hC' hDiff hXY
    omega
  · have hDepth :=
      TwoAdic.sub_depth_eq_right_of_lt hA hC hDiff hXY hCA
    omega

/-- crossing endpoint自身がhigh eventならreturn gapのdepthはexactに1。 -/
theorem exists_returnDepth_one_of_highOffset_eq_zero
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (H : FirstHighData F)
    (hOffset : H.offset = 0) :
    ∃ u : ℕ, TwoAdic.ExactFactor F.returnGap 1 u := by
  obtain ⟨A, a, hA⟩ :=
    TwoAdic.exists_of_pos (R.startValue + 1) (by
      have := O.value_pos R.startIndex
      unfold State.startValue
      omega)
  have hA2 : 2 ≤ A := by
    exact R.startFutureMinimum.value_add_one_depth_two_le
      R.unbounded (by simpa [State.startValue] using hA)
  obtain ⟨v, hC0⟩ :=
    H.endpointValue_add_one_exactFactor
  have hC :
      TwoAdic.ExactFactor (F.endpointValue + 1) 1 v := by
    simpa [hOffset] using hC0
  obtain ⟨D, u, hD⟩ :=
    TwoAdic.exists_of_pos F.returnGap F.returnGap_pos
  have hDiff :
      TwoAdic.ExactFactor
        ((F.endpointValue + 1) - (R.startValue + 1)) D u := by
    rw [H.addOneDifference_eq_returnGap]
    exact hD
  have hEndpoint :
      R.startValue < F.endpointValue := by
    have hgap := F.returnGap_pos
    unfold FirstCrossingData.returnGap at hgap
    omega
  have hXY :
      R.startValue + 1 < F.endpointValue + 1 :=
    Nat.add_lt_add_right hEndpoint 1
  have hDepth : D = 1 :=
    TwoAdic.sub_depth_eq_right_of_lt
      hA hC hDiff hXY (by omega)
  refine ⟨u, ?_⟩
  simpa [hDepth] using hD

/-- arbitraryなexact return depthに対して`D=1 ↔ highOffset=0`。 -/
theorem returnDepth_eq_one_iff_highOffset_eq_zero
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (H : FirstHighData F)
    {D u : ℕ}
    (hD : TwoAdic.ExactFactor F.returnGap D u) :
    D = 1 ↔ H.offset = 0 := by
  constructor
  · intro hDepth
    subst D
    exact H.highOffset_eq_zero_of_returnDepth_eq_one hD
  · intro hOffset
    obtain ⟨v, hOne⟩ := H.exists_returnDepth_one_of_highOffset_eq_zero hOffset
    exact TwoAdic.exponent_unique hD hOne

/--
`D=1`ではcrossing endpoint自身がhigh eventなので、
future-minimum性と次stepを合わせて`startValue ≤ 3*d+1`。
-/
theorem startValue_le_three_mul_returnGap_add_one_of_returnDepth_one
    {O : OddOrbit} {R : State O} {F : FirstCrossingData R}
    (H : FirstHighData F)
    {u : ℕ}
    (hD : TwoAdic.ExactFactor F.returnGap 1 u) :
    R.startValue ≤ 3 * F.returnGap + 1 := by
  have hOffset : H.offset = 0 :=
    H.highOffset_eq_zero_of_returnDepth_eq_one hD
  have hHigh : O.HighExponentAt (R.startIndex + F.length) := by
    simpa [hOffset] using H.high
  have heTwo : 2 ≤ O.exponent (R.startIndex + F.length) := by
    unfold OddOrbit.HighExponentAt at hHigh
    omega
  have hstep := O.step (R.startIndex + F.length)
  have hminNext :
      R.startValue ≤ O.value (R.startIndex + F.length + 1) := by
    unfold State.startValue
    exact R.startFutureMinimum _ (by
      have hp := F.length_pos
      omega)
  let x := R.startValue
  let z := F.endpointValue
  let d := F.returnGap
  let y := O.value (R.startIndex + F.length + 1)
  have hz : z = x + d := by
    simpa [x, z, d] using F.endpointValue_eq_startValue_add_returnGap
  have hpow : 4 ≤ 2 ^ O.exponent (R.startIndex + F.length) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) heTwo
  have h4xy : 4 * x ≤ 3 * z + 1 := by
    calc
      4 * x ≤ 4 * y := by
        exact Nat.mul_le_mul_left 4 (by simpa [x, y] using hminNext)
      _ ≤ 2 ^ O.exponent (R.startIndex + F.length) * y :=
        Nat.mul_le_mul_right y hpow
      _ = 3 * z + 1 := by
        simpa [z, y, FirstCrossingData.endpointValue, Nat.add_assoc] using hstep
  rw [hz] at h4xy
  omega

end FirstHighData

namespace FirstCrossingData

/-- first crossing終点以後にはhigh eventへのoffsetが存在する。 -/
private theorem existsHighOffset
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    ∃ L : ℕ, O.HighExponentAt (R.startIndex + F.length + L) := by
  obtain ⟨n, hn, hhigh⟩ :=
    O.exists_highExponent_at_or_after (R.startIndex + F.length)
  let L := n - (R.startIndex + F.length)
  have hindex : R.startIndex + F.length + L = n := by
    dsimp [L]
    omega
  refine ⟨L, ?_⟩
  rw [hindex]
  exact hhigh

/--
first crossingから、その後最初のhigh eventを選ぶ。
無限軌道から有限位置を選ぶため、このadapterだけはnoncomputable。
-/
noncomputable def firstHigh
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    FirstHighData F := by
  classical
  have hExists := F.existsHighOffset
  let L := Nat.find hExists
  have hHigh : O.HighExponentAt (R.startIndex + F.length + L) := by
    dsimp [L]
    exact Nat.find_spec hExists
  refine {
    offset := L
    beforeHigh_one := ?_
    high := hHigh
  }
  intro k hk
  have hnotHigh : ¬ O.HighExponentAt (R.startIndex + F.length + k) := by
    intro hkHigh
    have hle : L ≤ k := by
      dsimp [L]
      exact Nat.find_min' hExists hkHigh
    omega
  have hpos := O.exponent_pos (R.startIndex + F.length + k)
  unfold OddOrbit.HighExponentAt at hnotHigh
  omega

end FirstCrossingData
end AdjacentReturn
end Collatz
