import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.ReplayProfile
import Mathlib.Data.Fintype.Card

/-!
# positive return の first overshoot

first-crossing endpoint を `T` とする。
return gap が `T-S = 2*n` なら、future-minimum 性と非有界軌道の単射性により、
開始後 `n` step 以内に一度は `T` 以上へ到達しなければならない。

その最初の cut を `firstOvershootCut` とする。
`3 * returnGap < length` と合わせると `6 * firstOvershootCut < length`。
さらに直前は `T` 未満、cut は `T` 以上なので、その一歩の exponent は必ず1になる。

これは旧 prepend-one `j = 0` を、positive return 内部の自然な sign-change cut から
再抽出するための幾何層である。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn
namespace FirstCrossingData

/-- cut `k` で first-crossing endpoint 以上へ到達している。 -/
def IsEndpointOvershoot
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) (k : ℕ) : Prop :=
  0 < k ∧ F.endpointValue ≤ boundaryValue F k

/-- endpoint 自身が overshoot witness なので、overshoot cut は必ず存在する。 -/
theorem exists_endpointOvershoot
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    ∃ k : ℕ, IsEndpointOvershoot F k := by
  refine ⟨F.length, F.length_pos, ?_⟩
  exact le_rfl

/-- endpoint 以上へ初めて到達する cut。 -/
noncomputable def firstOvershootCut
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) : ℕ := by
  classical
  exact Nat.find (exists_endpointOvershoot F)

/-- first overshoot cut の defining property。 -/
theorem firstOvershootCut_spec
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    IsEndpointOvershoot F (firstOvershootCut F) := by
  classical
  exact Nat.find_spec (exists_endpointOvershoot F)

/-- first overshoot cut は正。 -/
theorem firstOvershootCut_pos
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    0 < firstOvershootCut F :=
  (firstOvershootCut_spec F).1

/-- first overshoot より前の boundary はすべて endpoint 未満。 -/
theorem boundaryValue_lt_endpoint_of_lt_firstOvershoot
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) {k : ℕ}
    (hk : k < firstOvershootCut F) :
    boundaryValue F k < F.endpointValue := by
  by_cases hk0 : k = 0
  · subst k
    simpa [boundaryValue, State.startValue] using F.start_lt_endpoint
  · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
    by_contra hnot
    have hge : F.endpointValue ≤ boundaryValue F k :=
      Nat.le_of_not_gt hnot
    have hmin : firstOvershootCut F ≤ k := by
      dsimp [firstOvershootCut]
      classical
      exact Nat.find_min' (exists_endpointOvershoot F) ⟨hkPos, hge⟩
    omega

/--
return gap `2*n` の中には odd 値が `n-1` 個しかないため、
非有界軌道は最初の `n` step をすべて endpoint 未満にはできない。
-/
theorem exists_endpointOvershoot_le_of_returnGap_eq_two_mul
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) {n : ℕ}
    (hgap : F.returnGap = 2 * n) :
    ∃ k : ℕ,
      0 < k ∧ k ≤ n ∧ F.endpointValue ≤ boundaryValue F k := by
  classical
  have hnTwo : 2 ≤ n := by
    have hfour := F.four_le_returnGap
    rw [hgap] at hfour
    omega
  by_contra hnone
  have hbelow :
      ∀ k : ℕ, 0 < k → k ≤ n →
        boundaryValue F k < F.endpointValue := by
    intro k hkPos hkLe
    by_contra hnot
    have hge : F.endpointValue ≤ boundaryValue F k :=
      Nat.le_of_not_gt hnot
    exact hnone ⟨k, hkPos, hkLe, hge⟩
  obtain ⟨a, haRaw⟩ := O.value_odd R.startIndex
  have ha : O.value R.startIndex = 2 * a + 1 := by
    simpa [two_mul] using haRaw
  let b : Fin n → ℕ := fun i =>
    Classical.choose
      (O.value_odd (R.startIndex + (i.1 + 1)))
  have hb :
      ∀ i : Fin n,
        O.value (R.startIndex + (i.1 + 1)) = 2 * b i + 1 := by
    intro i
    dsimp [b]
    simpa [two_mul] using
      (Classical.choose_spec
        (O.value_odd (R.startIndex + (i.1 + 1))))
  have hend : F.endpointValue = R.startValue + 2 * n := by
    calc
      F.endpointValue = R.startValue + F.returnGap :=
        F.endpointValue_eq_startValue_add_returnGap
      _ = R.startValue + 2 * n := by rw [hgap]
  have hbounds :
      ∀ i : Fin n, a < b i ∧ b i < a + n := by
    intro i
    let k : ℕ := i.1 + 1
    have hkPos : 0 < k := by
      dsimp [k]
      omega
    have hkLe : k ≤ n := by
      dsimp [k]
      omega
    have hstartLe :
        R.startValue ≤ boundaryValue F k := by
      have h := R.startFutureMinimum.le_segment_end k
      simpa [State.startValue, boundaryValue] using h
    have hstartNe :
        R.startValue ≠ boundaryValue F k := by
      unfold State.startValue boundaryValue
      exact O.value_ne_of_lt_of_unbounded R.unbounded (by
        dsimp [k]
        omega)
    have hstartLt :
        R.startValue < boundaryValue F k := by
      omega
    have hendLt : boundaryValue F k < F.endpointValue :=
      hbelow k hkPos hkLe
    have hlowOdd :
        O.value R.startIndex <
          O.value (R.startIndex + (i.1 + 1)) := by
      simpa [k, State.startValue, boundaryValue] using hstartLt
    have huppOdd :
        O.value (R.startIndex + (i.1 + 1)) <
          O.value R.startIndex + 2 * n := by
      calc
        O.value (R.startIndex + (i.1 + 1))
            = boundaryValue F k := by
                simp [k, boundaryValue]
        _ < F.endpointValue := hendLt
        _ = R.startValue + 2 * n := hend
        _ = O.value R.startIndex + 2 * n := by rfl
    rw [ha, hb i] at hlowOdd huppOdd
    constructor <;> omega
  let f : Fin n → Fin (n - 1) := fun i =>
    ⟨b i - a - 1, by
      have h := hbounds i
      omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hi := hbounds i
    have hj := hbounds j
    have hval : b i = b j := by
      have hfin := congrArg Fin.val hij
      dsimp [f] at hfin
      omega
    have horbit :
        O.value (R.startIndex + (i.1 + 1)) =
          O.value (R.startIndex + (j.1 + 1)) := by
      rw [hb i, hb j, hval]
    have hindex :=
      (O.value_injective_of_unbounded R.unbounded) horbit
    apply Fin.ext
    omega
  have hcard :
      Fintype.card (Fin n) ≤ Fintype.card (Fin (n - 1)) :=
    Fintype.card_le_of_injective f hf
  have hcontra : n ≤ n - 1 := by
    simpa using hcard
  omega

/-- first overshoot cut は half return gap 以下。 -/
theorem firstOvershootCut_le_of_returnGap_eq_two_mul
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) {n : ℕ}
    (hgap : F.returnGap = 2 * n) :
    firstOvershootCut F ≤ n := by
  obtain ⟨k, hkPos, hkLe, hkOver⟩ :=
    exists_endpointOvershoot_le_of_returnGap_eq_two_mul F hgap
  have hmin : firstOvershootCut F ≤ k := by
    dsimp [firstOvershootCut]
    classical
    exact Nat.find_min'
      (exists_endpointOvershoot F)
      ⟨hkPos, hkOver⟩
  exact le_trans hmin hkLe

/-- first overshoot は first-crossing 長の最初の 1/6 より前にある。 -/
theorem six_mul_firstOvershootCut_lt_length
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    6 * firstOvershootCut F < F.length := by
  obtain ⟨n, hEven⟩ := F.returnGap_even
  have hgap : F.returnGap = 2 * n := by
    omega
  have hcut :=
    firstOvershootCut_le_of_returnGap_eq_two_mul F hgap
  have hsharp := F.three_mul_returnGap_lt_length
  rw [hgap] at hsharp
  omega

/-- first overshoot は terminal より真に前。 -/
theorem firstOvershootCut_lt_length
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    firstOvershootCut F < F.length := by
  have h := six_mul_firstOvershootCut_lt_length F
  have hpos := firstOvershootCut_pos F
  omega

/-- first overshoot の直前 cut。 -/
noncomputable def firstOvershootPred
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) : ℕ :=
  firstOvershootCut F - 1

/-- first overshoot は predecessor の一歩後。 -/
theorem firstOvershootCut_eq_pred_add_one
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    firstOvershootCut F = firstOvershootPred F + 1 := by
  unfold firstOvershootPred
  have hpos := firstOvershootCut_pos F
  omega

/-- predecessor boundary は endpoint 未満。 -/
theorem firstOvershootPred_boundary_lt_endpoint
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    boundaryValue F (firstOvershootPred F) < F.endpointValue := by
  apply boundaryValue_lt_endpoint_of_lt_firstOvershoot F
  rw [firstOvershootCut_eq_pred_add_one F]
  omega

/-- first overshoot boundary は endpoint 以上。 -/
theorem endpoint_le_firstOvershoot_boundary
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    F.endpointValue ≤ boundaryValue F (firstOvershootCut F) :=
  (firstOvershootCut_spec F).2

/--
正の barrier `X` を下側から上へ越える odd-only 一歩の exponent は1。
-/
private theorem exponent_eq_one_of_step_crosses_barrier
    {X x y e : ℕ}
    (hX : 0 < X)
    (hx : x < X)
    (hy : X ≤ y)
    (he : 0 < e)
    (hstep : 2 ^ e * y = 3 * x + 1) :
    e = 1 := by
  by_contra hne
  have heTwo : 2 ≤ e := by omega
  have hpow : 4 ≤ 2 ^ e := by
    have h :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) heTwo
    norm_num at h
    exact h
  have hleft : 4 * X ≤ 2 ^ e * y := by
    calc
      4 * X ≤ 4 * y := Nat.mul_le_mul_left 4 hy
      _ ≤ 2 ^ e * y := Nat.mul_le_mul_right y hpow
  rw [hstep] at hleft
  omega

/-- first overshoot を起こす一歩の exponent は必ず1。 -/
theorem firstOvershootPred_exponent_eq_one
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    O.exponent (R.startIndex + firstOvershootPred F) = 1 := by
  let k := firstOvershootPred F
  have hcut : firstOvershootCut F = k + 1 := by
    simpa [k] using firstOvershootCut_eq_pred_add_one F
  have hX : 0 < F.endpointValue := by
    unfold FirstCrossingData.endpointValue
    exact O.value_pos _
  have hx : boundaryValue F k < F.endpointValue := by
    simpa [k] using firstOvershootPred_boundary_lt_endpoint F
  have hy :
      F.endpointValue ≤ boundaryValue F (k + 1) := by
    rw [← hcut]
    exact endpoint_le_firstOvershoot_boundary F
  have he : 0 < O.exponent (R.startIndex + k) :=
    O.exponent_pos _
  have hstep :
      2 ^ O.exponent (R.startIndex + k) * boundaryValue F (k + 1) =
        3 * boundaryValue F k + 1 := by
    simpa [boundaryValue, Nat.add_assoc] using
      O.step (R.startIndex + k)
  exact exponent_eq_one_of_step_crosses_barrier hX hx hy he hstep

end FirstCrossingData
end PositiveReturn
end AdjacentReturn
end Collatz
