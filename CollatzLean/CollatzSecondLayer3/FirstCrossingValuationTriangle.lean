import CollatzLean.CollatzSecondLayer3.FirstCrossingReturnArithmetic
import CollatzLean.CollatzSecondLayer3.FirstCrossingHighConnector

/-!
# first-crossing returnの2進valuation triangle

actual positive dataだけを用いて

* `A = v2(start + 1)`
* `C = v2(crossingEnd + 1) = highOffset + 1`
* `D = v2(crossingEnd - start)`

の関係を完全2進分解`ExactTwoFactor`で記述する。

`A < C`なら`D=A`、`C < A`なら`D=C`、`A=C`なら`A<D`。
future-minimumでは`A≥2`なので、特に`D=1 ↔ highOffset=0`が従う。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- 正自然数の完全2進分解をデータとして保持する。 -/
structure ReturnExactTwoFactorData (n : ℕ) where
  exponent : ℕ
  oddPart : ℕ
  factorization : ExactTwoFactor n exponent oddPart

/-- 正自然数から完全2進分解データを選ぶ。 -/
noncomputable def returnExactTwoFactorData
    (n : ℕ) (hn : 0 < n) : ReturnExactTwoFactorData n := by
  classical
  have hData :
      Nonempty (ReturnExactTwoFactorData n) := by
    obtain ⟨e, u, h⟩ :=
      exists_exactTwoFactor_of_pos n hn
    exact ⟨⟨e, u, h⟩⟩
  exact Classical.choice hData

/--
二つの正数の2進depthが異なるとき、正差のdepthは小さい側にexactに一致する。
-/
theorem exactTwoFactor_sub_depth_eq_left_of_lt
    {X Y A C u v D t : ℕ}
    (hX : ExactTwoFactor X A u)
    (hY : ExactTwoFactor Y C v)
    (hD : ExactTwoFactor (Y - X) D t)
    (hXY : X < Y)
    (hAC : A < C) :
    D = A := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, C = A + (r + 1) := by
    exact ⟨C - A - 1, by omega⟩
  let V : ℕ := 2 ^ (r + 1) * v
  have hY' : Y = 2 ^ A * V := by
    dsimp [V]
    rw [hY.1, hr, pow_add]
    ring
  have hX' : X = 2 ^ A * u := hX.1
  have hpowPos : 0 < 2 ^ A := Nat.pow_pos (by omega)
  have huV : u < V := by
    have hmul : 2 ^ A * u < 2 ^ A * V := by
      simpa [hX', hY'] using hXY
    exact (Nat.mul_lt_mul_left hpowPos).mp hmul
  let q : ℕ := V - u
  have hdiff : Y - X = 2 ^ A * q := by
    dsimp [q]
    rw [hY', hX', Nat.mul_sub_left_distrib]
  have hqOdd : Odd q := by
    rcases hX.2 with ⟨ku, hku⟩
    let T : ℕ := 2 ^ r * v
    have hV : V = 2 * T := by
      dsimp [V, T]
      rw [pow_succ]
      ring
    have hkuT : ku < T := by
      rw [hku, hV] at huV
      omega
    refine ⟨T - ku - 1, ?_⟩
    dsimp [q]
    rw [hku, hV]
    omega
  have hCandidate : ExactTwoFactor (Y - X) A q :=
    ⟨hdiff, hqOdd⟩
  exact exactTwoFactor_exponent_unique hD hCandidate

/-- 右側depthが小さい場合は差depthも右側に一致する。 -/
theorem exactTwoFactor_sub_depth_eq_right_of_lt
    {X Y A C u v D t : ℕ}
    (hX : ExactTwoFactor X A u)
    (hY : ExactTwoFactor Y C v)
    (hD : ExactTwoFactor (Y - X) D t)
    (hXY : X < Y)
    (hCA : C < A) :
    D = C := by
  obtain ⟨r, hr⟩ : ∃ r : ℕ, A = C + (r + 1) := by
    exact ⟨A - C - 1, by omega⟩
  let U : ℕ := 2 ^ (r + 1) * u
  have hX' : X = 2 ^ C * U := by
    dsimp [U]
    rw [hX.1, hr, pow_add]
    ring
  have hY' : Y = 2 ^ C * v := hY.1
  have hpowPos : 0 < 2 ^ C := Nat.pow_pos (by omega)
  have hUv : U < v := by
    have hmul : 2 ^ C * U < 2 ^ C * v := by
      simpa [hX', hY'] using hXY
    exact (Nat.mul_lt_mul_left hpowPos).mp hmul
  let q : ℕ := v - U
  have hdiff : Y - X = 2 ^ C * q := by
    dsimp [q]
    rw [hY', hX', Nat.mul_sub_left_distrib]
  have hqOdd : Odd q := by
    rcases hY.2 with ⟨kv, hkv⟩
    let T : ℕ := 2 ^ r * u
    have hU : U = 2 * T := by
      dsimp [U, T]
      rw [pow_succ]
      ring
    have hTkv : T ≤ kv := by
      rw [hU, hkv] at hUv
      omega
    refine ⟨kv - T, ?_⟩
    dsimp [q]
    rw [hU, hkv]
    omega
  have hCandidate : ExactTwoFactor (Y - X) C q :=
    ⟨hdiff, hqOdd⟩
  exact exactTwoFactor_exponent_unique hD hCandidate

/--
両側のdepthが一致する場合、奇数部分同士の差が偶数なので
正差には少なくとももう1ビット残る。
-/
theorem exactTwoFactor_sub_depth_gt_of_eq
    {X Y A u v D t : ℕ}
    (hX : ExactTwoFactor X A u)
    (hY : ExactTwoFactor Y A v)
    (hD : ExactTwoFactor (Y - X) D t)
    (hXY : X < Y) :
    A < D := by
  have hpowPos : 0 < 2 ^ A := Nat.pow_pos (by omega)
  have huv : u < v := by
    have hmul : 2 ^ A * u < 2 ^ A * v := by
      simpa [hX.1, hY.1] using hXY
    exact (Nat.mul_lt_mul_left hpowPos).mp hmul
  rcases hX.2 with ⟨ku, hku⟩
  rcases hY.2 with ⟨kv, hkv⟩
  have hk : ku < kv := by
    rw [hku, hkv] at huv
    omega
  let q : ℕ := kv - ku
  have hdiffOddParts : v - u = 2 * q := by
    dsimp [q]
    rw [hku, hkv]
    omega
  have hdiff : Y - X = 2 ^ (A + 1) * q := by
    rw [hY.1, hX.1, ← Nat.mul_sub_left_distrib, hdiffOddParts, pow_succ]
    ring
  by_contra hnot
  have hDle : D ≤ A := Nat.le_of_not_gt hnot
  have hDlt : D < A + 1 := by omega
  have hpowEq : 2 ^ D * t = 2 ^ (A + 1) * q := by
    calc
      2 ^ D * t = Y - X := hD.1.symm
      _ = 2 ^ (A + 1) * q := hdiff
  obtain ⟨r, ht⟩ := oddPart_eq_twoPow_mul_of_lt hpowEq hDlt
  have htEven : Even t := by
    rw [ht]
    exact even_two_pow_succ_mul_nat r q
  exact odd_even_false_nat hD.2 htEven

/--
future-minimum値`x`では`x+1`が少なくとも4で割れる。
-/
theorem futureMinimum_plusOne_four_dvd
    (O : OddOrbit)
    (hU : O.Unbounded)
    {anchor : ℕ}
    (hmin : O.FutureMinimumAt anchor) :
    ∃ q : ℕ, O.value anchor + 1 = 4 * q := by
  have he : O.exponent anchor = 1 :=
    futureMinimum_exponent_eq_one_of_unbounded O hU hmin
  have hs :
      2 * O.value (anchor + 1) = 3 * O.value anchor + 1 := by
    simpa [he] using O.step anchor
  rcases O.value_odd anchor with ⟨a, ha⟩
  rcases O.value_odd (anchor + 1) with ⟨b, hb⟩
  rw [ha, hb] at hs
  obtain ⟨k, hEven | hOdd⟩ := a.even_or_odd'
  · rw [hEven] at hs
    omega
  · refine ⟨k + 1, ?_⟩
    rw [ha, hOdd]
    ring

/-- future-minimumの`value+1` exact depthは2以上。 -/
theorem futureMinimum_plusOne_exactDepth_two_le
    (O : OddOrbit)
    (hU : O.Unbounded)
    {anchor A u : ℕ}
    (hmin : O.FutureMinimumAt anchor)
    (hA : ExactTwoFactor (O.value anchor + 1) A u) :
    2 ≤ A := by
  obtain ⟨q, hq⟩ := futureMinimum_plusOne_four_dvd O hU hmin
  by_contra hnot
  have hcases : A = 0 ∨ A = 1 := by omega
  rcases hcases with rfl | rfl
  · rcases hA with ⟨hfac, hodd⟩
    simp only [pow_zero, one_mul] at hfac
    have huEq : u = 4 * q := by omega
    have huEven : Even u := by
      rw [huEq]
      exact ⟨2 * q, by ring⟩
    exact odd_even_false_nat hodd huEven
  · rcases hA with ⟨hfac, hodd⟩
    norm_num at hfac
    have huEven : Even u := by
      refine ⟨q, ?_⟩
      omega
    exact odd_even_false_nat hodd huEven

namespace FutureMinimumFirstCrossingHighEventData

/-- first-high dataからnegative shadowを介さずactual return正本へ忘却する。 -/
def toReturnData
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    FutureMinimumFirstCrossingReturnData O :=
  { unbounded := D.unbounded
    start := D.anchor
    length := D.crossingLength
    futureMinimum := D.futureMinimum
    crossing := D.crossing }

/-- first-crossing startの`value+1`完全2進分解。 -/
noncomputable def startPlusOneFactor
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    ReturnExactTwoFactorData (O.value D.anchor + 1) :=
  returnExactTwoFactorData
    (O.value D.anchor + 1)
    (by have := O.value_pos D.anchor; omega)

/-- start側`value+1`のexact depth。 -/
noncomputable def startPlusOneDepth
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) : ℕ :=
  D.startPlusOneFactor.exponent

/-- first-crossing startからendまでのordered difference。 -/
noncomputable def returnDifference
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    O.WindowDifferenceData D.anchor D.crossingLength := by
  have hlt : O.value D.anchor < O.value (D.anchor + D.crossingLength) :=
    firstCrossing_endpoint_gt_start D.unbounded D.futureMinimum D.crossing
  exact O.windowDifferenceData_of_lt hlt

/-- actual return gapのexact 2進depth。 -/
noncomputable def returnDepth
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) : ℕ :=
  D.returnDifference.depth

/-- return gapは`returnDepth`で完全2進分解される。 -/
theorem returnGap_exactFactor
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    ExactTwoFactor
      (firstCrossingReturnGap (O := O) D.anchor D.crossingLength)
      D.returnDepth
      D.returnDifference.oddPart := by
  constructor
  · unfold firstCrossingReturnGap returnDepth
    have hd := D.returnDifference.difference
    omega
  · exact D.returnDifference.oddPart_odd

/-- first-high dataのreturn depthもsharpに`3*2^D < p`。 -/
theorem three_mul_twoPow_returnDepth_lt_crossingLength
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    3 * 2 ^ D.returnDepth < D.crossingLength := by
  have huPos : 0 < D.returnDifference.oddPart := by
    rcases D.returnDifference.oddPart_odd with ⟨u, hu⟩
    omega
  have hpowLe :
      2 ^ D.returnDepth ≤
        2 ^ D.returnDepth * D.returnDifference.oddPart := by
    have hu : 1 ≤ D.returnDifference.oddPart := by omega
    simpa using Nat.mul_le_mul_left (2 ^ D.returnDepth) hu
  have hgap :
      3 * firstCrossingReturnGap
          (O := O) D.anchor D.crossingLength < D.crossingLength :=
    three_mul_firstCrossingReturnGap_lt_length
      D.futureMinimum D.crossing
  have hEq := D.returnGap_exactFactor.1
  have hthree := Nat.mul_le_mul_left 3 hpowLe
  rw [hEq] at hgap
  exact lt_of_le_of_lt hthree hgap

/-- start側depthは2以上。 -/
theorem startPlusOneDepth_two_le
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    2 ≤ D.startPlusOneDepth := by
  unfold startPlusOneDepth
  exact futureMinimum_plusOne_exactDepth_two_le
    O D.unbounded D.futureMinimum D.startPlusOneFactor.factorization

/-- crossing endpoint側のdepthはexactに`highOffset+1`。 -/
theorem crossingEndPlusOne_exactFactor
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    ∃ u : ℕ,
      ExactTwoFactor
        (O.value (D.anchor + D.crossingLength) + 1)
        (D.highOffset + 1) u := by
  simpa [FutureMinimumFirstCrossingHighEventData.crossingEndPosition] using
    D.crossingEnd_plusOne_exactFactor

/-- `A<C`枝ではreturn depthはstart側depthに一致。 -/
theorem returnDepth_eq_startDepth_of_lt_highDepth
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O)
    (hAC : D.startPlusOneDepth < D.highOffset + 1) :
    D.returnDepth = D.startPlusOneDepth := by
  obtain ⟨v, hv⟩ := D.crossingEndPlusOne_exactFactor
  have hDiffEq :
      (O.value (D.anchor + D.crossingLength) + 1) -
          (O.value D.anchor + 1) =
        firstCrossingReturnGap (O := O) D.anchor D.crossingLength := by
    unfold firstCrossingReturnGap
    omega
  have hReturn :
      ExactTwoFactor
        ((O.value (D.anchor + D.crossingLength) + 1) -
          (O.value D.anchor + 1))
        D.returnDepth
        D.returnDifference.oddPart := by
    rw [hDiffEq]
    exact D.returnGap_exactFactor
  apply exactTwoFactor_sub_depth_eq_left_of_lt
      D.startPlusOneFactor.factorization hv hReturn
  · have hlt := firstCrossing_endpoint_gt_start
        D.unbounded D.futureMinimum D.crossing
    omega
  · exact hAC

/-- `C<A`枝ではreturn depthはcrossing endpoint側depthに一致。 -/
theorem returnDepth_eq_highDepth_of_lt_startDepth
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O)
    (hCA : D.highOffset + 1 < D.startPlusOneDepth) :
    D.returnDepth = D.highOffset + 1 := by
  obtain ⟨v, hv⟩ := D.crossingEndPlusOne_exactFactor
  have hDiffEq :
      (O.value (D.anchor + D.crossingLength) + 1) -
          (O.value D.anchor + 1) =
        firstCrossingReturnGap (O := O) D.anchor D.crossingLength := by
    unfold firstCrossingReturnGap
    omega
  have hReturn :
      ExactTwoFactor
        ((O.value (D.anchor + D.crossingLength) + 1) -
          (O.value D.anchor + 1))
        D.returnDepth
        D.returnDifference.oddPart := by
    rw [hDiffEq]
    exact D.returnGap_exactFactor
  apply exactTwoFactor_sub_depth_eq_right_of_lt
      D.startPlusOneFactor.factorization hv hReturn
  · have hlt := firstCrossing_endpoint_gt_start
        D.unbounded D.futureMinimum D.crossing
    omega
  · exact hCA

/-- `A=C`枝ではreturn depthは共通depthよりさらに深い。 -/
theorem startDepth_lt_returnDepth_of_eq_highDepth
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O)
    (hEq : D.startPlusOneDepth = D.highOffset + 1) :
    D.startPlusOneDepth < D.returnDepth := by
  obtain ⟨v, hv⟩ := D.crossingEndPlusOne_exactFactor
  rw [← hEq] at hv
  have hDiffEq :
      (O.value (D.anchor + D.crossingLength) + 1) -
          (O.value D.anchor + 1) =
        firstCrossingReturnGap (O := O) D.anchor D.crossingLength := by
    unfold firstCrossingReturnGap
    omega
  have hReturn :
      ExactTwoFactor
        ((O.value (D.anchor + D.crossingLength) + 1) -
          (O.value D.anchor + 1))
        D.returnDepth
        D.returnDifference.oddPart := by
    rw [hDiffEq]
    exact D.returnGap_exactFactor
  have hlt := firstCrossing_endpoint_gt_start
    D.unbounded D.futureMinimum D.crossing
  apply exactTwoFactor_sub_depth_gt_of_eq
    D.startPlusOneFactor.factorization hv hReturn
  omega

/-- return depthが1ならfirst-crossing endpoint自身がhigh event。 -/
theorem highOffset_eq_zero_of_returnDepth_eq_one
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O)
    (hDepth : D.returnDepth = 1) :
    D.highOffset = 0 := by
  rcases lt_trichotomy D.startPlusOneDepth (D.highOffset + 1) with hAC | hEq | hCA
  · have h := D.returnDepth_eq_startDepth_of_lt_highDepth hAC
    have hTwo := D.startPlusOneDepth_two_le
    omega
  · have h := D.startDepth_lt_returnDepth_of_eq_highDepth hEq
    have hTwo := D.startPlusOneDepth_two_le
    omega
  · have h := D.returnDepth_eq_highDepth_of_lt_startDepth hCA
    omega

/-- first-crossing endpoint自身がhigh eventならreturn depthはexactに1。 -/
theorem returnDepth_eq_one_of_highOffset_eq_zero
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O)
    (hOffset : D.highOffset = 0) :
    D.returnDepth = 1 := by
  have hC : D.highOffset + 1 < D.startPlusOneDepth := by
    rw [hOffset]
    have hTwo := D.startPlusOneDepth_two_le
    omega
  simpa [hOffset] using D.returnDepth_eq_highDepth_of_lt_startDepth hC

/-- return depth 1と`highOffset=0`は同値。 -/
theorem returnDepth_eq_one_iff_highOffset_eq_zero
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    D.returnDepth = 1 ↔ D.highOffset = 0 := by
  constructor
  · exact D.highOffset_eq_zero_of_returnDepth_eq_one
  · exact D.returnDepth_eq_one_of_highOffset_eq_zero

/--
`D=1`枝ではhigh event直後もfuture-minimum以上なので、
開始値はreturn gapの3倍+1以下まで線形に落ちる。
-/
theorem startValue_le_three_mul_returnGap_add_one_of_returnDepth_one
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O)
    (hDepth : D.returnDepth = 1) :
    O.value D.anchor ≤
      3 * firstCrossingReturnGap (O := O) D.anchor D.crossingLength + 1 := by
  have hOffset : D.highOffset = 0 :=
    D.highOffset_eq_zero_of_returnDepth_eq_one hDepth
  have hHigh : HighExponentAt O (D.anchor + D.crossingLength) := by
    simpa [hOffset] using D.high
  have heTwo : 2 ≤ O.exponent (D.anchor + D.crossingLength) := by
    unfold HighExponentAt at hHigh
    omega
  have hstep := O.step (D.anchor + D.crossingLength)
  have hminNext :
      O.value D.anchor ≤
        O.value (D.anchor + D.crossingLength + 1) :=
    D.futureMinimum _ (by omega)
  let x := O.value D.anchor
  let z := O.value (D.anchor + D.crossingLength)
  let d := firstCrossingReturnGap (O := O) D.anchor D.crossingLength
  let y := O.value (D.anchor + D.crossingLength + 1)
  have hz : z = x + d := by
    dsimp [d, firstCrossingReturnGap, x, z]
    have hlt := firstCrossing_endpoint_gt_start D.unbounded D.futureMinimum D.crossing
    omega
  have hpow : 4 ≤ 2 ^ O.exponent (D.anchor + D.crossingLength) := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) heTwo
  have h4xy : 4 * x ≤ 3 * z + 1 := by
    calc
      4 * x ≤ 4 * y := Nat.mul_le_mul_left 4 hminNext
      _ ≤ 2 ^ O.exponent (D.anchor + D.crossingLength) * y :=
        Nat.mul_le_mul_right y hpow
      _ = 3 * z + 1 := by simpa [x, z, y, Nat.add_assoc] using hstep
  rw [hz] at h4xy
  omega

end FutureMinimumFirstCrossingHighEventData

end CollatzSecondLayer3
