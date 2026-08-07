import CollatzLean.CollatzSecondLayer3.FutureMinimumHighEvent
import CollatzLean.CollatzSecondLayer3.PolynomialCrossing
import CollatzLean.CollatzWindowCore.Normalization

/-!
# first-crossingから最初のhigh-exponent eventまでの短いconnector

future-minimumからのfirst-crossing終点以後で、最初に指数が1を越える位置を取る。
その直前までは指数がすべて1なのでconnector wordは`[1,...,1]`である。

指数1の一段では`x+1`の2進depthがexactに1だけ減る。
最初のhigh-exponent位置では`x+1`の2進depthがexactに1であるため、
connector長を`L`、first-crossing終点を`z`とすると

`2^(L+1) ∣ z+1`

が従う。従って`2^(L+1) ≤ z+1`。
既存のBaker型first-crossing endpoint多項式評価と合わせることで、
`L = O(log p)`を整数不等式として得る。

また指数1 connectorのexact式から、最初のhigh-event値は`(z+1)^2`以下となり、
first-crossing長`p`に対する一様多項式上界も得られる。
-/

namespace CollatzSecondLayer3

open CollatzCore
open CollatzExternal
open CollatzFirstLayer
open CollatzFirstLayer.ExpWord

/-- high-exponent位置では`value+1`の完全2進depthはexactに1。 -/
theorem highExponent_plusOne_exact_one
    (O : OddOrbit)
    {i : ℕ}
    (hhigh : HighExponentAt O i) :
    ∃ u : ℕ, ExactTwoFactor (O.value i + 1) 1 u := by
  rcases O.value_odd i with ⟨a, ha⟩
  obtain ⟨k, haEven | haOdd⟩ := a.even_or_odd'
  · refine ⟨2 * k + 1, ?_⟩
    constructor
    · rw [ha, haEven]
      norm_num
      all_goals ring
    · exact ⟨k, by ring⟩
  · have hOne :
        ExactTwoFactor (3 * O.value i + 1) 1 (6 * k + 5) := by
      constructor
      · rw [ha, haOdd]
        norm_num
        all_goals ring
      · exact ⟨3 * k + 2, by ring⟩
    have hActual :
        ExactTwoFactor
          (3 * O.value i + 1)
          (O.exponent i)
          (O.value (i + 1)) :=
      ⟨(O.step i).symm, O.value_odd (i + 1)⟩
    have heq := exactTwoFactor_exponent_unique hActual hOne
    unfold HighExponentAt at hhigh
    omega

/--
指数1の一段を逆向きに見ると、`value+1`の2進depthはexactに1増える。
-/
theorem plusOne_exactFactor_prev_of_exponent_one
    (O : OddOrbit)
    {i d u : ℕ}
    (hexp : O.exponent i = 1)
    (hNext : ExactTwoFactor (O.value (i + 1) + 1) d u) :
    ∃ v : ℕ, ExactTwoFactor (O.value i + 1) (d + 1) v := by
  obtain ⟨a, v, hCurrent⟩ :=
    exists_exactTwoFactor_of_pos
      (O.value i + 1) (by have := O.value_pos i; omega)
  have hThreeCurrent :
      ExactTwoFactor (3 * (O.value i + 1)) a (3 * v) := by
    constructor
    · rw [hCurrent.1]
      ring
    · exact (show Odd (3 : ℕ) by decide).mul hCurrent.2
  have hstep :
      2 * O.value (i + 1) = 3 * O.value i + 1 := by
    simpa [hexp] using O.step i
  have hScaledNext :
      ExactTwoFactor
        (3 * (O.value i + 1)) (d + 1) u := by
    constructor
    · calc
        3 * (O.value i + 1)
            = (3 * O.value i + 1) + 2 := by
                ring
        _ = 2 * O.value (i + 1) + 2 := by
              rw [← hstep]
        _ = 2 * (O.value (i + 1) + 1) := by
              ring
        _ = 2 * (2 ^ d * u) := by
              rw [hNext.1]
        _ = 2 ^ (d + 1) * u := by
              rw [pow_succ]
              ring
    · exact hNext.2
  have ha : a = d + 1 :=
    exactTwoFactor_exponent_unique hThreeCurrent hScaledNext
  refine ⟨v, ?_⟩
  simpa [ha] using hCurrent

/--
長さ`L`の指数1区間の直後がhigh-exponentなら、
区間開始値`+1`の2進depthはexactに`L+1`。
-/
theorem plusOne_exactFactor_of_one_run_to_high
    (O : OddOrbit) :
    ∀ {start L : ℕ},
      (∀ k : ℕ, k < L → O.exponent (start + k) = 1) →
      HighExponentAt O (start + L) →
      ∃ u : ℕ, ExactTwoFactor (O.value start + 1) (L + 1) u := by
  intro start L
  induction L generalizing start with
  | zero =>
      intro _ hhigh
      simpa using highExponent_plusOne_exact_one O hhigh
  | succ L ih =>
      intro hones hhigh
      have hfirst : O.exponent start = 1 := by
        simpa using hones 0 (by omega)
      have htail : ∀ k : ℕ, k < L →
          O.exponent (start + 1 + k) = 1 := by
        intro k hk
        have h := hones (k + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hhighTail : HighExponentAt O (start + 1 + L) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhigh
      obtain ⟨u, hu⟩ := ih (start := start + 1) htail hhighTail
      obtain ⟨v, hv⟩ :=
        plusOne_exactFactor_prev_of_exponent_one O hfirst hu
      refine ⟨v, ?_⟩
      simpa [Nat.add_assoc] using hv

/-- 指数1だけの有限runでは`x+1`がexactに`3/2`倍される。 -/
theorem oneRun_scaled_addOne
    (O : OddOrbit) :
    ∀ {start L : ℕ},
      (∀ k : ℕ, k < L → O.exponent (start + k) = 1) →
      2 ^ L * (O.value (start + L) + 1) =
        3 ^ L * (O.value start + 1) := by
  intro start L
  induction L generalizing start with
  | zero =>
      intro _
      simp
  | succ L ih =>
      intro hones
      have hfirst : O.exponent start = 1 := by
        simpa using hones 0 (by omega)
      have htail : ∀ k : ℕ, k < L →
          O.exponent (start + 1 + k) = 1 := by
        intro k hk
        have h := hones (k + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hstep :
          2 * (O.value (start + 1) + 1) =
            3 * (O.value start + 1) := by
        have hs : 2 * O.value (start + 1) = 3 * O.value start + 1 := by
          simpa [hfirst] using O.step start
        omega
      have hrest := ih (start := start + 1) htail
      have hindex : start + (L + 1) = start + 1 + L := by omega
      calc
        2 ^ (L + 1) * (O.value (start + (L + 1)) + 1)
            = 2 *
                (2 ^ L * (O.value (start + 1 + L) + 1)) := by
                  rw [hindex, pow_succ]
                  ring
        _ = 2 * (3 ^ L * (O.value (start + 1) + 1)) := by
              rw [hrest]
        _ = 3 ^ L * (2 * (O.value (start + 1) + 1)) := by ring
        _ = 3 ^ L * (3 * (O.value start + 1)) := by rw [hstep]
        _ = 3 ^ (L + 1) * (O.value start + 1) := by
              rw [pow_succ]
              ring

/-- 任意の指数1有限区間はall-one exponent word。 -/
theorem segmentWord_eq_replicate_one
    (O : OddOrbit) :
    ∀ {start L : ℕ},
      (∀ k : ℕ, k < L → O.exponent (start + k) = 1) →
      O.segmentWord start L = List.replicate L 1 := by
  intro start L
  induction L generalizing start with
  | zero => simp
  | succ L ih =>
      intro hones
      have hfirst : O.exponent start = 1 := by
        simpa using hones 0 (by omega)
      have htail : ∀ k : ℕ, k < L →
          O.exponent (start + 1 + k) = 1 := by
        intro k hk
        have h := hones (k + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      rw [
        O.segmentWord_succ,
        hfirst,
        ih (start := start + 1) htail
      ]
      change 1 :: List.replicate L 1 =
        List.replicate (Nat.succ L) 1
      rw [List.replicate_succ]
/--
future-minimum first-crossing終点から最初のhigh-exponent eventまでの正本データ。
-/
structure FutureMinimumFirstCrossingHighEventData (O : OddOrbit) where
  unbounded : O.Unbounded
  anchor : ℕ
  crossingLength : ℕ
  futureMinimum : O.FutureMinimumAt anchor
  crossing : FirstCrossingAt O anchor crossingLength
  highOffset : ℕ
  beforeHigh_one : ∀ k : ℕ, k < highOffset →
    O.exponent (anchor + crossingLength + k) = 1
  high : HighExponentAt O (anchor + crossingLength + highOffset)

namespace FutureMinimumFirstCrossingHighEventData

/-- first-crossing終点位置。 -/
def crossingEndPosition
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) : ℕ :=
  D.anchor + D.crossingLength

/-- 最初のhigh-event位置。 -/
def highPosition
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) : ℕ :=
  D.crossingEndPosition + D.highOffset

/-- first-crossing終点からhigh eventまでのconnector word。 -/
def connectorWord
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) : ExpWord :=
  O.segmentWord D.crossingEndPosition D.highOffset

/-- connectorはall-one word。 -/
theorem connectorWord_eq_replicate_one
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    D.connectorWord = List.replicate D.highOffset 1 := by
  unfold connectorWord crossingEndPosition
  apply segmentWord_eq_replicate_one
  intro k hk
  simpa [Nat.add_assoc] using D.beforeHigh_one k hk

/-- connector開始値+1は`2^(L+1)`をexactに含む。 -/
theorem crossingEnd_plusOne_exactFactor
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    ∃ u : ℕ,
      ExactTwoFactor
        (O.value D.crossingEndPosition + 1)
        (D.highOffset + 1) u := by
  unfold crossingEndPosition
  apply plusOne_exactFactor_of_one_run_to_high O
  · intro k hk
    simpa [Nat.add_assoc] using D.beforeHigh_one k hk
  · simpa [highPosition, crossingEndPosition, Nat.add_assoc] using D.high

/-- `L = O(log crossingEndpoint)`の整数版。 -/
theorem twoPow_highOffset_succ_le_crossingEnd_add_one
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    2 ^ (D.highOffset + 1) ≤ O.value D.crossingEndPosition + 1 := by
  obtain ⟨u, hu⟩ := D.crossingEnd_plusOne_exactFactor
  have huPos : 0 < u := by
    rcases hu.2 with ⟨k, hk⟩
    omega
  rw [hu.1]
  have hone : 1 ≤ u := by omega
  simpa using
    Nat.mul_le_mul_left (2 ^ (D.highOffset + 1)) hone

/-- connector上の`x+1` exact transport。 -/
theorem connector_scaled_addOne
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    2 ^ D.highOffset * (O.value D.highPosition + 1) =
      3 ^ D.highOffset * (O.value D.crossingEndPosition + 1) := by
  unfold highPosition crossingEndPosition
  apply oneRun_scaled_addOne O
  intro k hk
  simpa [Nat.add_assoc] using D.beforeHigh_one k hk

/-- `3^n ≤ 4^n`。 -/
private theorem threePow_le_fourPow (n : ℕ) :
    3 ^ n ≤ 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul ih (by omega)

/-- 最初のhigh-event値は`(crossingEndpoint+1)^2`以下。 -/
theorem highValue_le_crossingEnd_addOne_sq
    {O : OddOrbit}
    (D : FutureMinimumFirstCrossingHighEventData O) :
    O.value D.highPosition ≤
      (O.value D.crossingEndPosition + 1) ^ 2 := by
  let L := D.highOffset
  let z := O.value D.crossingEndPosition
  let y := O.value D.highPosition
  have htransport := D.connector_scaled_addOne
  have h34 : 3 ^ L ≤ 4 ^ L := threePow_le_fourPow L
  have hscaled :
      2 ^ L * (y + 1) ≤
        2 ^ L * (2 ^ L * (z + 1)) := by
    calc
      2 ^ L * (y + 1)
          = 3 ^ L * (z + 1) := by
              simpa [L, y, z] using htransport
      _ ≤ 4 ^ L * (z + 1) :=
            Nat.mul_le_mul_right (z + 1) h34
      _ = 2 ^ L * (2 ^ L * (z + 1)) := by
            rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
            ring
  have hcancel : y + 1 ≤ 2 ^ L * (z + 1) :=
    Nat.le_of_mul_le_mul_left hscaled
      (Nat.pow_pos (by omega : 0 < (2 : ℕ)))
  have hpowStrong := D.twoPow_highOffset_succ_le_crossingEnd_add_one
  have hpowWeak : 2 ^ L ≤ z + 1 := by
    have hpowMono : 2 ^ L ≤ 2 ^ (L + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    exact le_trans hpowMono (by simpa [L, z] using hpowStrong)
  have hmul : 2 ^ L * (z + 1) ≤ (z + 1) * (z + 1) :=
    Nat.mul_le_mul_right (z + 1) hpowWeak
  have hy : y ≤ (z + 1) * (z + 1) := by
    omega
  simpa [L, y, z, pow_two] using hy

end FutureMinimumFirstCrossingHighEventData

/--
指定位置以後にはhigh-exponent eventへのoffsetが存在する。
-/
private theorem exists_highExponentOffset
    (O : OddOrbit)
    (start : ℕ) :
    ∃ L : ℕ, HighExponentAt O (start + L) := by
  obtain ⟨n, hn, hhigh⟩ :=
    highExponent_cofinally O start
  let L := n - start
  have hindex : start + L = n := by
    dsimp [L]
    omega
  refine ⟨L, ?_⟩
  rw [hindex]
  exact hhigh

/-- 指定位置以後の最初のhigh-exponent offset。 -/
private noncomputable def firstHighOffset
    (O : OddOrbit)
    (start : ℕ)
    (hExists : ∃ L : ℕ, HighExponentAt O (start + L)) :
    ℕ := by
  classical
  exact Nat.find hExists

/-- firstHighOffset自身はhigh-exponent位置。 -/
private theorem firstHighOffset_high
    (O : OddOrbit)
    (start : ℕ)
    (hExists : ∃ L : ℕ, HighExponentAt O (start + L)) :
    HighExponentAt O (start + firstHighOffset O start hExists) := by
  classical
  unfold firstHighOffset
  exact Nat.find_spec hExists


/-- firstHighOffsetはすべてのhigh-exponent offset以下。 -/
private theorem firstHighOffset_le
    (O : OddOrbit)
    (start : ℕ)
    (hExists : ∃ L : ℕ, HighExponentAt O (start + L))
    {k : ℕ}
    (hk : HighExponentAt O (start + k)) :
    firstHighOffset O start hExists ≤ k := by
  classical
  unfold firstHighOffset
  exact Nat.find_min' hExists hk

/--
最初のhigh-exponent offsetより前では指数はexactに1。
-/
private theorem exponent_eq_one_before_firstHigh
    (O : OddOrbit)
    (start : ℕ)
    (hExists : ∃ L : ℕ, HighExponentAt O (start + L))
    {k : ℕ}
    (hk : k < firstHighOffset O start hExists) :
    O.exponent (start + k) = 1 := by
  have hnot :
      ¬ HighExponentAt O (start + k) := by
    intro hkHigh
    have hle :
        firstHighOffset O start hExists ≤ k :=
      firstHighOffset_le O start hExists hkHigh
    omega
  have hpos :
      0 < O.exponent (start + k) :=
    O.exponent_pos (start + k)
  unfold HighExponentAt at hnot
  omega


/--
指定future-minimum first-crossingから、その後最初のhigh-exponent eventを構成する。
-/
noncomputable def firstCrossingFirstHighEventData
    (O : OddOrbit)
    (hU : O.Unbounded)
    {anchor p : ℕ}
    (hmin : O.FutureMinimumAt anchor)
    (hC : FirstCrossingAt O anchor p) :
    FutureMinimumFirstCrossingHighEventData O := by
  let start := anchor + p
  have hExists :
      ∃ L : ℕ, HighExponentAt O (start + L) :=
    exists_highExponentOffset O start
  let L := firstHighOffset O start hExists
  have hHigh :
      HighExponentAt O (start + L) := by
    dsimp [L]
    exact firstHighOffset_high O start hExists
  refine
    { unbounded := hU
      anchor := anchor
      crossingLength := p
      futureMinimum := hmin
      crossing := hC
      highOffset := L
      beforeHigh_one := ?_
      high := ?_ }
  · intro k hk
    have hkOne :
        O.exponent (start + k) = 1 := by
      apply exponent_eq_one_before_firstHigh O start hExists
      simpa [L] using hk
    simpa [start] using hkOne
  · simpa [start] using hHigh


/--
非有界軌道のfuture-minimumは、one-sided meanderか、
first-crossingとその後最初のhigh-eventを持つデータのどちらかへ入る。
-/
theorem futureMinimum_meander_or_firstCrossingHighEvent
    (O : OddOrbit)
    (hU : O.Unbounded)
    (anchor : ℕ)
    (hmin : O.FutureMinimumAt anchor) :
    MeanderAt O anchor ∨
      Nonempty (FutureMinimumFirstCrossingHighEventData O) := by
  rcases meander_or_firstCrossing_at O anchor with hM | hC
  · exact Or.inl hM
  · rcases hC with ⟨p, hp⟩
    exact Or.inr ⟨firstCrossingFirstHighEventData O hU hmin hp⟩

/--
Baker型first-crossing endpoint評価と`2^(L+1)≤endpoint+1`を合成し、
connector長の対数上界を純整数の多項式不等式として表す。
-/
theorem firstHighConnector_twoPow_polynomial
    (hGap : TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      ∀ O : OddOrbit,
      ∀ D : FutureMinimumFirstCrossingHighEventData O,
        2 ^ (D.highOffset + 1) ≤
          K * (D.crossingLength + 1) ^ A := by
  obtain ⟨K, A, hEndpoint⟩ :=
    futureMinimum_firstCrossing_endpoint_polynomial hGap
  refine ⟨K + 1, A + 1, ?_⟩
  intro O D
  have hz :
      O.value D.crossingEndPosition ≤
        K * (D.crossingLength + 1) ^ A := by
    simpa [FutureMinimumFirstCrossingHighEventData.crossingEndPosition] using
      hEndpoint O D.anchor D.crossingLength D.futureMinimum D.crossing
  have htwo := D.twoPow_highOffset_succ_le_crossingEnd_add_one
  let b := D.crossingLength + 1
  have hbPos : 0 < b := by dsimp [b]; omega
  have hpowGrow : b ^ A ≤ b ^ (A + 1) :=
    Nat.pow_le_pow_right hbPos (by omega)
  have hpowPos : 0 < b ^ (A + 1) := Nat.pow_pos hbPos
  calc
    2 ^ (D.highOffset + 1)
        ≤ O.value D.crossingEndPosition + 1 := htwo
    _ ≤ K * b ^ A + 1 := Nat.add_le_add_right hz 1
    _ ≤ K * b ^ (A + 1) + b ^ (A + 1) := by
          exact Nat.add_le_add
            (Nat.mul_le_mul_left K hpowGrow)
            (by omega)
    _ = (K + 1) * b ^ (A + 1) := by ring

/--
最初のhigh-event値もfirst-crossing長に対して一様多項式小。
-/
theorem firstHighEvent_value_polynomial
    (hGap : TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      ∀ O : OddOrbit,
      ∀ D : FutureMinimumFirstCrossingHighEventData O,
        O.value D.highPosition ≤
          K * (D.crossingLength + 1) ^ A := by
  obtain ⟨K, A, hEndpoint⟩ :=
    futureMinimum_firstCrossing_endpoint_polynomial hGap
  let K' := (K + 1) * (K + 1)
  let A' := (A + 1) + (A + 1)
  refine ⟨K', A', ?_⟩
  intro O D
  let b := D.crossingLength + 1
  have hbPos : 0 < b := by dsimp [b]; omega
  have hz :
      O.value D.crossingEndPosition ≤ K * b ^ A := by
    simpa [b, FutureMinimumFirstCrossingHighEventData.crossingEndPosition] using
      hEndpoint O D.anchor D.crossingLength D.futureMinimum D.crossing
  have hpowGrow : b ^ A ≤ b ^ (A + 1) :=
    Nat.pow_le_pow_right hbPos (by omega)
  have hpowPos : 0 < b ^ (A + 1) := Nat.pow_pos hbPos
  have hzBound :
      O.value D.crossingEndPosition + 1 ≤
        (K + 1) * b ^ (A + 1) := by
    calc
      O.value D.crossingEndPosition + 1
          ≤ K * b ^ A + 1 := Nat.add_le_add_right hz 1
      _ ≤ K * b ^ (A + 1) + b ^ (A + 1) := by
            exact Nat.add_le_add
              (Nat.mul_le_mul_left K hpowGrow)
              (by omega)
      _ = (K + 1) * b ^ (A + 1) := by ring
  have hy := D.highValue_le_crossingEnd_addOne_sq
  have hsquareMul :
      (O.value D.crossingEndPosition + 1) *
          (O.value D.crossingEndPosition + 1) ≤
        ((K + 1) * b ^ (A + 1)) *
          ((K + 1) * b ^ (A + 1)) :=
    Nat.mul_le_mul hzBound hzBound
  have hsquare :
      (O.value D.crossingEndPosition + 1) ^ 2 ≤
        ((K + 1) * b ^ (A + 1)) ^ 2 := by
    simpa [pow_two] using hsquareMul
  calc
    O.value D.highPosition
        ≤ (O.value D.crossingEndPosition + 1) ^ 2 := hy
    _ ≤ ((K + 1) * b ^ (A + 1)) ^ 2 := hsquare
    _ = K' * b ^ A' := by
          dsimp [K', A']
          rw [pow_two]
          conv_rhs => rw [pow_add]
          ring

end CollatzSecondLayer3
