import CollatzLean.Collatz.AdjacentReturn.FirstCrossing
import CollatzLean.Collatz.External.TwoThreeGap
import CollatzLean.Collatz.Arithmetic.Growth
import CollatzLean.Collatz.TwoAdic.Valuation

/-!
# adjacent first-crossing actual return算術

0a503cで得ていた
`B = 3^p*d + g*z`, `3*d < p`, return slack, Baker接続を
新FirstCrossingData上へ戻す。
-/

namespace Collatz
namespace AdjacentReturn
namespace FirstCrossingData

/-- return gapは偶数。 -/
theorem returnGap_even
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    Even F.returnGap := by
  have hlt := F.start_lt_endpoint
  rcases O.value_odd R.startIndex with ⟨a, ha⟩
  rcases O.value_odd (R.startIndex + F.length) with ⟨b, hb⟩
  have hab : a < b := by
    unfold State.startValue endpointValue at hlt
    rw [ha, hb] at hlt
    omega
  refine ⟨b - a, ?_⟩
  unfold returnGap endpointValue State.startValue
  rw [ha, hb]
  omega

/-- positive even return gapは少なくとも2。 -/
theorem two_le_returnGap
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    2 ≤ F.returnGap := by
  obtain ⟨q, hq⟩ := F.returnGap_even
  have hpos := F.returnGap_pos
  rw [hq] at hpos ⊢
  omega

/-- multiplicative gapは正。 -/
theorem multiplicativeGap_pos
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    0 < F.multiplicativeGap := by
  unfold multiplicativeGap totalExponent
  have h := F.crossing.terminalContracting
  simpa [F.oddSteps_word] using Nat.sub_pos_of_lt h

/-- first-crossing actual prefixのscaled equation。 -/
theorem firstCrossing_scaledEquation
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    2 ^ F.totalExponent * F.endpointValue =
      3 ^ F.length * R.startValue + F.affine := by
  have h := F.realizes
  unfold Word.Realizes at h
  simpa [totalExponent, endpointValue, affine, F.oddSteps_word] using h


/-- first-crossing endpointはstartとreturn gapの和。 -/
theorem endpointValue_eq_startValue_add_returnGap
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    F.endpointValue = R.startValue + F.returnGap := by
  unfold returnGap
  rw [Nat.add_comm]
  exact (Nat.sub_add_cancel F.start_le_endpoint).symm


/-- first-crossingはcontractingなので`3^p < 2^H`。 -/
theorem threePow_length_lt_twoPow_totalExponent
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    3 ^ F.length < 2 ^ F.totalExponent := by
  have h := F.crossing.terminalContracting
  change
    3 ^ Word.oddSteps (R.word.take F.length) <
      2 ^ Word.twoSteps (R.word.take F.length)
    at h
  rw [F.oddSteps_word] at h
  simpa [totalExponent] using h


/-- multiplicative gapを加法形`2^H = 3^p + g`へ戻す。 -/
theorem twoPow_totalExponent_eq_threePow_length_add_multiplicativeGap
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    2 ^ F.totalExponent =
      3 ^ F.length + F.multiplicativeGap := by
  unfold multiplicativeGap
  exact
    (Nat.add_sub_of_le
      (threePow_length_lt_twoPow_totalExponent F).le).symm

/-- return equationの純算術的消去。 -/
private theorem affine_eq_of_return_equations
    {A T x z d g B : ℕ}
    (hrun : T * z = A * x + B)
    (hzd : z = x + d)
    (htwo : T = A + g) :
    B = A * d + g * z := by
  have hcancel :
      A * x + (A * d + g * z) =
        A * x + B := by
    calc
      A * x + (A * d + g * z)
          = (A + g) * z := by
              rw [hzd]
              ring
      _ = T * z := by
            rw [← htwo]
      _ = A * x + B := hrun
  exact (Nat.add_left_cancel hcancel).symm

/-- exact actual return identity `B = 3^p*d + g*z`。 -/
theorem return_identity
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    F.affine =
      3 ^ F.length * F.returnGap +
        F.multiplicativeGap * F.endpointValue := by
  exact affine_eq_of_return_equations
    (firstCrossing_scaledEquation F)
    (endpointValue_eq_startValue_add_returnGap F)
    (twoPow_totalExponent_eq_threePow_length_add_multiplicativeGap F)

/-- first-crossing affine定数のsharp上界。 -/
theorem affine_le_sharp
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    F.affine ≤ F.length * 3 ^ (F.length - 1) := by
  unfold affine
  simpa [F.word_length] using F.crossing.affineConst_le_sharp

/-- actual return gapは`p/3`より真に小さい。 -/
theorem three_mul_returnGap_lt_length
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    3 * F.returnGap < F.length := by
  have hp : 0 < F.length := F.length_pos
  obtain ⟨r, hr⟩ : ∃ r : ℕ, F.length = r + 1 :=
    ⟨F.length - 1, by omega⟩
  let d := F.returnGap
  let g := F.multiplicativeGap
  let z := F.endpointValue
  let B := F.affine
  have hid : B = 3 ^ F.length * d + g * z := by
    simpa [B, d, g, z] using F.return_identity
  have hg : 0 < g := by simpa [g] using F.multiplicativeGap_pos
  have hz : 0 < z := by
    dsimp [z, endpointValue]
    exact O.value_pos _
  have hgz : 0 < g * z := Nat.mul_pos hg hz
  have hlow : 3 ^ F.length * d < B := by
    rw [hid]
    omega
  have hB : B ≤ F.length * 3 ^ (F.length - 1) := by
    simpa [B] using F.affine_le_sharp
  have hchain : 3 ^ F.length * d < F.length * 3 ^ (F.length - 1) :=
    lt_of_lt_of_le hlow hB
  rw [hr] at hchain ⊢
  have hpowPos : 0 < 3 ^ r := Nat.pow_pos (by omega)
  have hscaled : 3 ^ r * (3 * d) < 3 ^ r * (r + 1) := by
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hchain
  exact (Nat.mul_lt_mul_left hpowPos).mp hscaled

/-- return gap自身は語長未満。 -/
theorem returnGap_lt_length
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    F.returnGap < F.length := by
  have h := F.three_mul_returnGap_lt_length
  omega

/-- first-crossing return slack `p-3d`。 -/
def returnSlack
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) : ℕ :=
  F.length - 3 * F.returnGap

/-- return slackは正。 -/
theorem returnSlack_pos
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    0 < F.returnSlack := by
  unfold returnSlack
  have h := F.three_mul_returnGap_lt_length
  omega

/-- `3*g*endpoint ≤ (p-3d)*3^p`。 -/
theorem three_mul_gap_mul_endpoint_le_returnSlack_threePow
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    3 * F.multiplicativeGap * F.endpointValue ≤
      F.returnSlack * 3 ^ F.length := by
  let d := F.returnGap
  let g := F.multiplicativeGap
  let z := F.endpointValue
  let B := F.affine
  let s := F.returnSlack
  have hp : 0 < F.length := F.length_pos
  have hsharp : 3 * d < F.length := by
    simpa [d] using F.three_mul_returnGap_lt_length
  have hps : F.length = 3 * d + s := by
    dsimp [s, returnSlack, d]
    omega
  have hid : B = 3 ^ F.length * d + g * z := by
    simpa [B, d, g, z] using F.return_identity
  have hB : B ≤ F.length * 3 ^ (F.length - 1) := by
    simpa [B] using F.affine_le_sharp
  have hp1 : 1 ≤ F.length := by omega
  have hpow : 3 * 3 ^ (F.length - 1) = 3 ^ F.length := by
    calc
      3 * 3 ^ (F.length - 1) = 3 ^ (F.length - 1) * 3 := by ring
      _ = 3 ^ ((F.length - 1) + 1) := by rw [pow_succ]
      _ = 3 ^ F.length := by rw [Nat.sub_add_cancel hp1]
  have hscaled : 3 * B ≤ F.length * 3 ^ F.length := by
    have h := Nat.mul_le_mul_left 3 hB
    calc
      3 * B ≤ 3 * (F.length * 3 ^ (F.length - 1)) := h
      _ = F.length * 3 ^ F.length := by rw [← hpow]; ring
  have hsum :
      3 ^ F.length * (3 * d) + 3 * g * z ≤
        3 ^ F.length * (3 * d) + s * 3 ^ F.length := by
    calc
      3 ^ F.length * (3 * d) + 3 * g * z = 3 * B := by rw [hid]; ring
      _ ≤ F.length * 3 ^ F.length := hscaled
      _ = 3 ^ F.length * (3 * d) + s * 3 ^ F.length := by rw [hps]; ring
  have hcancel : 3 * g * z ≤ s * 3 ^ F.length :=
    Nat.le_of_add_le_add_left hsum
  simpa [g, z, s] using hcancel

/-- Baker型gap入力とslack評価からendpointを多項式で抑える。 -/
theorem endpoint_le_returnSlack_polynomial
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
      ∀ F : FirstCrossingData R,
        3 * F.endpointValue ≤ F.returnSlack * (K * (F.length + 1) ^ A) := by
  rcases hGap with ⟨K, A, _hK, hBaker⟩
  refine ⟨K, A, ?_⟩
  intro O R F
  let H := F.totalExponent
  let g := F.multiplicativeGap
  let s := F.returnSlack
  let z := F.endpointValue
  have hp : 0 < F.length := F.length_pos
  have hcontract : 3 ^ F.length < 2 ^ H := by
    simpa [H] using F.threePow_length_lt_twoPow_totalExponent
  have hg : 0 < g := by simpa [g] using F.multiplicativeGap_pos
  have hBaker' : 3 ^ F.length ≤ K * (F.length + 1) ^ A * g := by
    simpa [H, g, multiplicativeGap] using hBaker F.length H hp hcontract
  have hslack : 3 * g * z ≤ s * 3 ^ F.length := by
    simpa [g, s, z] using F.three_mul_gap_mul_endpoint_le_returnSlack_threePow
  have hwithG :
      g * (3 * z) ≤ g * (s * (K * (F.length + 1) ^ A)) := by
    calc
      g * (3 * z) = 3 * g * z := by ring
      _ ≤ s * 3 ^ F.length := hslack
      _ ≤ s * (K * (F.length + 1) ^ A * g) := Nat.mul_le_mul_left s hBaker'
      _ = g * (s * (K * (F.length + 1) ^ A)) := by ring
  have hcancel : 3 * z ≤ s * (K * (F.length + 1) ^ A) :=
    Nat.le_of_mul_le_mul_left hwithG hg
  simpa [z, s] using hcancel

/-- return gapのexact 2進depthにも`3*2^D < p`。 -/
theorem three_mul_twoPow_returnDepth_lt_length
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R)
    {D u : ℕ} (hD : TwoAdic.ExactFactor F.returnGap D u) :
    3 * 2 ^ D < F.length := by
  have hgap := F.three_mul_returnGap_lt_length
  have huPos : 0 < u := by
    rcases hD.2 with ⟨k, hk⟩
    omega
  have hpowLe : 2 ^ D ≤ 2 ^ D * u := by
    have hu : 1 ≤ u := by omega
    simpa using Nat.mul_le_mul_left (2 ^ D) hu
  rw [hD.1] at hgap
  have hthree := Nat.mul_le_mul_left 3 hpowLe
  exact lt_of_le_of_lt hthree hgap

/-- first-crossing開始値の粗い有限bound。towerで`p→∞`を戻すために使う。 -/
theorem startValue_le_length_mul_threePow
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    R.startValue ≤ F.length * 3 ^ F.length := by
  have hgPos : 0 < F.multiplicativeGap := F.multiplicativeGap_pos
  have hg : 1 ≤ F.multiplicativeGap := by omega
  have hz : R.startValue ≤ F.endpointValue := F.start_le_endpoint
  have hgz : F.endpointValue ≤ F.multiplicativeGap * F.endpointValue := by
    simpa using Nat.mul_le_mul_right F.endpointValue hg
  have hterm :
      F.multiplicativeGap * F.endpointValue ≤ F.affine := by
    rw [F.return_identity]
    omega
  have hB := F.affine_le_sharp
  have hpow : 3 ^ (F.length - 1) ≤ 3 ^ F.length :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact le_trans hz (le_trans hgz (le_trans hterm
    (le_trans hB (Nat.mul_le_mul_left F.length hpow))))

/-- adjacent future minima間では`d≥4`なのでfirst-crossing長は13以上。 -/
theorem thirteen_le_length
    {O : OddOrbit} {R : State O} (F : FirstCrossingData R) :
    13 ≤ F.length := by
  have hd : 4 ≤ F.returnGap := F.four_le_returnGap
  have hsharp := F.three_mul_returnGap_lt_length
  omega

private theorem twoPow_succ_le_threePow_of_two_le
    (p : ℕ) (hp : 2 ≤ p) : 2 ^ (p + 1) ≤ 3 ^ p := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ, p = q + 2 := ⟨p - 2, by omega⟩
  subst p
  have hpow : 2 ^ q ≤ 3 ^ q := Arithmetic.twoPow_le_threePow q
  calc
    2 ^ ((q + 2) + 1) = 8 * 2 ^ q := by
      rw [show q + 2 + 1 = 3 + q by omega, pow_add]
      norm_num
    _ ≤ 9 * 3 ^ q := Nat.mul_le_mul (by norm_num) hpow
    _ = 3 ^ (q + 2) := by
      rw [show q + 2 = 2 + q by omega, pow_add]
      norm_num

/-- 十分長いfirst crossingではmultiplicative gapは語長より大きい。 -/
theorem multiplicativeGap_gt_length_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
      ∀ F : FirstCrossingData R,
        N ≤ F.length → F.length < F.multiplicativeGap := by
  rcases hGap with ⟨K, A, _hK, hBaker⟩
  obtain ⟨Npoly, hNpoly⟩ := Arithmetic.polynomialBelowTwoPower K (A + 1)
  let N := max Npoly 2
  refine ⟨N, ?_⟩
  intro O R F hpN
  have hp : 0 < F.length := F.length_pos
  let H := F.totalExponent
  let g := F.multiplicativeGap
  have hcontract : 3 ^ F.length < 2 ^ H := by
    simpa [H] using F.threePow_length_lt_twoPow_totalExponent
  have hBaker' : 3 ^ F.length ≤ K * (F.length + 1) ^ A * g := by
    simpa [g, H, multiplicativeGap] using hBaker F.length H hp hcontract
  have hpTwo : 2 ≤ F.length := by dsimp [N] at hpN; omega
  have htwoThree := twoPow_succ_le_threePow_of_two_le F.length hpTwo
  by_contra hnot
  have hgle : g ≤ F.length := Nat.le_of_not_gt hnot
  have hpolyGrow :
      K * (F.length + 1) ^ A * F.length ≤
        K * (F.length + 1) ^ (A + 1) := by
    have hpLe : F.length ≤ F.length + 1 := by omega
    have hmul := Nat.mul_le_mul_left (K * (F.length + 1) ^ A) hpLe
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hthreePoly : 3 ^ F.length ≤ K * (F.length + 1) ^ (A + 1) := by
    calc
      3 ^ F.length ≤ K * (F.length + 1) ^ A * g := hBaker'
      _ ≤ K * (F.length + 1) ^ A * F.length :=
        Nat.mul_le_mul_left (K * (F.length + 1) ^ A) hgle
      _ ≤ K * (F.length + 1) ^ (A + 1) := hpolyGrow
  have hpolyTwo : K * (F.length + 1) ^ (A + 1) < 2 ^ (F.length + 1) := by
    apply hNpoly F.length
    dsimp [N] at hpN
    omega
  have : 3 ^ F.length < 3 ^ F.length :=
    lt_of_le_of_lt hthreePoly (lt_of_lt_of_le hpolyTwo htwoThree)
  exact (Nat.lt_irrefl _) this

/-- 十分長いfirst crossingではactual return gapもmultiplicative gapより小さい。 -/
theorem returnGap_lt_multiplicativeGap_eventually
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ N : ℕ,
      ∀ O : OddOrbit,
      ∀ R : State O,
      ∀ F : FirstCrossingData R,
        N ≤ F.length → F.returnGap < F.multiplicativeGap := by
  obtain ⟨N, hN⟩ := multiplicativeGap_gt_length_eventually hGap
  refine ⟨N, ?_⟩
  intro O R F hp
  exact lt_trans F.returnGap_lt_length (hN O R F hp)

end FirstCrossingData
end AdjacentReturn
end Collatz
