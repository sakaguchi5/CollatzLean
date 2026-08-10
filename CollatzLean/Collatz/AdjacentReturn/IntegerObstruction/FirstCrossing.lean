import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Basic
import CollatzLean.Collatz.AdjacentReturn.FirstCrossingArithmetic

/-!
# first crossing の純算術 package

contracting adjacent block の最小 first crossing から得られる
`B = 3^p*d + g*z`, `3*d < p` などを軌道から切り離して保持する。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/-- 一つの adjacent block に付随する first-crossing 算術。 -/
structure FirstCrossingArithmeticData (B : BlockArithmeticData) where
  length : ℕ
  word : Collatz.Word
  endpointValue : ℕ
  returnGap : ℕ
  totalExponent : ℕ
  multiplicativeGap : ℕ
  affine : ℕ
  le_block : length ≤ B.length
  word_eq_take : word = B.word.take length
  crossing : word.FirstCrossing
  endpoint_eq_start_add_gap :
    endpointValue = B.startValue + returnGap
  returnGap_pos : 0 < returnGap
  four_le_returnGap : 4 ≤ returnGap
  scaledEquation :
    2 ^ totalExponent * endpointValue =
      3 ^ length * B.startValue + affine
  contractingPower : 3 ^ length < 2 ^ totalExponent
  gapEquation :
    2 ^ totalExponent = 3 ^ length + multiplicativeGap
  returnIdentity :
    affine =
      3 ^ length * returnGap + multiplicativeGap * endpointValue
  affineBound :
    affine ≤ length * 3 ^ (length - 1)
  three_mul_returnGap_lt_length :
    3 * returnGap < length
  thirteen_le_length : 13 ≤ length
  returnDepthBound :
    ∀ D u : ℕ,
      TwoAdic.ExactFactor returnGap D u →
        3 * 2 ^ D < length

namespace FirstCrossingArithmeticData

/-- actual first crossing を純算術 package に落とす。 -/
def ofFirstCrossing
    {O : OddOrbit} {R : State O}
    (F : FirstCrossingData R) :
    FirstCrossingArithmeticData (BlockArithmeticData.ofState R) := by
  refine {
    length := F.length
    word := R.word.take F.length
    endpointValue := F.endpointValue
    returnGap := F.returnGap
    totalExponent := F.totalExponent
    multiplicativeGap := F.multiplicativeGap
    affine := F.affine
    le_block := F.le_adjacent
    word_eq_take := rfl
    crossing := F.crossing
    endpoint_eq_start_add_gap := ?_
    returnGap_pos := F.returnGap_pos
    four_le_returnGap := F.four_le_returnGap
    scaledEquation := ?_
    contractingPower := F.threePow_length_lt_twoPow_totalExponent
    gapEquation := F.twoPow_totalExponent_eq_threePow_length_add_multiplicativeGap
    returnIdentity := ?_
    affineBound := F.affine_le_sharp
    three_mul_returnGap_lt_length := F.three_mul_returnGap_lt_length
    thirteen_le_length := F.thirteen_le_length
    returnDepthBound := ?_
  }
  · change F.endpointValue = R.startValue + F.returnGap
    exact F.endpointValue_eq_startValue_add_returnGap
  · change
      2 ^ F.totalExponent * F.endpointValue =
        3 ^ F.length * R.startValue + F.affine
    exact F.firstCrossing_scaledEquation
  · exact F.return_identity
  · intro D u hD
    exact F.three_mul_twoPow_returnDepth_lt_length hD

/-- first-crossing return slack `p - 3*d`。 -/
def returnSlack
    {B : BlockArithmeticData}
    (F : FirstCrossingArithmeticData B) : ℕ :=
  F.length - 3 * F.returnGap

/-- return slack は正。 -/
theorem returnSlack_pos
    {B : BlockArithmeticData}
    (F : FirstCrossingArithmeticData B) :
    0 < F.returnSlack := by
  unfold returnSlack
  exact Nat.sub_pos_of_lt F.three_mul_returnGap_lt_length

/-- 純算術 first-crossing data でも `3*g*z ≤ (p-3*d)*3^p`。 -/
theorem three_mul_gap_mul_endpoint_le_returnSlack_threePow
    {B : BlockArithmeticData}
    (F : FirstCrossingArithmeticData B) :
    3 * F.multiplicativeGap * F.endpointValue ≤
      F.returnSlack * 3 ^ F.length := by
  let d := F.returnGap
  let g := F.multiplicativeGap
  let z := F.endpointValue
  let A := F.affine
  let s := F.returnSlack
  have hsharp : 3 * d < F.length := by
    simpa [d] using F.three_mul_returnGap_lt_length
  have hps : F.length = 3 * d + s := by
    dsimp [s, returnSlack, d]
    omega
  have hid : A = 3 ^ F.length * d + g * z := by
    simpa [A, d, g, z] using F.returnIdentity
  have hA : A ≤ F.length * 3 ^ (F.length - 1) := by
    simpa [A] using F.affineBound
  have hp1 : 1 ≤ F.length := by
    omega
  have hpow : 3 * 3 ^ (F.length - 1) = 3 ^ F.length := by
    calc
      3 * 3 ^ (F.length - 1) = 3 ^ (F.length - 1) * 3 := by ring
      _ = 3 ^ ((F.length - 1) + 1) := by rw [pow_succ]
      _ = 3 ^ F.length := by rw [Nat.sub_add_cancel hp1]
  have hscaled : 3 * A ≤ F.length * 3 ^ F.length := by
    have h := Nat.mul_le_mul_left 3 hA
    calc
      3 * A ≤ 3 * (F.length * 3 ^ (F.length - 1)) := h
      _ = F.length * 3 ^ F.length := by rw [← hpow]; ring
  have hsum :
      3 ^ F.length * (3 * d) + 3 * g * z ≤
        3 ^ F.length * (3 * d) + s * 3 ^ F.length := by
    calc
      3 ^ F.length * (3 * d) + 3 * g * z = 3 * A := by rw [hid]; ring
      _ ≤ F.length * 3 ^ F.length := hscaled
      _ = 3 ^ F.length * (3 * d) + s * 3 ^ F.length := by rw [hps]; ring
  have hcancel : 3 * g * z ≤ s * 3 ^ F.length :=
    Nat.le_of_add_le_add_left hsum
  simpa [g, z, s] using hcancel

/--
Baker 型 polynomial gap を純算術 first-crossing data に直接適用し、
endpoint を return slack 倍の多項式で抑える。
-/
theorem endpoint_le_returnSlack_polynomial
    {B : BlockArithmeticData}
    (F : FirstCrossingArithmeticData B)
    (hGap : External.TwoThreeGapPolynomialBound) :
    ∃ K A : ℕ,
      0 < K ∧
      3 * F.endpointValue ≤
        F.returnSlack * (K * (F.length + 1) ^ A) := by
  rcases hGap with ⟨K, A, hK, hBaker⟩
  have hSlackPos : 0 < F.returnSlack :=
    F.returnSlack_pos
  have hp : 0 < F.length := by
    unfold returnSlack at hSlackPos
    omega
  have hBakerRaw :
      3 ^ F.length ≤
        K * (F.length + 1) ^ A *
          (2 ^ F.totalExponent - 3 ^ F.length) :=
    hBaker F.length F.totalExponent hp F.contractingPower
  have hgapSub :
      2 ^ F.totalExponent - 3 ^ F.length =
        F.multiplicativeGap := by
    rw [F.gapEquation]
    omega
  rw [hgapSub] at hBakerRaw
  have hg : 0 < F.multiplicativeGap := by
    rw [← hgapSub]
    exact Nat.sub_pos_of_lt F.contractingPower
  have hslack :
      3 * F.multiplicativeGap * F.endpointValue ≤
        F.returnSlack * 3 ^ F.length :=
    F.three_mul_gap_mul_endpoint_le_returnSlack_threePow
  have hwithG :
      F.multiplicativeGap * (3 * F.endpointValue) ≤
        F.multiplicativeGap *
          (F.returnSlack * (K * (F.length + 1) ^ A)) := by
    calc
      F.multiplicativeGap * (3 * F.endpointValue)
          = 3 * F.multiplicativeGap * F.endpointValue := by ring
      _ ≤ F.returnSlack * 3 ^ F.length := hslack
      _ ≤ F.returnSlack *
            (K * (F.length + 1) ^ A * F.multiplicativeGap) :=
          Nat.mul_le_mul_left F.returnSlack hBakerRaw
      _ = F.multiplicativeGap *
            (F.returnSlack * (K * (F.length + 1) ^ A)) := by ring
  have hendpoint :
      3 * F.endpointValue ≤
        F.returnSlack * (K * (F.length + 1) ^ A) :=
    Nat.le_of_mul_le_mul_left hwithG hg
  exact ⟨K, A, hK, hendpoint⟩

end FirstCrossingArithmeticData
end IntegerObstruction
end AdjacentReturn
end Collatz
