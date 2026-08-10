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

end FirstCrossingArithmeticData
end IntegerObstruction
end AdjacentReturn
end Collatz
