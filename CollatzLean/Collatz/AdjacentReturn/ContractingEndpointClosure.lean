import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.Global
import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.EndpointFloorZeroBranches

/-!
# Contracting branch closure interface

Contracting 側は

`CanonicalChain`
  -> eventual natural j=0 packet
  -> source-preserving minimal positive candidate
  -> endpoint-floor zero packet
  -> e=1 / e=2

へ還元される。

従って Ellison 型 effective gap を入力として受け取る場合、
今後 Contracting 側で証明すべき新規数学は

* `EndpointFloorZero.NoE1Branch`
* `EndpointFloorZero.NoE2Branch`

の二つだけになる。
-/

namespace Collatz
namespace AdjacentReturn

/--
Baker/canonical shift 後の Contracting branch は、
e=1/e=2 の二枝排除だけで完全に消える。
したがって非有界反例があるなら Expanding integer tower 側にしか残れない。
-/
theorem unbounded_to_expandingInteger_of_endpointFloorBranches
    (hGap : External.TwoThreeGapPolynomialBound)
    (hEffective : External.TwoThreeEffectiveGapInput)
    (hE1 : PositiveReturn.EndpointFloorZero.NoE1Branch)
    (hE2 : PositiveReturn.EndpointFloorZero.NoE2Branch) :
    HasUnboundedOddOrbit →
      IntegerObstruction.HasExpandingIntegerTower := by
  intro hU
  rcases
      PositiveReturn.unbounded_to_expandingInteger_or_positiveReturn
        hGap hU with hExp | hCon
  · exact hExp
  · exact False.elim
      (PositiveReturn.EndpointFloorZero.no_canonicalChain_of_e1_e2
        hEffective hE1 hE2 hCon)

/--
Expanding obstruction も別途排除できれば、非有界 odd 反例は存在しない。
Contracting 側の入力は e=1/e=2 の二枝だけ。
-/
theorem no_unbounded_of_no_expanding_and_endpointFloorBranches
    (hGap : External.TwoThreeGapPolynomialBound)
    (hEffective : External.TwoThreeEffectiveGapInput)
    (hE1 : PositiveReturn.EndpointFloorZero.NoE1Branch)
    (hE2 : PositiveReturn.EndpointFloorZero.NoE2Branch)
    (hExpanding : ¬ IntegerObstruction.HasExpandingIntegerTower) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  exact hExpanding
    (unbounded_to_expandingInteger_of_endpointFloorBranches
      hGap hEffective hE1 hE2 hU)

end AdjacentReturn
end Collatz
