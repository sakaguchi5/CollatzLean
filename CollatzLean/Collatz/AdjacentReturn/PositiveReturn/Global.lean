import CollatzLean.Collatz.AdjacentReturn.PositiveReturn
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Global
import CollatzLean.Collatz.Canonical.FirstCrossingReduction

/-!
# positive canonical return を contracting 側の最上位 obstruction にする bridge

Exact/Late や prepend-one CORE より前に、Baker/canonical shift 後の contracting 側を
`HasCanonicalChain` へ集約する。CORE はこの obstruction を排除する fallback として残す。
-/

namespace Collatz
namespace AdjacentReturn
namespace PositiveReturn

/--
Baker 型 gap 入力のもと、非有界反例は expanding integer tower か
positive canonical return chain のどちらかを与える。
-/
theorem unbounded_to_expandingInteger_or_positiveReturn
    (hGap : External.TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      IntegerObstruction.HasExpandingIntegerTower ∨ HasCanonicalChain := by
  intro hU
  rcases
      IntegerObstruction.unbounded_to_expandingInteger_or_canonicalContracting
        hGap hU with hE | hC
  · exact Or.inl hE
  · rcases hC with ⟨O, ⟨C⟩⟩
    exact Or.inr
      ⟨O, ⟨CanonicalChain.ofCanonicalContractingChain C hGap⟩⟩

/--
既存 CORE 原理は positive-return obstruction 全体を排除する。
Exact/Late や quotient の場合分けはここでは最終目標に露出させない。
-/
theorem no_canonicalChain_of_core
    (hCore : Word.PrependOneCorePrinciple) :
    ¬ HasCanonicalChain := by
  rintro ⟨O, ⟨C⟩⟩
  let F := C.firstCrossing 0
  have hvalid : Word.Valid (C.word 0) := C.word_valid 0
  have hcross : Word.FirstCrossing (C.word 0) := by
    simpa [CanonicalChain.word, F] using F.crossing
  have hlen : 1 < (C.word 0).length := by
    rw [C.word_length]
    have h13 := C.thirteen_le_length 0
    omega
  have hdescent :
      Word.canonicalEnd (C.word 0) ≤ Word.canonicalStart (C.word 0) :=
    Word.FirstCrossing.canonicalEnd_le_canonicalStart_of_core
      hCore hvalid hcross hlen
  have hpositive := C.positive 0
  omega

/-- CORE を使う場合も、まず positive-return obstruction を経由して contracting 側を消す。 -/
theorem unbounded_to_expandingInteger_of_core
    (hGap : External.TwoThreeGapPolynomialBound)
    (hCore : Word.PrependOneCorePrinciple) :
    HasUnboundedOddOrbit → IntegerObstruction.HasExpandingIntegerTower := by
  intro hU
  rcases unbounded_to_expandingInteger_or_positiveReturn hGap hU with hE | hP
  · exact hE
  · exact False.elim (no_canonicalChain_of_core hCore hP)

/-- expanding obstruction と positive-return obstruction の双方を排除すれば非有界軌道はない。 -/
theorem no_unbounded_of_no_expanding_no_positive
    (hGap : External.TwoThreeGapPolynomialBound)
    (hExpanding : ¬ IntegerObstruction.HasExpandingIntegerTower)
    (hPositive : ¬ HasCanonicalChain) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_to_expandingInteger_or_positiveReturn hGap hU with hE | hP
  · exact hExpanding hE
  · exact hPositive hP

/-- CORE は positive-return 排除の既存 fallback を供給する。 -/
theorem no_unbounded_of_core_and_no_expanding
    (hGap : External.TwoThreeGapPolynomialBound)
    (hCore : Word.PrependOneCorePrinciple)
    (hExpanding : ¬ IntegerObstruction.HasExpandingIntegerTower) :
    ¬ HasUnboundedOddOrbit := by
  exact no_unbounded_of_no_expanding_no_positive
    hGap hExpanding (no_canonicalChain_of_core hCore)

end PositiveReturn
end AdjacentReturn
end Collatz
