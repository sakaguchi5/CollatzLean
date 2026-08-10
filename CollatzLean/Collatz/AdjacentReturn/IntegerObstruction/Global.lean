import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Expanding
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Contracting
import CollatzLean.Collatz.AdjacentReturn.CanonicalContractingChain

/-!
# 非有界反例から二整数問題への最終境界

今後の正本を expanding / eventually-contracting の二整数問題に固定する。
細かい枝はこの二つの解集合への追加条件として扱う。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/-- expanding 側の純整数 obstruction が存在する。 -/
def HasExpandingIntegerTower : Prop :=
  Nonempty ExpandingIntegerTower

/-- eventually-contracting 側の純整数 obstruction が存在する。 -/
def HasContractingIntegerChain : Prop :=
  Nonempty ContractingIntegerChain

/--
非有界 odd 軌道は、拡大型整数 tower か、
最終的に全区間が収縮する純整数 chain のどちらかを与える。
-/
theorem unbounded_to_integer_dichotomy :
    HasUnboundedOddOrbit →
      HasExpandingIntegerTower ∨ HasContractingIntegerChain := by
  rintro ⟨O, hU⟩
  rcases dichotomy_on_strong O hU with hE | hC
  · rcases hE with ⟨T⟩
    exact Or.inl ⟨ExpandingIntegerTower.ofTower T⟩
  · rcases hC with ⟨D⟩
    exact Or.inr ⟨ContractingIntegerChain.ofEventuallyContractingTail D⟩

/--
Baker 型 gap 入力を使う場合、収縮側は既存の canonical chain まで強化できる。
純整数側の正本とは分離し、既存 canonical machinery への橋だけを残す。
-/
theorem unbounded_to_expandingInteger_or_canonicalContracting
    (hGap : External.TwoThreeGapPolynomialBound) :
    HasUnboundedOddOrbit →
      HasExpandingIntegerTower ∨
        ∃ O : OddOrbit, Nonempty (CanonicalContractingChain O) := by
  rintro ⟨O, hU⟩
  rcases dichotomy_on_strong O hU with hE | hC
  · rcases hE with ⟨T⟩
    exact Or.inl ⟨ExpandingIntegerTower.ofTower T⟩
  · rcases hC with ⟨D⟩
    right
    exact ⟨O, ⟨CanonicalContractingChain.ofEventuallyContractingTail D hGap⟩⟩

/-- 二整数問題の双方を排除すれば非有界反例は存在しない。 -/
theorem no_unbounded_of_no_integer_obstructions
    (hE : ¬ HasExpandingIntegerTower)
    (hC : ¬ HasContractingIntegerChain) :
    ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases unbounded_to_integer_dichotomy hU with hExp | hCon
  · exact hE hExp
  · exact hC hCon

end IntegerObstruction
end AdjacentReturn
end Collatz
