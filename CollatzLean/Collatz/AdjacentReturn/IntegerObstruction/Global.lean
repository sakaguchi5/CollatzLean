import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Expanding
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Contracting
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Late
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Primitive
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Barrier
import CollatzLean.Collatz.AdjacentReturn.IntegerObstruction.Canonical
import CollatzLean.Collatz.AdjacentReturn.CanonicalContractingChain

/-!
# 非有界反例から二整数問題への最終境界

今後の正本を expanding / eventually-contracting の二整数問題に固定する。
細かい枝はこの二つの解集合への追加条件として扱う。

さらに Late / primitive / backward-barrier / canonical の各 refinement を
依存関係を保ったまま積み上げるための最終インターフェースを置く。
-/

namespace Collatz
namespace AdjacentReturn
namespace IntegerObstruction

/-- 標準 adjacent return の連続純整数 chain が存在する。 -/
def HasAdjacentIntegerChain : Prop :=
  Nonempty AdjacentIntegerChain

/-- 非有界 odd 軌道から、分岐前の共通連続整数 chain を得る。 -/
theorem unbounded_to_adjacentIntegerChain :
    HasUnboundedOddOrbit → HasAdjacentIntegerChain := by
  rintro ⟨O, hU⟩
  exact ⟨AdjacentIntegerChain.ofUnboundedOrbit O hU⟩

/-- expanding 側の純整数 obstruction が存在する。 -/
def HasExpandingIntegerTower : Prop :=
  Nonempty ExpandingIntegerTower

/-- eventually-contracting 側の純整数 obstruction が存在する。 -/
def HasContractingIntegerChain : Prop :=
  Nonempty ContractingIntegerChain

/-- expanding obstruction は共通連続 chain を保持する。 -/
theorem expanding_has_adjacentIntegerChain
    (hE : HasExpandingIntegerTower) :
    HasAdjacentIntegerChain := by
  rcases hE with ⟨T⟩
  exact ⟨T.chain⟩

/-- contracting obstruction も共通連続 chain を保持する。 -/
theorem contracting_has_adjacentIntegerChain
    (hC : HasContractingIntegerChain) :
    HasAdjacentIntegerChain := by
  rcases hC with ⟨C⟩
  exact ⟨C.chain⟩

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

/--
contracting integer chain に Late primitive・barrier・canonical の全 refinement を積んだ最終対象。

各追加条件の出自は別ファイルに分離し、この structure は合流点だけを担う。
-/
structure RefinedContractingIntegerChain (bound : ℕ) where
  core : ContractingIntegerChain
  barrier : ReverseBarrier bound core.chain
  primitiveLate :
    ∀ n : ℕ,
    ∀ L : LateBlockArithmeticData (core.block n),
      L.crossing = core.firstCrossing n →
        Nonempty (PrimitiveLateConstraintData L)
  canonical : CanonicalIntegerRefinement core

/-- 全 refinement を持つ contracting obstruction が存在すること。 -/
def HasRefinedContractingIntegerChain (bound : ℕ) : Prop :=
  Nonempty (RefinedContractingIntegerChain bound)

/-- refined contracting obstruction は元の core obstruction を忘却できる。 -/
theorem refinedContracting_has_core
    {bound : ℕ}
    (h : HasRefinedContractingIntegerChain bound) :
    HasContractingIntegerChain := by
  rcases h with ⟨R⟩
  exact ⟨R.core⟩

/-- barrier expanding obstruction は元の expanding obstruction を忘却できる。 -/
theorem barrierExpanding_has_core
    {bound : ℕ}
    (h : HasBarrierExpandingIntegerTower bound) :
    HasExpandingIntegerTower := by
  rcases h with ⟨R⟩
  exact ⟨R.core⟩

/--
各 refinement の供給 theorem が得られた時点で、既存の二整数分岐を
barrier expanding / fully-refined contracting 分岐へそのまま持ち上げる。

`hExpBarrier` は計算検証などの backward barrier 層、
`hConPrimitive` は Late/Coprime 層、`hConCanonical` は Baker/canonical 層を
それぞれ独立に供給するためのインターフェースである。
-/
theorem unbounded_to_refined_integer_dichotomy
    {bound : ℕ}
    (hExpBarrier :
      ∀ T : ExpandingIntegerTower,
        ReverseBarrier bound T.chain)
    (hConBarrier :
      ∀ C : ContractingIntegerChain,
        ReverseBarrier bound C.chain)
    (hConPrimitive :
      ∀ C : ContractingIntegerChain,
      ∀ n : ℕ,
      ∀ L : LateBlockArithmeticData (C.block n),
        L.crossing = C.firstCrossing n →
          Nonempty (PrimitiveLateConstraintData L))
    (hConCanonical :
      ∀ C : ContractingIntegerChain,
        CanonicalIntegerRefinement C) :
    HasUnboundedOddOrbit →
      HasBarrierExpandingIntegerTower bound ∨
        HasRefinedContractingIntegerChain bound := by
  intro hU
  rcases unbounded_to_integer_dichotomy hU with hE | hC
  · rcases hE with ⟨T⟩
    left
    exact ⟨⟨T, hExpBarrier T⟩⟩
  · rcases hC with ⟨C⟩
    right
    exact
      ⟨{
        core := C
        barrier := hConBarrier C
        primitiveLate := hConPrimitive C
        canonical := hConCanonical C
      }⟩

end IntegerObstruction
end AdjacentReturn
end Collatz
