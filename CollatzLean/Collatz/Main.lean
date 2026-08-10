import CollatzLean.Collatz.AdjacentReturn.Dichotomy
import CollatzLean.Collatz.AdjacentReturn.PositiveReturn.Global
import CollatzLean.Collatz.Canonical.Residue
import CollatzLean.Collatz.FiniteOrbit.Comparison
import CollatzLean.Collatz.Word.Center
import CollatzLean.Collatz.Word.Kernel
import CollatzLean.Collatz.FiniteOrbit.Trajectory

/-!
# Collatz proof core

無条件の公開分岐は Adjacent Return の expanding / contracting 二枝を維持する。
Baker/canonical route では contracting 側の最上位 obstruction を
Exact/Late や CORE ではなく positive canonical return chain とする。
-/

namespace Collatz

/-- expanding adjacent tower排除原理。 -/
def AdjacentReturn.ExpandingExclusion : Prop :=
  ¬ AdjacentReturn.HasExpandingTower

/-- contracting adjacent tower排除原理。 -/
def AdjacentReturn.ContractingExclusion : Prop :=
  ¬ AdjacentReturn.HasContractingTower

/-- 発散側の無条件最終目標。 -/
def ActualReturnMainTarget : Prop :=
  AdjacentReturn.ExpandingExclusion ∧ AdjacentReturn.ContractingExclusion

/-- 二つの隣接return枝を排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit
    (h : ActualReturnMainTarget) : ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases AdjacentReturn.dichotomy hU with hE | hC
  · exact h.1 hE
  · exact h.2 hC

/-- Baker/canonical route の contracting 側排除目標。 -/
def AdjacentReturn.PositiveReturnExclusion : Prop :=
  ¬ AdjacentReturn.PositiveReturn.HasCanonicalChain

/--
Baker/canonical route の最終目標。
contracting 側では positive canonical return chain の不存在だけを正本に露出させる。
-/
def CanonicalPositiveReturnMainTarget : Prop :=
  (¬ AdjacentReturn.IntegerObstruction.HasExpandingIntegerTower) ∧
    AdjacentReturn.PositiveReturnExclusion

/-- positive-return 正本の二 obstruction を排除すれば非有界odd-only軌道はない。 -/
theorem no_unbounded_odd_orbit_of_positiveReturn
    (hGap : External.TwoThreeGapPolynomialBound)
    (h : CanonicalPositiveReturnMainTarget) :
    ¬ HasUnboundedOddOrbit := by
  exact
    AdjacentReturn.PositiveReturn.no_unbounded_of_no_expanding_no_positive
      hGap h.1 h.2

end Collatz
