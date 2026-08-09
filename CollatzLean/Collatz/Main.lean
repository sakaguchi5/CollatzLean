import CollatzLean.Collatz.AdjacentReturn.Dichotomy
import CollatzLean.Collatz.Canonical.Residue
import CollatzLean.Collatz.FiniteOrbit.Comparison
import CollatzLean.Collatz.Word.Center
import CollatzLean.Collatz.Word.Kernel
import CollatzLean.Collatz.FiniteOrbit.Trajectory

/-!
# Collatz proof core

発散側の公開分岐はAdjacent Returnの二枝だけとする。
Special C3 / negative shadow / terminal normalizationの旧歴史枝は正本から外す。
-/

namespace Collatz

/-- expanding adjacent tower排除原理。 -/
def AdjacentReturn.ExpandingExclusion : Prop :=
  ¬ AdjacentReturn.HasExpandingTower

/-- contracting adjacent tower排除原理。 -/
def AdjacentReturn.ContractingExclusion : Prop :=
  ¬ AdjacentReturn.HasContractingTower

/-- 発散側最終目標。 -/
def ActualReturnMainTarget : Prop :=
  AdjacentReturn.ExpandingExclusion ∧ AdjacentReturn.ContractingExclusion

/-- 二つの隣接return枝を排除すれば非有界odd-only軌道は存在しない。 -/
theorem no_unbounded_odd_orbit
    (h : ActualReturnMainTarget) : ¬ HasUnboundedOddOrbit := by
  intro hU
  rcases AdjacentReturn.dichotomy hU with hE | hC
  · exact h.1 hE
  · exact h.2 hC

end Collatz
