import CollatzLean.Collatz.OddOrbit.Selection
import CollatzLean.Collatz.OddOrbit.StandardFutureMinimum

/-!
# 標準future-minimum選択の隣接性

noncomputableな標準選択が、選択後には`FutureMinima.IsStandard`を満たすことだけを
selection adapterとして証明する。
-/

namespace Collatz
namespace OddOrbit
namespace Selection

/-- tail minimumを再帰選択した標準列はIsStandard。 -/
theorem futureMinima_isStandard
    (O : OddOrbit) (hU : O.Unbounded) :
    (futureMinima O hU).IsStandard := by
  intro j t ht
  have ht' :
      futureMinIndex O j + 1 ≤ t := by
    change futureMinIndex O j < t at ht
    exact Nat.succ_le_of_lt ht
  change
    O.value (tailMinIndex O (futureMinIndex O j + 1)) ≤
      O.value t
  rw [value_tailMinIndex]
  exact tailMinValue_le
    O
    (futureMinIndex O j + 1)
    t
    ht'

end Selection
end OddOrbit
end Collatz
