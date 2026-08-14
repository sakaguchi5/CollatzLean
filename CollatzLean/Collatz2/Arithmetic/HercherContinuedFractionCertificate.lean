import Mathlib.Data.Nat.Factorization.Defs

/-!
# Collatz2 Arithmetic: Hercher `2^71` continued-fraction finite certificate

`delta = log(3)/log(2)` と

  delta + 1/(3*2^71*log 2)

の continued fraction は最初の22項を共有し、次の partial quotient が
それぞれ 9 と 10 になる。
Hercher Lemma 22 では `min(9,10)+1 = 10` を境界係数として使う。

このファイルは、その有限 continued-fraction candidate の numerator / denominator
計算だけを Lean 内で証明する。
real logarithm側の interval containment は `External.BarinaHercher` に隔離する。
-/

namespace Collatz2
namespace Arithmetic

/-- continued fraction の `(numerator, denominator)` recurrence。 -/
def cfStep
    (state : (ℕ × ℕ) × (ℕ × ℕ))
    (a : ℕ) : (ℕ × ℕ) × (ℕ × ℕ) :=
  let ⟨prevprev, prev⟩ := state
  let next : ℕ × ℕ :=
    (a * prev.1 + prevprev.1,
      a * prev.2 + prevprev.2)
  (prev, next)

/-- finite simple continued fraction の numerator / denominator。 -/
def cfValuePair (xs : List ℕ) : ℕ × ℕ :=
  ((xs.foldl cfStep ((0, 1), (1, 0))).2)

/-- denominator。 -/
def cfDenominator (xs : List ℕ) : ℕ :=
  (cfValuePair xs).2

/-- numerator。 -/
def cfNumerator (xs : List ℕ) : ℕ :=
  (cfValuePair xs).1

/-- `delta` と upper endpoint が共有する prefix。 -/
def hercherTwoPow71CommonPrefix : List ℕ :=
  [1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2,
    1, 1, 55, 1, 4, 3, 1, 1, 15, 1]

/-- Lemma 22 の boundary coefficient `min(9,10)+1 = 10`。 -/
def hercherTwoPow71BoundaryCF : List ℕ :=
  hercherTwoPow71CommonPrefix ++ [10]

/-- finite CF candidate の numerator は exact に 114208327604。 -/
theorem hercherTwoPow71_numerator_eq :
    cfNumerator hercherTwoPow71BoundaryCF =
      114208327604 := by
  decide

/-- finite CF candidate の denominator は exact に 72057431991。 -/
theorem hercherTwoPow71_denominator_eq :
    cfDenominator hercherTwoPow71BoundaryCF =
      72057431991 := by
  decide

/-- numerator / denominator を同時に固定。 -/
theorem hercherTwoPow71_fraction_eq :
    cfValuePair hercherTwoPow71BoundaryCF =
      (114208327604, 72057431991) := by
  decide

end Arithmetic
end Collatz2
