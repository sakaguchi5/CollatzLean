import CollatzLean.Collatz3.CSTConditional.IntegerReduction.InteriorDefectGrowth
import CollatzLean.Collatz3.Canonical.REQ
import CollatzLean.Collatz3.Core.EndpointEquation
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional IntegerReduction: 奇整数 recurrence

独立整数問題側で actual 軌道を使わずに済むよう、
指数列 `e` と奇整数列 `y` の一段関係だけを薄い predicate として置く。

`2^(e_m) y_(m+1) = 3 y_m + 1`。

そこから有限 prefix の affine endpoint equation、canonical residue との一致を
すべて derived theorem として得る。
-/

namespace Collatz3
namespace IntegerReduction

/-- 正指数・奇整数からなる一段 recurrence。 -/
def RunsOddRecurrence
    (e y : ℕ → ℕ) : Prop :=
  ∀ m : ℕ,
    0 < e m ∧
      Odd (y m) ∧
      2 ^ e m * y (m + 1) = 3 * y m + 1

namespace RunsOddRecurrence

/-- exponent は正。 -/
theorem exponent_pos
    {e y : ℕ → ℕ}
    (h : RunsOddRecurrence e y)
    (m : ℕ) :
    0 < e m :=
  (h m).1

/-- 各値は奇数。 -/
theorem value_odd
    {e y : ℕ → ℕ}
    (h : RunsOddRecurrence e y)
    (m : ℕ) :
    Odd (y m) :=
  (h m).2.1

/-- 一段方程式。 -/
theorem equation
    {e y : ℕ → ℕ}
    (h : RunsOddRecurrence e y)
    (m : ℕ) :
    2 ^ e m * y (m + 1) = 3 * y m + 1 :=
  (h m).2.2

/--
有限 prefix の exact affine equation。

`2^D_m y_m = 3^m y_0 + A_m`。
-/
theorem prefixEquation
    {e y : ℕ → ℕ}
    (h : RunsOddRecurrence e y)
    (m : ℕ) :
    2 ^ prefixDepth e m * y m =
      3 ^ m * y 0 + prefixAffine e m := by
  induction m with
  | zero =>
      simp [prefixDepth, prefixAffine, prefixWord]
  | succ m ih =>
      have hStep := h.equation m
      rw [prefixDepth_succ, prefixAffine_succ, pow_add, pow_succ]
      calc
        (2 ^ prefixDepth e m * 2 ^ e m) * y (m + 1)
            = 2 ^ prefixDepth e m *
                (2 ^ e m * y (m + 1)) := by ring
        _ = 2 ^ prefixDepth e m * (3 * y m + 1) := by rw [hStep]
        _ = 3 * (2 ^ prefixDepth e m * y m) +
              2 ^ prefixDepth e m := by ring
        _ = 3 * (3 ^ m * y 0 + prefixAffine e m) +
              2 ^ prefixDepth e m := by rw [ih]
        _ = (3 ^ m * 3) * y 0 +
              (3 * prefixAffine e m + 2 ^ prefixDepth e m) := by ring

/-- finite prefix word は recurrence の endpoint equation を満たす。 -/
theorem prefixEndpointEquation
    {e y : ℕ → ℕ}
    (h : RunsOddRecurrence e y)
    (m : ℕ) :
    (prefixWord e m).EndpointEquation (y 0) (y m) := by
  apply (Word.endpointEquation_iff (prefixWord e m) (y 0) (y m)).2
  have hMain := h.prefixEquation m
  have hOddSteps : Word.oddSteps (prefixWord e m) = m := by
    simp [Word.oddSteps, prefixWord_length]
  change
    2 ^ Word.twoSteps (prefixWord e m) * y m =
      3 ^ Word.oddSteps (prefixWord e m) * y 0 +
        Word.affineConst (prefixWord e m)
  simpa [prefixDepth, prefixAffine, hOddSteps] using hMain

/--
recurrence の初期値を各有限 prefix modulus へ落とすと canonical residue になる。
-/
theorem start_mod_eq_canonicalResidue
    {e y : ℕ → ℕ}
    (h : RunsOddRecurrence e y)
    (m : ℕ) :
    y 0 % 2 ^ (prefixDepth e m + 1) = canonicalResidue e m := by
  have hEndpoint := h.prefixEndpointEquation m
  have hMod := hEndpoint.start_mod_eq_canonicalStart (h.value_odd m)
  have hOddSteps : Word.oddSteps (prefixWord e m) = m := by
    simp [Word.oddSteps, prefixWord_length]
  simpa [
    Word.oddEndpointModulus,
    oddEndpointModulusOfAffineData,
    Arithmetic.twoPowModulus,
    Word.canonicalStart,
    canonicalResidue,
    prefixDepth,
    prefixAffine,
    hOddSteps
  ] using hMod

end RunsOddRecurrence

end IntegerReduction
end Collatz3
