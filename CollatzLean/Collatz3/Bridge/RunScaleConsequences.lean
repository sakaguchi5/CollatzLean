import CollatzLean.Collatz3.Core.WordScale

import CollatzLean.Collatz3.Bridge.RunsToCanonical
import CollatzLean.Collatz3.Semantics.ReachOne
import CollatzLean.Collatz3.Semantics.OrbitReturn

/-!
# Collatz3: actual run の contracting scale consequence

非空 actual run が endpoint で開始値以下へ戻るなら、正の affine translation のため
`2^H` は `3^p` より strict に大きくなければならない。
-/

namespace Collatz3
namespace Runs

/--
非空 actual run `x -> y` で `y ≤ x` なら `3^p < 2^H`。
これは endpoint equation と `B>0` だけから従う一般形。
-/
theorem threePow_lt_twoPow_of_end_le_start
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hne : w ≠ [])
    (hyx : y ≤ x) :
    3 ^ Word.oddSteps w < 2 ^ Word.twoSteps w := by
  have hEq :
      2 ^ Word.twoSteps w * y =
        3 ^ Word.oddSteps w * x + Word.affineConst w :=
    (Word.endpointEquation_iff w x y).1 h.endpointEquation
  have hBPos : 0 < Word.affineConst w :=
    Word.affineConst_pos_of_nonempty hne
  by_contra hNot
  have hScale :
      2 ^ Word.twoSteps w ≤ 3 ^ Word.oddSteps w :=
    Nat.le_of_not_gt hNot
  have hLeft :
      2 ^ Word.twoSteps w * y ≤
        2 ^ Word.twoSteps w * x :=
    Nat.mul_le_mul_left _ hyx
  have hRight :
      2 ^ Word.twoSteps w * x ≤
        3 ^ Word.oddSteps w * x :=
    Nat.mul_le_mul_right x hScale
  have hContr :
      2 ^ Word.twoSteps w * y ≤
        3 ^ Word.oddSteps w * x :=
    le_trans hLeft hRight
  rw [hEq] at hContr
  omega

end Runs

namespace OrbitReturn

/-- actual return では必ず `3^p < 2^H`。 -/
theorem threePow_lt_twoPow
    {w : Word} {x : ℕ}
    (h : ReturnsTo w x) :
    3 ^ Word.oddSteps w < 2 ^ Word.twoSteps w :=
  Runs.threePow_lt_twoPow_of_end_le_start
    h.run h.word_nonempty (Nat.le_refl x)

end OrbitReturn

namespace FirstHitsOne

/-- `1` への first hit でも `3^p < 2^H`。 -/
theorem threePow_lt_twoPow
    {w : Word} {x : ℕ}
    (h : FirstHitsOne w x) :
    3 ^ Word.oddSteps w < 2 ^ Word.twoSteps w := by
  have hxOdd :=
    Runs.start_odd_of_nonempty h.endsAtOne h.word_nonempty
  have hxOne : 1 ≤ x := by
    rcases hxOdd with ⟨k, hk⟩
    omega
  exact
    Runs.threePow_lt_twoPow_of_end_le_start
      h.endsAtOne h.word_nonempty hxOne

end FirstHitsOne
end Collatz3
