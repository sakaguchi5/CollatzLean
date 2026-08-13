import CollatzLean.Collatz2.Local.Defect
import Mathlib.Tactic.Linarith

/-!
# Collatz2 Native: prepend-one defect geometry

`PrependOne...Data` を先に作らない。
`[1]` の transfer と既存 defect cocycle の特殊化だけを取り出す。

CORE 型条件が必要になった場合も、この exact sign balance の Prop として後から命名する。
-/

namespace Collatz2
namespace Word

/-- `[1]` の start defect は exact に `x + 1`。 -/
@[simp] theorem startDefect_singleton_one (x : ℕ) :
    startDefect ([1] : Word) x = (x : ℤ) + 1 := by
  simp [startDefect, AffineTransfer.startDefect,
    AffineTransfer.determinant, AffineTransfer.ofWord,
    oddSteps, twoSteps, affineConst]
  ring

/--
actual `[1] : x -> y` の後に `v : y -> z` が続くとき、
whole start defect は positive head contribution と tail defect の transported sum。
-/
theorem prependOne_startDefect
    {v : Word} {x y z : ℕ}
    (hOne : Realizes ([1] : Word) x y)
    (hTail : Realizes v y z) :
    startDefect (1 :: v) x =
      ((AffineTransfer.ofWord v).twoCoeff : ℤ) * ((x : ℤ) + 1) +
        2 * startDefect v y := by
  have hCocycle :=
    AffineTransfer.Realizes.startDefect_followedBy
      (T := AffineTransfer.ofWord ([1] : Word))
      (U := AffineTransfer.ofWord v)
      hOne hTail
  have hAppend :
      AffineTransfer.ofWord (1 :: v) =
        (AffineTransfer.ofWord ([1] : Word)).followedBy
          (AffineTransfer.ofWord v) := by
    simpa using AffineTransfer.ofWord_append ([1] : Word) v
  change (AffineTransfer.ofWord (1 :: v)).startDefect x = _
  rw [hAppend]
  calc
    ((AffineTransfer.ofWord ([1] : Word)).followedBy
        (AffineTransfer.ofWord v)).startDefect x
        =
        ((AffineTransfer.ofWord v).twoCoeff : ℤ) *
            (AffineTransfer.ofWord ([1] : Word)).startDefect x +
          ((AffineTransfer.ofWord ([1] : Word)).twoCoeff : ℤ) *
            (AffineTransfer.ofWord v).startDefect y := hCocycle
    _ =
        ((AffineTransfer.ofWord v).twoCoeff : ℤ) * ((x : ℤ) + 1) +
          2 * startDefect v y := by
            simp [startDefect, AffineTransfer.startDefect,
              AffineTransfer.determinant, AffineTransfer.ofWord,
              oddSteps, twoSteps, affineConst]
            ring

/--
whole defect が正なら、

`-(2 * tailDefect) < tailTwoCoeff * (x + 1)`

が成り立つ。

これは `[1]` head contribution と tail defect の競合を、
旧 CORE Data を介さず直接表す基本不等式。
-/
theorem tail_defect_bound_of_prependOne_positive
    {v : Word} {x y z : ℕ}
    (hOne : Realizes ([1] : Word) x y)
    (hTail : Realizes v y z)
    (hWhole : 0 < startDefect (1 :: v) x) :
    -(2 * startDefect v y) <
      ((AffineTransfer.ofWord v).twoCoeff : ℤ) * ((x : ℤ) + 1) := by
  rw [prependOne_startDefect hOne hTail] at hWhole
  linarith

end Word
end Collatz2
