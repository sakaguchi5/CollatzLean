import CollatzLean.Collatz3.External.BakerWustholz

/-!
# Baker--Wüstholz 四対数の有理数特殊化

A1 では三対数

`a log 2 + ε log α - k log 3`

だけを trusted input として残している。

A2 target-large の variable-period window では、Stephan の gap principle に現れる

`log G + m log 3 - y log 2 - log A`

という四対数形が必要になる。ここでは一般 number field / 任意個数の対数へ戻さず、
数体 `ℚ`、係数 `(1,m,-y,-1)` の形だけを trusted theorem として追加する。

Collatz equation、Mersenne normal form、hole、depth bound は一切仮定しない。
-/

namespace BakerWustholz

/--
A2 variable-period proof が必要とする四対数形。

`G,A > 0` を想定し、

`log G + m log 3 - y log 2 - log A`

を表す。
-/
noncomputable def fourLogRatForm
    (G A : ℚ) (m y : ℕ) : ℝ :=
  Real.log (G : ℝ) +
    (m : ℝ) * Real.log 3 -
    (y : ℝ) * Real.log 2 -
    Real.log (A : ℝ)

/--
Baker--Wüstholz [BW93] のうち、A2 variable-period engine が使う
有理数四対数特殊化。

基数は `(G,3,2,A)`、係数は `(1,m,-y,-1)` に固定する。
-/
axiom linearForms_logs_four_rat
    {m y B : ℕ}
    (G A : ℚ)
    (hG : 0 < G)
    (hA : 0 < A)
    (hB : 2 ≤ B)
    (hmB : m ≤ B)
    (hyB : y ≤ B)
    (hΛ_ne_zero : fourLogRatForm G A m y ≠ 0) :
    -(BakerWustholz.C 4 1 * max (Real.log B) 1 *
        (BakerWustholz.modifiedHeight (Rat.castHom ℂ) G *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ) (3 : ℚ) *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ) (2 : ℚ) *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ) A))
      ≤ Real.log |fourLogRatForm G A m y|

end BakerWustholz

namespace Collatz3
namespace External
namespace BakerWustholzFourQ

/--
正の四対数線形形式に使いやすい wrapper。

この theorem 自身は axiom ではなく、
`BakerWustholz.linearForms_logs_four_rat` の単純な特殊化。
-/
theorem log_fourForm_rat_ge
    {m y B : ℕ}
    {G A : ℚ}
    (hG : 0 < G)
    (hA : 0 < A)
    (hB : 2 ≤ B)
    (hmB : m ≤ B)
    (hyB : y ≤ B)
    {Λ : ℝ}
    (hΛeq : Λ = BakerWustholz.fourLogRatForm G A m y)
    (hΛPos : 0 < Λ) :
    -(BakerWustholz.C 4 1 * max (Real.log B) 1 *
        (BakerWustholz.modifiedHeight (Rat.castHom ℂ) G *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ) (3 : ℚ) *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ) (2 : ℚ) *
          BakerWustholz.modifiedHeight (Rat.castHom ℂ) A))
      ≤ Real.log Λ := by
  have hFormPos :
      0 < BakerWustholz.fourLogRatForm G A m y := by
    rw [← hΛeq]
    exact hΛPos
  have hBW :=
    BakerWustholz.linearForms_logs_four_rat
      (m := m) (y := y) (B := B)
      G A hG hA hB hmB hyB hFormPos.ne'
  rw [abs_of_pos hFormPos] at hBW
  rw [← hΛeq] at hBW
  exact hBW

end BakerWustholzFourQ
end External
end Collatz3
