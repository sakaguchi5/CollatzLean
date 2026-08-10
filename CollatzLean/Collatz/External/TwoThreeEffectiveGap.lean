import CollatzLean.Collatz.External.TwoThreeGap

/-!
# 2と3のgapに対するEllison型明示入力

`TwoThreeGapPolynomialBound` は十分大きい指数でのBaker型gapを与えるが、
このファイルでは positive replay quotient を全長で閉じるため、
Ellison の2冪・3冪に対する明示評価の算術帰結を外部入力として採用する。

外部入力として保留するのは `H >= 28` の部分だけである。
`H < 28` では contracting 条件から自動的に `p < 18` となり、
残る `Fin 18 × Fin 28` の有限箱はLean内で直接検証する。

Ellison評価そのものの形式化は後回しにし、ここでは
Collatz語に依存しない純粋な2冪・3冪命題として隔離する。
-/

namespace Collatz
namespace External

/--
Ellison の明示的2-3 gap評価から使用する算術帰結。

`H >= 28` かつ `3^p < 2^H` なら、正のgap `2^H - 3^p` は
少なくとも `H` 以上であるとする。
この命題の外部数学的証明は後で形式化する。
-/
def EllisonTwoThreeGapBound : Prop :=
  ∀ p H : ℕ,
    28 ≤ H →
    3 ^ p < 2 ^ H →
      H ≤ 2 ^ H - 3 ^ p

/--
CORE positive quotient 排除に使うeffective 2-3 gap package。
未証明の外部入力はEllison型明示評価だけに限定する。
-/
structure TwoThreeEffectiveGapInput : Prop where
  ellison : EllisonTwoThreeGapBound

/-- `p < 18`, `H < 28` の有限箱では線形gapが直接成立する。 -/
private theorem twoThreeGap_ge_exponent_small_box :
    ∀ p : Fin 18,
    ∀ H : Fin 28,
      3 ^ p.1 < 2 ^ H.1 →
        p.1 ≤ 2 ^ H.1 - 3 ^ p.1 := by
  decide

/-- contracting なら指数側でも `p < H`。 -/
theorem exponent_lt_twoExponent_of_contracting
    {p H : ℕ}
    (hcontract : 3 ^ p < 2 ^ H) :
    p < H := by
  by_contra hnot
  have hHle : H ≤ p := by omega
  have htwoMono : 2 ^ H ≤ 2 ^ p :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hHle
  have htwoThree : 2 ^ p ≤ 3 ^ p :=
    Arithmetic.twoPow_le_threePow p
  omega

/-- `H < 28` の contracting pair では自動的に `p < 18`。 -/
theorem exponent_lt_eighteen_of_twoExponent_lt_28
    {p H : ℕ}
    (hH : H < 28)
    (hcontract : 3 ^ p < 2 ^ H) :
    p < 18 := by
  by_contra hnot
  have hp : 18 ≤ p := by omega
  have hHle : H ≤ 27 := by omega
  have hthreeMono : 3 ^ 18 ≤ 3 ^ p :=
    Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hp
  have htwoMono : 2 ^ H ≤ 2 ^ 27 :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hHle
  have hfixed : 2 ^ 27 < 3 ^ 18 := by
    decide
  omega

/--
`H < 28` では外部入力なしで線形gapが成立する。
contracting から `p < 18` を得て、小さな有限箱へ落とす。
-/
theorem twoThreeGap_ge_exponent_below_28
    {p H : ℕ}
    (hH : H < 28)
    (hcontract : 3 ^ p < 2 ^ H) :
    p ≤ 2 ^ H - 3 ^ p := by
  have hp : p < 18 :=
    exponent_lt_eighteen_of_twoExponent_lt_28 hH hcontract
  let pf : Fin 18 := ⟨p, hp⟩
  let Hf : Fin 28 := ⟨H, hH⟩
  have h := twoThreeGap_ge_exponent_small_box pf Hf
  simpa [pf, Hf] using h hcontract

/--
Ellison型外部入力とLean内有限検証を合わせると、
全 contracting exponent pair で `p <= 2^H - 3^p` が成立する。
-/
theorem twoThreeGap_ge_exponent
    (hGap : TwoThreeEffectiveGapInput)
    {p H : ℕ}
    (hcontract : 3 ^ p < 2 ^ H) :
    p ≤ 2 ^ H - 3 ^ p := by
  by_cases hH : H < 28
  · exact twoThreeGap_ge_exponent_below_28 hH hcontract
  · have hH28 : 28 ≤ H := by omega
    have hpH : p < H :=
      exponent_lt_twoExponent_of_contracting hcontract
    have hEllison : H ≤ 2 ^ H - 3 ^ p :=
      hGap.ellison p H hH28 hcontract
    omega

end External
end Collatz
