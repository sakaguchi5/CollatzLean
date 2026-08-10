import CollatzLean.Collatz.External.TwoThreeGap

set_option linter.style.nativeDecide false
set_option exponentiation.threshold 312
/-!
# 2と3のgapに対するeffective外部入力

既存の `TwoThreeGapPolynomialBound` は定数の存在だけを保持するため、
「十分大きい」側は閉じられても、その cutoff 未満をLean内で有限確認するための
具体的な境界を取り出せない。

ここでは外部超越数論入力を一段だけeffectiveにし、
`p >= 197` では `p <= 2^H - 3^p` が成立することを明示的に要求する。
`p < 197` 側は外部仮定にせず、このファイル内で有限計算により検証する。

`197` は外部入力と有限検証を接続するための公開 cutoff であり、
このファイルより上のCollatz構造には依存しない。
-/

namespace Collatz
namespace External

/--
既存のBaker型多項式gap入力に、明示cutoff以後の線形gapを加えたeffective package。

`linear_from_197` は純粋な2冪・3冪命題であり、Collatz語には依存しない。
-/
structure TwoThreeEffectiveGapInput : Prop where
  polynomial : TwoThreeGapPolynomialBound
  linear_from_197 :
    ∀ p H : ℕ,
      197 ≤ p →
      3 ^ p < 2 ^ H →
        p ≤ 2 ^ H - 3 ^ p

/-- `p < 197`, `H < 312` の有限領域では線形gapが直接成立する。 -/
private theorem twoThreeGap_ge_exponent_small_box :
    ∀ p : Fin 197,
    ∀ H : Fin 312,
      3 ^ p.1 < 2 ^ H.1 →
        p.1 ≤ 2 ^ H.1 - 3 ^ p.1 := by
  native_decide

/--
`p < 197` では `H` に上限を仮定せず線形gapが成立する。
`H < 312` は有限計算、`312 <= H` は単調性と固定数値評価で処理する。
-/
theorem twoThreeGap_ge_exponent_below_197
    {p H : ℕ}
    (hp : p < 197)
    (hcontract : 3 ^ p < 2 ^ H) :
    p ≤ 2 ^ H - 3 ^ p := by
  by_cases hH : H < 312
  · let pf : Fin 197 := ⟨p, hp⟩
    let Hf : Fin 312 := ⟨H, hH⟩
    have h := twoThreeGap_ge_exponent_small_box pf Hf
    simpa [pf, Hf] using h hcontract
  · have hpLe : p ≤ 196 := by omega
    have hHLe : 312 ≤ H := by omega
    have hthree : 3 ^ p ≤ 3 ^ 196 :=
      Nat.pow_le_pow_right (by omega : 0 < (3 : ℕ)) hpLe
    have htwo : 2 ^ 312 ≤ 2 ^ H :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hHLe
    have hfixed : 196 + 3 ^ 196 < 2 ^ 312 := by
      decide
    have hsum : p + 3 ^ p ≤ 2 ^ H := by
      omega
    omega

/--
effective外部入力とLean内有限検証を合わせると、全指数で線形gapが成立する。
-/
theorem twoThreeGap_ge_exponent
    (hGap : TwoThreeEffectiveGapInput)
    {p H : ℕ}
    (hcontract : 3 ^ p < 2 ^ H) :
    p ≤ 2 ^ H - 3 ^ p := by
  by_cases hp : p < 197
  · exact twoThreeGap_ge_exponent_below_197 hp hcontract
  · exact hGap.linear_from_197 p H (by omega) hcontract

end External
end Collatz
