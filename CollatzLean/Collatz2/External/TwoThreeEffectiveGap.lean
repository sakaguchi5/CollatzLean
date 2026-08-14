import CollatzLean.Collatz2.Arithmetic.ExponentSlope
import CollatzLean.Collatz2.External.TwoThreeGap

/-!
# Collatz2 External: effective 2-3 gap

旧系で使っていた Ellison 型明示入力を Collatz2 側へ再導入する。

外部入力として保留するのは

  H >= 28
  3^p < 2^H
  ----------------
  H <= 2^H - 3^p

だけ。

`H < 28` は Lean 内の有限箱で閉じる。

これにより

  p <= gap

だけでなく、今回の zero-core に必要な

  2 <= p
  ----------------
  19*p < 12*gap

も全長で得る。
-/

namespace Collatz2
namespace External

/-- Ellison 型の明示 2-3 gap 帰結。 -/
def EllisonTwoThreeGapBound : Prop :=
  ∀ p H : ℕ,
    28 ≤ H →
    3 ^ p < 2 ^ H →
    H ≤ 2 ^ H - 3 ^ p

/-- effective gap package。 -/
structure TwoThreeEffectiveGapInput : Prop where
  ellison : EllisonTwoThreeGapBound

/-- 小指数箱の通常 linear gap。 -/
private theorem twoThreeGap_ge_exponent_small_box :
    ∀ p : Fin 18,
    ∀ H : Fin 28,
      3 ^ p.1 < 2 ^ H.1 →
      p.1 ≤ 2 ^ H.1 - 3 ^ p.1 := by
  decide

/--
小指数箱の `19/12` 強化。
唯一の小さい例外 `(p,H)=(1,2)` を `2 <= p` で除く。
-/
private theorem nineteen_mul_exponent_lt_twelve_mul_gap_small_box :
    ∀ p : Fin 18,
    ∀ H : Fin 28,
      2 ≤ p.1 →
      3 ^ p.1 < 2 ^ H.1 →
      19 * p.1 <
        12 * (2 ^ H.1 - 3 ^ p.1) := by
  decide

/-- 同じ自然数指数なら `2^p ≤ 3^p`。 -/
theorem twoPow_le_threePow (p : ℕ) :
    2 ^ p ≤ 3 ^ p := by
  induction p with
  | zero =>
      simp
  | succ p ih =>
      rw [pow_succ, pow_succ]
      exact Nat.mul_le_mul ih (by omega)

/-- contracting なら指数側でも `p < H`。 -/
theorem exponent_lt_twoExponent_of_contracting
    {p H : ℕ}
    (hcontract : 3 ^ p < 2 ^ H) :
    p < H := by
  by_contra hnot
  have hHle : H ≤ p := by
    omega
  have htwoMono :
      2 ^ H ≤ 2 ^ p :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ)) hHle
  have htwoThree :
      2 ^ p ≤ 3 ^ p :=
    twoPow_le_threePow p
  omega

/-- `H < 28` の contracting pair では `p < 18`。 -/
theorem exponent_lt_eighteen_of_twoExponent_lt_28
    {p H : ℕ}
    (hH : H < 28)
    (hcontract : 3 ^ p < 2 ^ H) :
    p < 18 := by
  by_contra hnot
  have hp : 18 ≤ p := by
    omega
  have hHle : H ≤ 27 := by
    omega
  have hthreeMono :
      3 ^ 18 ≤ 3 ^ p :=
    Nat.pow_le_pow_right
      (by omega : 0 < (3 : ℕ)) hp
  have htwoMono :
      2 ^ H ≤ 2 ^ 27 :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ)) hHle
  have hfixed : 2 ^ 27 < 3 ^ 18 := by
    decide
  omega

/-- `H < 28` では外部入力なしで `p <= gap`。 -/
theorem twoThreeGap_ge_exponent_below_28
    {p H : ℕ}
    (hH : H < 28)
    (hcontract : 3 ^ p < 2 ^ H) :
    p ≤ 2 ^ H - 3 ^ p := by
  have hp18 :
      p < 18 :=
    exponent_lt_eighteen_of_twoExponent_lt_28
      hH hcontract
  let pf : Fin 18 := ⟨p, hp18⟩
  let Hf : Fin 28 := ⟨H, hH⟩
  have h :=
    twoThreeGap_ge_exponent_small_box pf Hf
  simpa [pf, Hf] using h hcontract

/-- 全 contracting exponent pair で `p <= gap`。 -/
theorem twoThreeGap_ge_exponent
    (hGap : TwoThreeEffectiveGapInput)
    {p H : ℕ}
    (hcontract : 3 ^ p < 2 ^ H) :
    p ≤ 2 ^ H - 3 ^ p := by
  by_cases hH : H < 28
  · exact
      twoThreeGap_ge_exponent_below_28
        hH hcontract
  · have hH28 : 28 ≤ H := by
      omega
    have hpH :
        p < H :=
      exponent_lt_twoExponent_of_contracting hcontract
    have hEllison :
        H ≤ 2 ^ H - 3 ^ p :=
      hGap.ellison p H hH28 hcontract
    omega

/--
`2 <= p` の contracting exponent pair では

  19*p < 12*(2^H-3^p)

が全長で成立する。

大指数では `19*p < 12*H <= 12*gap`、
小指数では有限箱。
-/
theorem nineteen_mul_exponent_lt_twelve_mul_gap
    (hGap : TwoThreeEffectiveGapInput)
    {p H : ℕ}
    (hpTwo : 2 ≤ p)
    (hcontract : 3 ^ p < 2 ^ H) :
    19 * p <
      12 * (2 ^ H - 3 ^ p) := by
  by_cases hH : H < 28
  · have hp18 :
        p < 18 :=
      exponent_lt_eighteen_of_twoExponent_lt_28
        hH hcontract
    let pf : Fin 18 := ⟨p, hp18⟩
    let Hf : Fin 28 := ⟨H, hH⟩
    have h :=
      nineteen_mul_exponent_lt_twelve_mul_gap_small_box
        pf Hf
    simpa [pf, Hf] using
      h hpTwo hcontract
  · have hH28 : 28 ≤ H := by
      omega
    have hpPos : 0 < p := by
      omega
    have hSlope :
        19 * p < 12 * H :=
      Word.nineteen_mul_lt_twelve_mul_of_threePow_lt_twoPow
        hpPos hcontract
    have hEllison :
        H ≤ 2 ^ H - 3 ^ p :=
      hGap.ellison p H hH28 hcontract
    omega

end External
end Collatz2
