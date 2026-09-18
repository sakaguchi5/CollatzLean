import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Collatz3 Arithmetic: `3` の `2` 冪法における位数

no-hole source-one residual では

`3^m = 2^r(2^L-1)+1`

から `3^m = 1 (mod 2^r)` が現れる。
このとき必要なのは、`r ≥ 3` に対する classical な事実

`ord_(2^r)(3) = 2^(r-2)`

だけである。

このファイルでは LTE を primitive として持ち込まず、

`3^(2^(r-2)) = 1 + 2^r * q`, `q` odd

という exact witness を帰納的に作り、そこから multiplicative order を導く。
後段では `orderOf` の詳細を忘れ、`3^m = 1 (mod 2^r)` なら
`2^(r-2) ∣ m` という形だけを使える。
-/

namespace Collatz3
namespace Arithmetic

/--
`r ≥ 3` なら

`3^(2^(r-2)) = 1 + 2^r*q`

となる odd `q` が存在する。

これは `v₂(3^(2^(r-2))-1)=r` の valuation を使わない exact 版。
-/
theorem exists_oddQuotient_threePow_twoPow
    (r : ℕ)
    (hr : 3 ≤ r) :
    ∃ q : ℕ,
      q % 2 = 1 ∧
      3 ^ (2 ^ (r - 2)) = 1 + 2 ^ r * q := by
  induction r, hr using Nat.le_induction with
  | base =>
      exact ⟨1, by decide, by norm_num⟩
  | succ r hr ih =>
      rcases ih with ⟨q, hqOdd, hqEq⟩
      let q' : ℕ := q + 2 ^ (r - 1) * q ^ 2
      refine ⟨q', ?_, ?_⟩
      · have hPowDvd : 2 ∣ 2 ^ (r - 1) * q ^ 2 := by
          apply dvd_mul_of_dvd_left
          exact pow_dvd_pow 2 (by omega : 1 ≤ r - 1)
        have hPowMod : (2 ^ (r - 1) * q ^ 2) % 2 = 0 :=
          Nat.mod_eq_zero_of_dvd hPowDvd
        simp [q', Nat.add_mod, hqOdd, hPowMod]
      · have hExp :
            2 ^ ((r + 1) - 2) = 2 ^ (r - 2) * 2 := by
          rw [show (r + 1) - 2 = (r - 2) + 1 by omega, pow_succ]
        have hPowN : 2 ^ r = 2 ^ (r - 1) * 2 := by
          rw [show r = (r - 1) + 1 by omega, pow_succ]
          simp
        have hPowSucc : 2 ^ (r + 1) = 2 ^ (r - 1) * 4 := by
          rw [show r + 1 = (r - 1) + 2 by omega, pow_add]
          norm_num
        rw [hExp, pow_mul, hqEq, hPowN, hPowSucc]
        dsimp [q']
        ring

/--
上の exact witness は一段高い `2` 冪では消えない。

`r ≥ 3` なら

`2^(r+1) ∤ 3^(2^(r-2)) - 1`。
-/
theorem threePow_twoPow_not_dvd_next
    (r : ℕ)
    (hr : 3 ≤ r) :
    ¬ 2 ^ (r + 1) ∣ 3 ^ (2 ^ (r - 2)) - 1 := by
  rcases exists_oddQuotient_threePow_twoPow r hr with
    ⟨q, hqOdd, hEq⟩
  have hSub :
      3 ^ (2 ^ (r - 2)) - 1 = 2 ^ r * q := by
    omega
  intro hDvd
  rw [hSub, show 2 ^ (r + 1) = 2 ^ r * 2 by rw [pow_succ]] at hDvd
  have hTwoDvd : 2 ∣ q := by
    exact (Nat.mul_dvd_mul_iff_left (by positivity : 0 < 2 ^ r)).mp hDvd
  have hModZero : q % 2 = 0 := Nat.mod_eq_zero_of_dvd hTwoDvd
  omega

/-- `3^(2^(r-2)) = 1 (mod 2^r)`。 -/
theorem threePow_twoPow_modEq_one
    (r : ℕ)
    (hr : 3 ≤ r) :
    3 ^ (2 ^ (r - 2)) ≡ 1 [MOD 2 ^ r] := by
  rcases exists_oddQuotient_threePow_twoPow r hr with
    ⟨q, _hqOdd, hEq⟩
  rw [Nat.modEq_iff_dvd]
  have hEqZ :
      (3 : ℤ) ^ (2 ^ (r - 2)) =
        1 + (2 : ℤ) ^ r * (q : ℤ) := by
    exact_mod_cast hEq
  refine ⟨-(q : ℤ), ?_⟩
  push_cast
  rw [hEqZ]
  ring

/--
法を `2^r` から `2^(r+1)` に上げると、
`3` の古い multiplicative order は新しい order を割る。
-/
private theorem orderOf_three_zmod_twoPow_dvd_succ
    (r : ℕ) :
    orderOf (3 : ZMod (2 ^ r)) ∣
      orderOf (3 : ZMod (2 ^ (r + 1))) := by
  rw [orderOf_dvd_iff_pow_eq_one]
  have hOrderSucc :
      3 ^ orderOf (3 : ZMod (2 ^ (r + 1)))
        ≡ 1 [MOD 2 ^ (r + 1)] := by
    simp +decide [
      ← ZMod.natCast_eq_natCast_iff,
      pow_orderOf_eq_one
    ]
  have hModDvd :
      2 ^ r ∣ 2 ^ (r + 1) :=
    pow_dvd_pow 2 (by omega)
  have hOrderCurrent :=
    hOrderSucc.of_dvd hModDvd
  simpa [← ZMod.natCast_eq_natCast_iff] using hOrderCurrent


/--
`r ≥ 3` で現在の order が `2^(r-2)` なら、
次の法 `2^(r+1)` における order は現在の order の 2 倍を割る。
-/
private theorem orderOf_three_zmod_twoPow_succ_dvd_double
    (r : ℕ)
    (hr : 3 ≤ r)
    (hOrder :
      orderOf (3 : ZMod (2 ^ r)) = 2 ^ (r - 2)) :
    orderOf (3 : ZMod (2 ^ (r + 1))) ∣
      orderOf (3 : ZMod (2 ^ r)) * 2 := by
  rw [orderOf_dvd_iff_pow_eq_one]
  have hWitness :=
    threePow_twoPow_modEq_one (r + 1) (by omega)
  have hExp :
      orderOf (3 : ZMod (2 ^ r)) * 2 =
        2 ^ ((r + 1) - 2) := by
    rw [hOrder]
    rw [show (r + 1) - 2 = (r - 2) + 1 by omega]
    rw [pow_succ]
  rw [hExp]
  simpa [← ZMod.natCast_eq_natCast_iff] using hWitness


/--
`r ≥ 3` では、法を `2^r` から `2^(r+1)` に上げたとき
`3` の multiplicative order は同じ値には留まらない。

exact quotient が奇数であることから、
古い order の指数では `mod 2^(r+1)` でまだ 1 にならない。
-/
private theorem orderOf_three_zmod_twoPow_succ_ne_current
    (r : ℕ)
    (hr : 3 ≤ r)
    (hOrder :
      orderOf (3 : ZMod (2 ^ r)) = 2 ^ (r - 2)) :
    orderOf (3 : ZMod (2 ^ (r + 1))) ≠
      orderOf (3 : ZMod (2 ^ r)) := by
  intro hSame
  have hPow :
      (3 : ZMod (2 ^ (r + 1))) ^
          orderOf (3 : ZMod (2 ^ r)) = 1 := by
    rw [← hSame]
    exact pow_orderOf_eq_one _
  have hMod :
      3 ^ orderOf (3 : ZMod (2 ^ r))
        ≡ 1 [MOD 2 ^ (r + 1)] := by
    simpa [← ZMod.natCast_eq_natCast_iff] using hPow
  rw [hOrder] at hMod
  have hNot :
      ¬ 3 ^ (2 ^ (r - 2))
          ≡ 1 [MOD 2 ^ (r + 1)] := by
    intro hCong
    have hOneLe :
        1 ≤ 3 ^ (2 ^ (r - 2)) := by
      apply Nat.one_le_iff_ne_zero.mpr
      exact pow_ne_zero _ (by norm_num)
    have hDvd :
        2 ^ (r + 1) ∣
          3 ^ (2 ^ (r - 2)) - 1 := by
      exact
        (Nat.modEq_iff_dvd' hOneLe).mp hCong.symm
    exact
      (threePow_twoPow_not_dvd_next r hr) hDvd
  exact hNot hMod

/--
正の自然数 `a` に対し、`b` が `a` の倍数で、
同時に `2a` を割り、しかも `b ≠ a` なら、
`b = 2a`。

隣接する multiplicative order の比が
`1` または `2` に限られる場面で使う。
-/
private theorem eq_double_of_dvd_of_dvd_double_of_ne
    {a b : ℕ}
    (ha : 0 < a)
    (hab : a ∣ b)
    (hba : b ∣ a * 2)
    (hne : b ≠ a) :
    b = a * 2 := by
  rcases hab with ⟨t, rfl⟩
  have htDvdTwo : t ∣ 2 := by
    exact (Nat.mul_dvd_mul_iff_left ha).mp hba
  have htCases : t = 1 ∨ t = 2 := by
    exact
      (Nat.dvd_prime (by decide : Nat.Prime 2)).mp htDvdTwo
  rcases htCases with htOne | htTwo
  · subst t
    simp at hne
  · subst t
    rfl

/--
`r ≥ 3` で `ord_(2^r)(3) = 2^(r-2)` なら、
法を一段上げると multiplicative order はちょうど 2 倍になる。
-/
private theorem orderOf_three_zmod_twoPow_succ_eq_double
    (r : ℕ)
    (hr : 3 ≤ r)
    (hOrder :
      orderOf (3 : ZMod (2 ^ r)) = 2 ^ (r - 2)) :
    orderOf (3 : ZMod (2 ^ (r + 1))) =
      orderOf (3 : ZMod (2 ^ r)) * 2 := by
  apply eq_double_of_dvd_of_dvd_double_of_ne
  · rw [hOrder]
    positivity
  · exact orderOf_three_zmod_twoPow_dvd_succ r
  · exact
      orderOf_three_zmod_twoPow_succ_dvd_double
        r hr hOrder
  · exact
      orderOf_three_zmod_twoPow_succ_ne_current
        r hr hOrder

/--
`r ≥ 3` に対する multiplicative order の exact formula。

`ord_(2^r)(3) = 2^(r-2)`。
-/
theorem orderOf_three_zmod_twoPow
    (r : ℕ)
    (hr : 3 ≤ r) :
    orderOf (3 : ZMod (2 ^ r)) = 2 ^ (r - 2) := by
  induction r, hr using Nat.le_induction with
  | base =>
      norm_num
      simp +decide only [orderOf_eq_iff]
  | succ r hr ih =>
      have hDouble :
          orderOf (3 : ZMod (2 ^ (r + 1))) =
            orderOf (3 : ZMod (2 ^ r)) * 2 :=
        orderOf_three_zmod_twoPow_succ_eq_double
          r hr ih
      calc
        orderOf (3 : ZMod (2 ^ (r + 1)))
            = orderOf (3 : ZMod (2 ^ r)) * 2 :=
              hDouble
        _ = 2 ^ (r - 2) * 2 := by
              rw [ih]
        _ = 2 ^ ((r + 1) - 2) := by
              rw [show (r + 1) - 2 = (r - 2) + 1 by omega]
              rw [pow_succ]

/--
`3^m = 1 (mod 2^r)` なら、`r ≥ 3` の下で
`2^(r-2)` が exponent `m` を割る。

後段の residual proof ではこの形だけを使用する。
-/
theorem twoPow_dvd_exponent_of_threePow_modEq_one
    {r m : ℕ}
    (hr : 3 ≤ r)
    (h : 3 ^ m ≡ 1 [MOD 2 ^ r]) :
    2 ^ (r - 2) ∣ m := by
  have hPow : (3 : ZMod (2 ^ r)) ^ m = 1 := by
    simpa [← ZMod.natCast_eq_natCast_iff] using h
  have hOrd : orderOf (3 : ZMod (2 ^ r)) ∣ m :=
    orderOf_dvd_iff_pow_eq_one.mpr hPow
  rwa [orderOf_three_zmod_twoPow r hr] at hOrd

end Arithmetic
end Collatz3
