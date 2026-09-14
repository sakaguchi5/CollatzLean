import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Arithmetic: 一つの剰余類を短い整数区間へ切ったときの5候補補題

このファイルは Collatz 固有の量を持たない。

正の法 `M` と canonical representative `0 ≤ r < M` を固定し、

`q ≡ r (mod M)`

かつ

`-M < q < 4M`

なら、`q` は

`r-M, r, r+M, r+2M, r+3M`

の5個のうちどれかに限られる。

後段では `M = 2^(E+1)`、`q` を completion lift cocycle に適用する。
-/

namespace Collatz3
namespace Arithmetic

/--
一つの剰余類を open interval `(-M,4M)` に制限すると候補は高々5個。

`Int.ModEq` の quotient witness を取り出し、その係数が `-3,-2,-1,0,1`
以外では区間条件に反することだけを使う。
-/
theorem five_candidates_of_modEq_of_short_window
    {M r q : ℤ}
    (hM : 0 < M)
    (hr0 : 0 ≤ r)
    (hrM : r < M)
    (hmod : q ≡ r [ZMOD M])
    (hlow : -M < q)
    (hhigh : q < 4 * M) :
    q = r - M ∨
      q = r ∨
      q = r + M ∨
      q = r + 2 * M ∨
      q = r + 3 * M := by
  rcases (Int.modEq_iff_add_fac).1 hmod with ⟨k, hk⟩
  have hkLower : -3 ≤ k := by
    by_contra hNot
    have hkLe : k ≤ -4 := by omega
    have hMul : M * k ≤ M * (-4) :=
      mul_le_mul_of_nonneg_left hkLe (le_of_lt hM)
    linarith
  have hkUpper : k ≤ 1 := by
    by_contra hNot
    have hkGe : 2 ≤ k := by omega
    have hMul : M * 2 ≤ M * k :=
      mul_le_mul_of_nonneg_left hkGe (le_of_lt hM)
    linarith
  have hkCases :
      k = -3 ∨ k = -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 := by
    omega
  rcases hkCases with hk3 | hk2 | hk1 | hk0 | hkP
  · right; right; right; right
    rw [hk3] at hk
    linarith
  · right; right; right; left
    rw [hk2] at hk
    linarith
  · right; right; left
    rw [hk1] at hk
    linarith
  · right; left
    rw [hk0] at hk
    linarith
  · left
    rw [hkP] at hk
    linarith

end Arithmetic
end Collatz3
