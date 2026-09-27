import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTCarry: trailing-ones odd-run の除算なし exact model

二進数の末尾に `a` 個の `1` が並ぶ状況は

  x + 1 = 2^a * u

（`u` は奇数）と書ける。

このファイルでは除算可能性を途中で毎回扱わず、

  X_j + 1 = 2^(a-j) * 3^j * u

という整数恒等式を primitive に置く。
`j<a` では `3 X_j + 1 = 2 X_(j+1)` が exact に従い、
`j=a` では `X_a = 3^a u - 1` となる。

これは trailing-ones block の最小算術層である。
-/

namespace Collatz3
namespace CSTCarry

/-- trailing-ones factorization の始点を整数上で表す。 -/
def trailingOnesSeedZ (a u : ℕ) : ℤ :=
  (2 : ℤ) ^ a * (u : ℤ) - 1

/-- `j` 個の odd Terras step を消費した後の除算なし closed form。 -/
def trailingOnesRunZ (a u j : ℕ) : ℤ :=
  (2 : ℤ) ^ (a - j) * (3 : ℤ) ^ j * (u : ℤ) - 1

/-- run の時刻0は seed そのもの。 -/
@[simp] theorem trailingOnesRunZ_zero (a u : ℕ) :
    trailingOnesRunZ a u 0 = trailingOnesSeedZ a u := by
  simp [trailingOnesRunZ, trailingOnesSeedZ]

/-- `a` 個の trailing ones を使い切った終点は `3^a u - 1`。 -/
theorem trailingOnesRunZ_terminal (a u : ℕ) :
    trailingOnesRunZ a u a = (3 : ℤ) ^ a * (u : ℤ) - 1 := by
  simp [trailingOnesRunZ]

/--
`j<a` では一つ先の closed form が exact odd Terras relation
`3 X_j + 1 = 2 X_(j+1)` を満たす。
-/
theorem trailingOnesRunZ_step
    {a u j : ℕ}
    (hj : j < a) :
    3 * trailingOnesRunZ a u j + 1 =
      2 * trailingOnesRunZ a u (j + 1) := by
  have hExp : a - j = (a - (j + 1)) + 1 := by
    omega
  unfold trailingOnesRunZ
  rw [hExp, pow_succ]
  ring

/--
trailing-ones block 全体を一つの macro equation として読む形。
始点 `2^a u-1` から `a` odd relations の後に `3^a u-1` へ到達する。
-/
theorem trailingOnes_macro_end (a u : ℕ) :
    trailingOnesRunZ a u 0 = trailingOnesSeedZ a u ∧
      trailingOnesRunZ a u a = (3 : ℤ) ^ a * (u : ℤ) - 1 := by
  exact ⟨trailingOnesRunZ_zero a u, trailingOnesRunZ_terminal a u⟩

end CSTCarry
end Collatz3
