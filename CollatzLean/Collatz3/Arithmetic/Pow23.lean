import Mathlib.Data.Nat.Prime.Basic

/-!
# Collatz3: 2 と 3 の冪に関する最小算術

このファイルには Collatz 固有の軌道概念を置かない。
後段で繰り返し使う `2^H` と `3^p` の互いに素性だけをまとめる。
-/

namespace Collatz3
namespace Arithmetic

@[simp] theorem twoPow_pos (H : ℕ) : 0 < 2 ^ H := by
  induction H with
  | zero =>
      decide
  | succ H ih =>
      rw [pow_succ]
      exact Nat.mul_pos ih (by decide)

@[simp] theorem threePow_pos (p : ℕ) : 0 < 3 ^ p := by
  induction p with
  | zero =>
      decide
  | succ p ih =>
      rw [pow_succ]
      exact Nat.mul_pos ih (by decide)

/-- `3^p` と `2^H` は互いに素。 -/
theorem coprime_threePow_twoPow (p H : ℕ) :
    Nat.Coprime (3 ^ p) (2 ^ H) := by
  exact ((by decide : Nat.Coprime 3 2).pow_left p).pow_right H

end Arithmetic
end Collatz3
