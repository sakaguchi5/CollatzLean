import CollatzLean.Collatz3.Semantics.OddOrbit
import Mathlib.Tactic.NormNum

/-!
# Collatz3: future minimum の thin semantics

future minimum は **actual orbit の値** に関する意味論であり、
critical roof anchor や Record--Ferrers の cut とは別概念である。

ここでは一点の性質と、任意に選択された future-minimum 列だけを定義する。
「次項が current+1 以後の tail minimum そのもの」という標準隣接性は
`StandardFutureMinimum.lean` に分離する。
-/

namespace Collatz3
namespace OddOrbit

/-- 位置 `n` の値が、それ以後の全軌道値以下である。 -/
def FutureMinimumAt
    (O : OddOrbit)
    (n : ℕ) : Prop :=
  ∀ m : ℕ, n ≤ m → O.value n ≤ O.value m

namespace FutureMinimumAt

/-- future minimum から始まる任意の有限 segment の終点は開始値以上。 -/
theorem le_segment_end
    {O : OddOrbit}
    {n : ℕ}
    (h : O.FutureMinimumAt n)
    (q : ℕ) :
    O.value n ≤ O.value (n + q) :=
  h (n + q) (by omega)

/--
値が `1` より大きい future minimum では、その位置の odd-only 指数は exact に `1`。

これは actual 値の最小性から出る定理であり、pure roof anchor `[1]` の定義には使わない。
-/
theorem exponent_eq_one_of_one_lt
    {O : OddOrbit}
    {n : ℕ}
    (h : O.FutureMinimumAt n)
    (hValue : 1 < O.value n) :
    O.exponent n = 1 := by
  have hExpPos := O.exponent_pos n
  by_contra hNe
  have hTwo : 2 ≤ O.exponent n := by
    omega
  have hPow : 4 ≤ 2 ^ O.exponent n := by
    have hMon := Nat.pow_le_pow_right
      (by decide : 0 < (2 : ℕ)) hTwo
    norm_num at hMon
    exact hMon
  have hNext : O.value n ≤ O.value (n + 1) :=
    h.le_segment_end 1
  have hFourStart :
      4 * O.value n ≤ 4 * O.value (n + 1) :=
    Nat.mul_le_mul_left 4 hNext
  have hFourNext :
      4 * O.value (n + 1) ≤
        2 ^ O.exponent n * O.value (n + 1) :=
    Nat.mul_le_mul_right (O.value (n + 1)) hPow
  have hEquation := (O.step n).equation
  have hBound : 4 * O.value n ≤ 3 * O.value n + 1 := by
    calc
      4 * O.value n ≤ 4 * O.value (n + 1) := hFourStart
      _ ≤ 2 ^ O.exponent n * O.value (n + 1) := hFourNext
      _ = 3 * O.value n + 1 := hEquation
  omega

end FutureMinimumAt

/--
選択済み future-minimum 列。

ここには「標準列であること」「値が strict に増えること」「非有界性」を保存しない。
それらは必要な theorem / predicate 側で追加する。
-/
structure FutureMinima (O : OddOrbit) where
  index : ℕ → ℕ
  index_strict : StrictMono index
  minimum : ∀ j : ℕ, O.FutureMinimumAt (index j)

namespace FutureMinima

/-- strict selector の index は列添字自身以上。 -/
theorem index_ge
    {O : OddOrbit}
    (S : O.FutureMinima)
    (j : ℕ) :
    j ≤ S.index j := by
  induction j with
  | zero =>
      exact Nat.zero_le _
  | succ j ih =>
      have hStep := S.index_strict (Nat.lt_succ_self j)
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih hStep)

end FutureMinima
end OddOrbit
end Collatz3
