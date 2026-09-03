import Mathlib.Data.Nat.Factorization.Defs

/-!
# 第3例探索 8: special return から t = tau を閉じる

係数側 first crossing が時刻 `H` にあり、proper prefix の実値がすべて開始値以上で、
terminal 値 `y` が

  3 y = 2 n + 1

を満たすとする。
`n > 1` なら `y < n` なので、実際の first drop も時刻 `H` である。

したがって coefficient stopping time `tau = H` と actual stopping time `t` は一致する。
この補題により、候補発見後に巨大軌道を step-by-step 再実行する必要がない。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch

/-- `t` が軌道 `x` の開始値 `n` に対する最初の strict drop である。 -/
def FirstDropAt
    (x : ℕ → ℕ) (n t : ℕ) : Prop :=
  x t < n ∧ ∀ k : ℕ, k < t → n ≤ x k

/-- first drop の時刻は一意。 -/
theorem FirstDropAt.unique
    {x : ℕ → ℕ} {n a b : ℕ}
    (ha : FirstDropAt x n a)
    (hb : FirstDropAt x n b) :
    a = b := by
  by_cases hab : a < b
  · have hba : n ≤ x a := hb.2 a hab
    have haDrop : x a < n := ha.1
    omega
  by_cases hba : b < a
  · have hab' : n ≤ x b := ha.2 b hba
    have hbDrop : x b < n := hb.1
    omega
  omega
/--
`3y = 2n+1` かつ `n>1` なら、special-return の直前値 `y` は必ず開始値より小さい。
-/
theorem specialReturn_terminal_lt
    (n y : ℕ)
    (hn : 1 < n)
    (hReturn : 3 * y = 2 * n + 1) :
    y < n := by
  omega

/--
first-crossing 候補を final verifier へ渡す最小 certificate。
`proper_not_below` が coefficient FirstCrossing と actual realization から供給される想定。
-/
structure FirstCrossingSpecialReturnData where
  n : ℕ
  y : ℕ
  H : ℕ
  trajectory : ℕ → ℕ
  n_gt_one : 1 < n
  terminal : trajectory H = y
  proper_not_below : ∀ k : ℕ, k < H → n ≤ trajectory k
  specialReturn : 3 * y = 2 * n + 1

/-- special-return certificate から実際の first drop が `H` と分かる。 -/
theorem FirstCrossingSpecialReturnData.firstDropAt
    (D : FirstCrossingSpecialReturnData) :
    FirstDropAt D.trajectory D.n D.H := by
  constructor
  · rw [D.terminal]
    exact specialReturn_terminal_lt D.n D.y D.n_gt_one D.specialReturn
  · exact D.proper_not_below

/--
係数側 first crossing が `tau = H` と分かっているなら、actual first drop `t` と一致する。

既存 RecordFerrers / Beatty 側では `hCoeff : tau = D.H` を supply すればよい。
-/
theorem firstCrossing_specialReturn_t_eq_tau
    (D : FirstCrossingSpecialReturnData)
    (t tau : ℕ)
    (ht : FirstDropAt D.trajectory D.n t)
    (hCoeff : tau = D.H) :
    t = tau := by
  have hH : FirstDropAt D.trajectory D.n D.H := D.firstDropAt
  have htH : t = D.H := FirstDropAt.unique ht hH
  omega

end ThirdExampleSearch
end CSTMicro
end Collatz2
