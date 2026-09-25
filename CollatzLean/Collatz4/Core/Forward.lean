import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Multiplicity
/-!
# Collatz4.Core.Forward

Collatz3 から独立した、m=7 前向き証明用の最小状態系。

正整数 `A` を

`A = 2^t * u`

と分解し、`t` と奇数部分 `u` だけを状態として保持する。
-/

namespace Collatz4

/-- 2進指数。`0` では `0` とする mathlib の `padicValNat` を使う。 -/
def v2 (n : ℕ) : ℕ :=
  padicValNat 2 n

/-- 2の最大冪を除いた部分。 -/
def oddPart (n : ℕ) : ℕ :=
  n.divMaxPow 2

/-- 前向き反復で使う圧縮状態。`value = 2^t * u`。 -/
@[ext]
structure ForwardState where
  t : ℕ
  u : ℕ
  deriving DecidableEq, Repr

namespace ForwardState

/-- 圧縮状態が表す自然数。 -/
def value (x : ForwardState) : ℕ :=
  2 ^ x.t * x.u

/-- 自然数を2進指数と奇数部分へ分解する。 -/
def ofNat (n : ℕ) : ForwardState :=
  ⟨v2 n, oddPart n⟩

/-- `ofNat` は元の自然数を正確に復元する。 -/
theorem value_ofNat (n : ℕ) : (ofNat n).value = n := by
  simp [ofNat, value, v2, oddPart, Nat.pow_padicValNat_mul_divMaxPow]

end ForwardState

/--
`A = 2^t u` に対する決定的前向き写像。

`3A + 2^t = 2^t (3u+1)` を再び 2進指数と奇数部分へ分解する。
-/
def step (x : ForwardState) : ForwardState :=
  let z := 3 * x.u + 1
  let a := v2 z
  ⟨x.t + a, oddPart z⟩

/-- `step` を指定回数だけ反復する。native 実行を意識した単純な末尾再帰。 -/
def run : ℕ → ForwardState → ForwardState
  | 0, x => x
  | k + 1, x => run k (step x)

@[simp] theorem run_zero (x : ForwardState) : run 0 x = x := rfl
@[simp] theorem run_succ (k : ℕ) (x : ForwardState) :
    run (k + 1) x = run k (step x) := rfl

/-- `3u+1` は常に正なので、前向き計算中に `v2` の 0 用規約は使われない。 -/
theorem three_mul_add_one_ne_zero (u : ℕ) : 3 * u + 1 ≠ 0 := by
  omega

end Collatz4
