import CollatzLean.Collatz4.Dynamics.Odd


/-!
# Collatz4.Dynamics.Accumulated

奇数圧縮 Collatz 写像を、累積した 2 指数を失わない自然数座標で扱う一般層。

自然数 `A` に対して

`F(A) = 3*A + 2^v₂(A)`

と置く。`A = 2^t * u`（`u` は 2 の最大冪を除いた部分）なら

`F(A) = 2^t * (3*u+1)`

である。したがって `F(A)` の奇数部分は `u` の奇数圧縮 Collatz 次状態と一致する。
このファイルには `M=7` や `101...` 族固有の定数を置かない。
-/

namespace Collatz4.Dynamics

/-- 自然数の 2 進指数。`0` では mathlib の規約により `0`。 -/
def accumulatedV2 (A : ℕ) : ℕ :=
  padicValNat 2 A

/-- 自然数から 2 の最大冪を除いた部分。 -/
def accumulatedOddPart (A : ℕ) : ℕ :=
  A.divMaxPow 2

/--
累積 2 指数を保持する前向き写像。

`A = 2^t*u` なら `accumulatedStep A = 2^t*(3*u+1)` となる。
-/
def accumulatedStep (A : ℕ) : ℕ :=
  3 * A + 2 ^ accumulatedV2 A

/-- `accumulatedStep` を指定回数だけ反復する。 -/
def accumulatedRun : ℕ → ℕ → ℕ
  | 0, A => A
  | k + 1, A => accumulatedRun k (accumulatedStep A)

@[simp] theorem accumulatedRun_zero (A : ℕ) : accumulatedRun 0 A = A := rfl

@[simp] theorem accumulatedRun_succ (k A : ℕ) :
    accumulatedRun (k + 1) A = accumulatedRun k (accumulatedStep A) := rfl

/-- 任意の自然数は「2 の冪 × 2 の最大冪を除いた部分」に正確に分解できる。 -/
theorem accumulated_decomposition (A : ℕ) :
    2 ^ accumulatedV2 A * accumulatedOddPart A = A := by
  simp only [accumulatedV2, accumulatedOddPart, Nat.pow_padicValNat_mul_divMaxPow]

/--
累積写像の基本因数分解。

`A = 2^t*u` を代入すると、`F(A)=2^t(3u+1)` がそのまま得られる。
-/
theorem accumulatedStep_factor (A : ℕ) :
    accumulatedStep A =
      2 ^ accumulatedV2 A * (3 * accumulatedOddPart A + 1) := by
  unfold accumulatedStep
  calc
    3 * A + 2 ^ accumulatedV2 A
        =
      3 * (2 ^ accumulatedV2 A * accumulatedOddPart A) +
        2 ^ accumulatedV2 A := by
          rw [accumulated_decomposition A]
    _ =
      2 ^ accumulatedV2 A * (3 * accumulatedOddPart A + 1) := by
          ring


/--
累積写像を 1 回進めた後の奇数部分は、元の奇数部分を `oddStep` で 1 回進めた値。

これが `F(A)=3A+2^v₂(A)` と通常の奇数圧縮 Collatz 写像の直接対応である。
-/
theorem accumulatedOddPart_step (A : ℕ) :
    accumulatedOddPart (accumulatedStep A) =
      oddStep (accumulatedOddPart A) := by
  rw [accumulatedStep_factor]
  unfold accumulatedOddPart oddStep
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Nat.divMaxPow_base_pow_mul]

/--
1 回の遷移で増える累積 2 指数は、奇数部分 `u` に対する `v₂(3u+1)` そのもの。
-/
theorem accumulatedV2_step (A : ℕ) :
    accumulatedV2 (accumulatedStep A) =
      accumulatedV2 A + padicValNat 2 (3 * accumulatedOddPart A + 1) := by
  have hne : 3 * accumulatedOddPart A + 1 ≠ 0 := by omega
  rw [accumulatedStep_factor]
  unfold accumulatedV2 accumulatedOddPart
  have h :=
    padicValNat_base_pow_mul
      (p := 2) (n := 3 * A.divMaxPow 2 + 1)
      (by norm_num : 1 < (2 : ℕ)) hne (padicValNat 2 A)
  omega

/--
累積写像を何回進めても、その奇数部分は `oddRun` と完全に一致する。

したがって累積座標は奇数 Collatz 軌道を変更せず、2 指数の履歴だけを保持している。
-/
theorem accumulatedOddPart_run (k A : ℕ) :
    accumulatedOddPart (accumulatedRun k A) =
      oddRun k (accumulatedOddPart A) := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih =>
      simp only [accumulatedRun_succ, oddRun_succ]
      rw [ih]
      rw [accumulatedOddPart_step]

end Collatz4.Dynamics
