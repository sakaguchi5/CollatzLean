import CollatzLean.Collatz3.Experimental2.OstrowskiCorridorArithmetic

/-!
# Collatz3 Experimental2: canonical Ostrowski 算術核

このファイルでは continued fraction の実数論そのものを再実装せず、
`a₁ = 1` の場合に退化した最初の `0/1` convergent を取り除いた後の
Ostrowski weight 列が満たす純粋な自然数再帰だけを保存する。

標準記法 `q₀=1, q₁=a₁=1` から `q₁,q₂,...` へ一段ずらし、ここでは

* `Q 0 = 1`,
* `Q 1 = a 0 + 1`,
* `Q (n+2) = a (n+1) * Q (n+1) + Q n`

とする。`a n` は対応する digit の上限である。

重要な分離は次の通り。

* `IsBoundedOstrowskiDigits`: 各 digit が partial quotient 上限以下。
  これは exact corridor composition に十分である。
* `IsCanonicalOstrowskiDigits`: 上に加えて最大 digit の直下を `0` にする。
  これは exactness ではなく normal form / uniqueness のために使う。

bounded 条件だけから

`(d n - 1) * Q n + Σ_{i<n} d i Q i < Q (n+1)`

が従う。これが sharp corridor の自然 range と完全に一致する。
-/

namespace Collatz3
namespace Experimental2

/--
`a₁=1` の標準 Ostrowski 系から最初の退化 weight を除いた自然数 weight system。

`a n` は digit `n` の最大値、`Q n` はその weight。
-/
structure UnitOstrowskiWeightSystem where
  a : ℕ → ℕ
  Q : ℕ → ℕ
  a_pos : ∀ n, 0 < a n
  q_zero : Q 0 = 1
  q_one : Q 1 = a 0 + 1
  q_rec : ∀ n, Q (n + 2) = a (n + 1) * Q (n + 1) + Q n

namespace UnitOstrowskiWeightSystem

/-- 全ての Ostrowski weight は正。 -/
theorem q_pos (W : UnitOstrowskiWeightSystem) :
    ∀ n : ℕ, 0 < W.Q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | n)
      · rw [W.q_zero]
        omega
      · rw [W.q_one]
        omega
      · rw [W.q_rec n]
        have hq : 0 < W.Q (n + 1) := ih (n + 1) (by omega)
        have ha : 0 < W.a (n + 1) := W.a_pos (n + 1)
        have hMul : 0 < W.a (n + 1) * W.Q (n + 1) := Nat.mul_pos ha hq
        omega

/-- weight 列は一段ごとに真に増加する。 -/
theorem q_lt_succ (W : UnitOstrowskiWeightSystem) (n : ℕ) :
    W.Q n < W.Q (n + 1) := by
  rcases n with (_ | n)
  · rw [W.q_zero, W.q_one]
    have ha := W.a_pos 0
    omega
  · rw [W.q_rec n]
    have ha : 1 ≤ W.a (n + 1) := by
      exact Nat.succ_le_iff.mpr (W.a_pos (n + 1))
    have hMul : W.Q (n + 1) ≤ W.a (n + 1) * W.Q (n + 1) := by
      simpa using Nat.mul_le_mul_right (W.Q (n + 1)) ha
    have hQPos : 0 < W.Q n := W.q_pos n
    omega

/-- weight 列は strict monotone。 -/
theorem q_strictMono (W : UnitOstrowskiWeightSystem) :
    StrictMono W.Q := by
  exact strictMono_nat_of_lt_succ W.q_lt_succ

/-- `Q n` は少なくとも `n+1`。従って任意の自然数は十分高い weight より小さい。 -/
theorem index_succ_le_q (W : UnitOstrowskiWeightSystem) :
    ∀ n : ℕ, n + 1 ≤ W.Q n := by
  intro n
  induction n with
  | zero =>
      rw [W.q_zero]
  | succ n ih =>
      have hlt := W.q_lt_succ n
      omega

/-- 任意の `N` について `N < Q(N+1)`。greedy existence の有限上界として使う。 -/
theorem self_lt_next_q (W : UnitOstrowskiWeightSystem) (N : ℕ) :
    N < W.Q (N + 1) := by
  have h := W.index_succ_le_q (N + 1)
  omega

end UnitOstrowskiWeightSystem

/--
`a₁=1` の regular continued fraction から最初の退化 convergent `0/1` を除いた
分子・分母再帰。

`Q` 側は Ostrowski weight、`P` 側は同じ partial quotient で進む対応分子である。
-/
structure UnitOstrowskiConvergentSystem extends UnitOstrowskiWeightSystem where
  P : ℕ → ℕ
  p_zero : P 0 = 1
  p_one : P 1 = a 0
  p_rec : ∀ n, P (n + 2) = a (n + 1) * P (n + 1) + P n

namespace UnitOstrowskiConvergentSystem

/-- convergent の `P` 座標も全て正。 -/
theorem p_pos (C : UnitOstrowskiConvergentSystem) :
    ∀ n : ℕ, 0 < C.P n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | n)
      · rw [C.p_zero]
        omega
      · rw [C.p_one]
        exact C.a_pos 0
      · rw [C.p_rec n]
        have hp : 0 < C.P (n + 1) := ih (n + 1) (by omega)
        have ha : 0 < C.a (n + 1) := C.a_pos (n + 1)
        have hMul : 0 < C.a (n + 1) * C.P (n + 1) := Nat.mul_pos ha hp
        omega

/-- 最初の同値 `P0=P1=1` の可能性を除けば `P` は真に増加する。 -/
theorem p_lt_succ_of_pos_index
    (C : UnitOstrowskiConvergentSystem)
    {n : ℕ}
    (hn : 0 < n) :
    C.P n < C.P (n + 1) := by
  cases n with
  | zero => omega
  | succ m =>
      rw [C.p_rec m]
      have ha : 1 ≤ C.a (m + 1) := by
        exact Nat.succ_le_iff.mpr (C.a_pos (m + 1))
      have hMul : C.P (m + 1) ≤ C.a (m + 1) * C.P (m + 1) := by
        simpa using Nat.mul_le_mul_right (C.P (m + 1)) ha
      have hPrev : 0 < C.P m := C.p_pos m
      omega

end UnitOstrowskiConvergentSystem

/-- weight `w` と digit 列 `d` の先頭 `n` 桁の weighted sum。 -/
def ostrowskiPrefixSum
    (w d : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ostrowskiPrefixSum w d n + d n * w n

@[simp] theorem ostrowskiPrefixSum_zero
    (w d : ℕ → ℕ) :
    ostrowskiPrefixSum w d 0 = 0 := rfl

@[simp] theorem ostrowskiPrefixSum_succ
    (w d : ℕ → ℕ) (n : ℕ) :
    ostrowskiPrefixSum w d (n + 1) =
      ostrowskiPrefixSum w d n + d n * w n := rfl

/-- prefix 内で digit が一致すれば weighted sum も一致する。 -/
theorem ostrowskiPrefixSum_congr
    {w d e : ℕ → ℕ} :
    ∀ {n : ℕ},
      (∀ i < n, d i = e i) →
      ostrowskiPrefixSum w d n = ostrowskiPrefixSum w e n := by
  intro n
  induction n with
  | zero =>
      intro h
      rfl
  | succ n ih =>
      intro h
      rw [ostrowskiPrefixSum_succ, ostrowskiPrefixSum_succ]
      rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- prefix sum は index を伸ばすと減らない。 -/
theorem ostrowskiPrefixSum_mono_index
    (w d : ℕ → ℕ) :
    Monotone (ostrowskiPrefixSum w d) := by
  intro a b hab
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact Nat.le_refl _
  | succ b ih =>
      by_cases hEq : a = b + 1
      · subst a
        exact Nat.le_refl _
      · have hab' : a ≤ b := by omega
        have hle := ih hab'
        rw [ostrowskiPrefixSum_succ]
        omega

/-- 指定 prefix 内の digit が全て `0` なら weighted sum も `0`。 -/
theorem ostrowskiPrefixSum_eq_zero_of_digits_eq_zero
    {w d : ℕ → ℕ} :
    ∀ {n : ℕ},
      (∀ i < n, d i = 0) →
      ostrowskiPrefixSum w d n = 0 := by
  intro n
  induction n with
  | zero =>
      intro h
      rfl
  | succ n ih =>
      intro h
      rw [ostrowskiPrefixSum_succ, ih (fun i hi => h i (by omega)), h n (by omega)]
      simp

/-- positive digit を含む prefix の weighted sum は、weight が正なら正。 -/
theorem ostrowskiPrefixSum_pos_of_digit_pos
    {w d : ℕ → ℕ}
    {j n : ℕ}
    (hWeight : 0 < w j)
    (hDigit : 0 < d j)
    (hj : j < n) :
    0 < ostrowskiPrefixSum w d n := by
  have hAt :
      0 < ostrowskiPrefixSum w d (j + 1) := by
    rw [ostrowskiPrefixSum_succ]
    have hMul : 0 < d j * w j := Nat.mul_pos hDigit hWeight
    omega
  have hMono := ostrowskiPrefixSum_mono_index w d (show j + 1 ≤ n by omega)
  exact lt_of_lt_of_le hAt hMono

/-- 各 digit が対応する partial quotient 上限以下であるという最小条件。 -/
def IsBoundedOstrowskiDigits
    (W : UnitOstrowskiWeightSystem)
    (d : ℕ → ℕ) : Prop :=
  ∀ n, d n ≤ W.a n

/--
canonical Ostrowski normal form。

exact corridor law に必要なのは `bounded` だけであり、
最大 digit の直下を `0` にする条件は一意性のために分離して持つ。
-/
def IsCanonicalOstrowskiDigits
    (W : UnitOstrowskiWeightSystem)
    (d : ℕ → ℕ) : Prop :=
  IsBoundedOstrowskiDigits W d ∧
    ∀ n, d (n + 1) = W.a (n + 1) → d n = 0

namespace IsCanonicalOstrowskiDigits

/-- canonical digits は当然 bounded。 -/
theorem bounded
    {W : UnitOstrowskiWeightSystem}
    {d : ℕ → ℕ}
    (C : IsCanonicalOstrowskiDigits W d) :
    IsBoundedOstrowskiDigits W d := C.1

/-- 最大 digit の直下は `0`。 -/
theorem previous_eq_zero_of_max
    {W : UnitOstrowskiWeightSystem}
    {d : ℕ → ℕ}
    (C : IsCanonicalOstrowskiDigits W d)
    {n : ℕ}
    (hMax : d (n + 1) = W.a (n + 1)) :
    d n = 0 := C.2 n hMax

end IsCanonicalOstrowskiDigits

/--
bounded digits の prefix は、隣接二 weight の和より二だけ小さい範囲に収まる。

減算を避けた形

`sum + 2 ≤ Q(n+1) + Q n`

で証明する。これは digit 上限だけから従い、canonical adjacency は使わない。
-/
theorem boundedOstrowskiPrefix_add_two_le
    {W : UnitOstrowskiWeightSystem}
    {d : ℕ → ℕ}
    (B : IsBoundedOstrowskiDigits W d) :
    ∀ n : ℕ,
      ostrowskiPrefixSum W.Q d (n + 1) + 2 ≤
        W.Q (n + 1) + W.Q n := by
  intro n
  induction n with
  | zero =>
      rw [ostrowskiPrefixSum_succ, ostrowskiPrefixSum_zero,
        W.q_zero, W.q_one]
      have hd := B 0
      simpa [Nat.zero_add, Nat.mul_one] using Nat.add_le_add_right hd 2
  | succ n ih =>
      rw [ostrowskiPrefixSum_succ]
      have hd := B (n + 1)
      have hMul :
          d (n + 1) * W.Q (n + 1) ≤
            W.a (n + 1) * W.Q (n + 1) :=
        Nat.mul_le_mul_right (W.Q (n + 1)) hd
      calc
        ostrowskiPrefixSum W.Q d (n + 1) +
              d (n + 1) * W.Q (n + 1) + 2
            = (ostrowskiPrefixSum W.Q d (n + 1) + 2) +
                d (n + 1) * W.Q (n + 1) := by omega
        _ ≤ (W.Q (n + 1) + W.Q n) +
              W.a (n + 1) * W.Q (n + 1) :=
            Nat.add_le_add ih hMul
        _ = W.Q (n + 2) + W.Q (n + 1) := by
            rw [W.q_rec n]
            ring

/--
positive digit の一個を現在の corridor として剥がした後の residual は
必ず次 weight 未満。

`d n > 0` と bounded digit 条件だけから

`(d n - 1) Q n + lowerPrefix < Q(n+1)`

を得る。これが sharp inverse corridor の自然 range と一致する。
-/
theorem boundedOstrowskiResidual_lt_nextWeight
    {W : UnitOstrowskiWeightSystem}
    {d : ℕ → ℕ}
    (B : IsBoundedOstrowskiDigits W d)
    {n : ℕ}
    (hPos : 0 < d n) :
    (d n - 1) * W.Q n + ostrowskiPrefixSum W.Q d n <
      W.Q (n + 1) := by
  rcases n with (_ | n)
  · rw [ostrowskiPrefixSum_zero, W.q_zero, W.q_one]
    have hd := B 0
    omega
  · have hCap := boundedOstrowskiPrefix_add_two_le B n
    have hd := B (n + 1)
    have hMul :
        d (n + 1) * W.Q (n + 1) ≤
          W.a (n + 1) * W.Q (n + 1) :=
      Nat.mul_le_mul_right (W.Q (n + 1)) hd
    have hSplit :
        (d (n + 1) - 1) * W.Q (n + 1) + W.Q (n + 1) =
          d (n + 1) * W.Q (n + 1) := by
      have hdEq : d (n + 1) - 1 + 1 = d (n + 1) := by omega
      calc
        (d (n + 1) - 1) * W.Q (n + 1) + W.Q (n + 1)
            = (d (n + 1) - 1 + 1) * W.Q (n + 1) := by ring
        _ = d (n + 1) * W.Q (n + 1) := by rw [hdEq]
    have hBound :
        (d (n + 1) - 1) * W.Q (n + 1) +
              ostrowskiPrefixSum W.Q d (n + 1) + 2 ≤
          W.Q (n + 2) := by
      calc
        (d (n + 1) - 1) * W.Q (n + 1) +
              ostrowskiPrefixSum W.Q d (n + 1) + 2
            = (d (n + 1) - 1) * W.Q (n + 1) +
                (ostrowskiPrefixSum W.Q d (n + 1) + 2) := by omega
        _ ≤ (d (n + 1) - 1) * W.Q (n + 1) +
              (W.Q (n + 1) + W.Q n) :=
            Nat.add_le_add_left hCap _
        _ = d (n + 1) * W.Q (n + 1) + W.Q n := by
            rw [← Nat.add_assoc, hSplit]
        _ ≤ W.a (n + 1) * W.Q (n + 1) + W.Q n :=
            Nat.add_le_add_right hMul _
        _ = W.Q (n + 2) := by rw [W.q_rec n]
    have hIdx : n + 1 + 1 = n + 2 := by
      omega
    rw [hIdx]
    omega

/--
canonical digits では prefix remainder が一段強く exact に `Q n` 未満となる。

これは uniqueness / greedy normal form の本質であり、corridor exactness 自体には不要。
-/
theorem canonicalOstrowskiPrefix_lt_weight
    {W : UnitOstrowskiWeightSystem}
    {d : ℕ → ℕ}
    (C : IsCanonicalOstrowskiDigits W d) :
    ∀ n : ℕ,
      ostrowskiPrefixSum W.Q d n < W.Q n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | n)
      · rw [ostrowskiPrefixSum_zero, W.q_zero]
        omega
      · rw [ostrowskiPrefixSum_succ, ostrowskiPrefixSum_zero,
          W.q_zero, W.q_one]
        have hd := C.bounded 0
        omega
      · have hPrev :
            ostrowskiPrefixSum W.Q d (n + 1) < W.Q (n + 1) :=
          ih (n + 1) (by omega)
        have hPrevPrev :
            ostrowskiPrefixSum W.Q d n < W.Q n :=
          ih n (by omega)
        rw [ostrowskiPrefixSum_succ, W.q_rec n]
        by_cases hMax : d (n + 1) = W.a (n + 1)
        · have hZero : d n = 0 := C.previous_eq_zero_of_max hMax
          have hLowEq :
              ostrowskiPrefixSum W.Q d (n + 1) =
                ostrowskiPrefixSum W.Q d n := by
            rw [ostrowskiPrefixSum_succ, hZero]
            simp
          rw [hMax, hLowEq]
          simpa [Nat.add_comm] using
            Nat.add_lt_add_left hPrevPrev
              (W.a (n + 1) * W.Q (n + 1))
        · have hLt : d (n + 1) < W.a (n + 1) :=
            lt_of_le_of_ne (C.bounded (n + 1)) hMax
          have hSuccLe : d (n + 1) + 1 ≤ W.a (n + 1) := by omega
          have hMul :
              (d (n + 1) + 1) * W.Q (n + 1) ≤
                W.a (n + 1) * W.Q (n + 1) :=
            Nat.mul_le_mul_right (W.Q (n + 1)) hSuccLe
          calc
            ostrowskiPrefixSum W.Q d (n + 1) +
                  d (n + 1) * W.Q (n + 1)
                < W.Q (n + 1) +
                    d (n + 1) * W.Q (n + 1) :=
                  Nat.add_lt_add_right hPrev _
            _ = (d (n + 1) + 1) * W.Q (n + 1) := by ring
            _ ≤ W.a (n + 1) * W.Q (n + 1) := hMul
            _ < W.a (n + 1) * W.Q (n + 1) + W.Q n := by
                  have hq := W.q_pos n
                  omega

end Experimental2
end Collatz3
