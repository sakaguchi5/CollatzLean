import CollatzLean.Collatz4.Parametric.Reachability



/-!
# Collatz4.Parametric.ReachabilityWord

`Dynamics.Reaches` が保持する actual odd-only orbit から、各 odd step で除かれた
2指数の有限 word を決定的に復元する一般層。

ここでは `Q_N` や特定の target `M` に依存しない。

奇数状態 `x` に対して

`A(x) = 2*x + 1`

と置くと、1回の odd step の 2指数を `e` として

`2^e * A(next x) = 3 * A(x) + (2^e - 1)`

が成り立つ。この式を word に沿って合成し、

`2^E * A(x_s) = 3^s * A(x_0) + D(w)`

を得る。
-/

namespace Collatz4.Parametric

open Collatz4.Dynamics

/-- odd step `x -> oddStep x` で除かれる2の指数。 -/
def stepExponent (x : ℕ) : ℕ :=
  padicValNat 2 (3 * x + 1)

/-- odd state を `A = 2*x+1` へ持ち上げる。 -/
def lifted (x : ℕ) : ℕ :=
  2 * x + 1

/-- 1 odd step の exact balance。 -/
theorem step_exact (x : ℕ) :
    2 ^ stepExponent x * oddStep x = 3 * x + 1 := by
  simp [stepExponent, oddStep, Nat.pow_padicValNat_mul_divMaxPow]

/-- `A=2*x+1` 座標での1 step affine relation。 -/
theorem step_lifted_balance (x : ℕ) :
    2 ^ stepExponent x * lifted (oddStep x) =
      3 * lifted x + (2 ^ stepExponent x - 1) := by
  have hstep := step_exact x
  have hp : 0 < 2 ^ stepExponent x := by positivity
  unfold lifted
  calc
    2 ^ stepExponent x * (2 * oddStep x + 1) =
        2 * (2 ^ stepExponent x * oddStep x) + 2 ^ stepExponent x := by
      ring
    _ = 2 * (3 * x + 1) + 2 ^ stepExponent x := by
      rw [hstep]
    _ = 3 * (2 * x + 1) + (2 ^ stepExponent x - 1) := by
      omega

/-- `k` 回の actual odd run から得られる2指数 word。 -/
def reachabilityWord : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, x => stepExponent x :: reachabilityWord k (oddStep x)

/-- word が消費する総2指数。 -/
def wordTwoExponent (w : List ℕ) : ℕ :=
  w.sum

/--
`A=2*x+1` 座標での affine 定数。

先頭指数 `e`、残り word `w` に対して

`D(e::w) = 3^|w| (2^e-1) + 2^e D(w)`。
-/
def wordAffineConst : List ℕ → ℕ
  | [] => 0
  | e :: w =>
      3 ^ w.length * (2 ^ e - 1) + 2 ^ e * wordAffineConst w

@[simp] theorem reachabilityWord_length (k x : ℕ) :
    (reachabilityWord k x).length = k := by
  induction k generalizing x with
  | zero => simp [reachabilityWord]
  | succ k ih =>
      simp [reachabilityWord, ih]

/-- `oddRun` の最後の1 step を右側へ取り出す。 -/
theorem oddRun_succ_last (k x : ℕ) :
    oddRun (k + 1) x = oddStep (oddRun k x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [oddRun_succ]
      rw [ih]
      rw [oddRun_succ]

/--
actual odd run に沿う exponent word の exact affine identity。
-/
theorem oddRun_lifted_affine (k x : ℕ) :
    2 ^ wordTwoExponent (reachabilityWord k x) * lifted (oddRun k x) =
      3 ^ k * lifted x + wordAffineConst (reachabilityWord k x) := by
  induction k generalizing x with
  | zero =>
      simp [reachabilityWord, wordTwoExponent, wordAffineConst]
  | succ k ih =>
      let y : ℕ := oddStep x
      let e : ℕ := stepExponent x
      let w : List ℕ := reachabilityWord k y
      have hih :
          2 ^ wordTwoExponent w * lifted (oddRun k y) =
            3 ^ k * lifted y + wordAffineConst w := by
        simpa [w, y] using ih y
      have hstep :
          2 ^ e * lifted y = 3 * lifted x + (2 ^ e - 1) := by
        simpa [e, y] using step_lifted_balance x
      have hlen : w.length = k := by
        simp only [reachabilityWord_length, w, y]
      simp only [reachabilityWord, wordTwoExponent, wordAffineConst, List.sum_cons]
      change
        2 ^ (e + wordTwoExponent w) * lifted (oddRun k y) =
          3 ^ (k + 1) * lifted x +
            (3 ^ w.length * (2 ^ e - 1) + 2 ^ e * wordAffineConst w)
      rw [hlen]
      calc
        2 ^ (e + wordTwoExponent w) * lifted (oddRun k y) =
            2 ^ e * (2 ^ wordTwoExponent w * lifted (oddRun k y)) := by
          rw [pow_add]
          ring
        _ = 2 ^ e * (3 ^ k * lifted y + wordAffineConst w) := by
          rw [hih]
        _ = 3 ^ k * (2 ^ e * lifted y) + 2 ^ e * wordAffineConst w := by
          ring
        _ = 3 ^ k * (3 * lifted x + (2 ^ e - 1)) +
              2 ^ e * wordAffineConst w := by
          rw [hstep]
        _ = 3 ^ (k + 1) * lifted x +
              (3 ^ k * (2 ^ e - 1) + 2 ^ e * wordAffineConst w) := by
          rw [pow_succ]
          ring

/-- `Q_N=(3^N-1)/2` を `A=2*x+1` に持ち上げると正確に `3^N`。 -/
theorem qStart_lifted (N : ℕ) :
    lifted (Collatz4.Family.qStart N) = 3 ^ N := by
  induction N with
  | zero =>
      simp [lifted, Collatz4.Family.qStart]
  | succ N ih =>
      have hnum :
          3 ^ (N + 1) - 1 =
            2 * (3 * Collatz4.Family.qStart N + 1) := by
        rw [pow_succ]
        rw [← ih]
        simp only [lifted]
        omega
      have hq :
          Collatz4.Family.qStart (N + 1) =
            3 * Collatz4.Family.qStart N + 1 := by
        change
          (3 ^ (N + 1) - 1) / 2 =
            3 * Collatz4.Family.qStart N + 1
        rw [hnum]
        simp
      rw [hq]
      rw [pow_succ]
      rw [← ih]
      simp only [lifted]
      ring

/-- `Q_N` の基本漸化式。 -/
theorem qStart_succ (N : ℕ) :
    Collatz4.Family.qStart (N + 1) =
      3 * Collatz4.Family.qStart N + 1 := by
  have h1 := qStart_lifted (N + 1)
  have h0 := qStart_lifted N
  rw [pow_succ] at h1
  simp only [lifted] at h1 h0
  omega

/-- 正の `N` では `Q_N = 1 mod 3`。 -/
theorem qStart_mod_three_of_pos
    {N : ℕ} (hN : 0 < N) :
    Collatz4.Family.qStart N % 3 = 1 := by
  obtain ⟨n, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [qStart_succ]
  simp [Nat.add_mod]

end Collatz4.Parametric
