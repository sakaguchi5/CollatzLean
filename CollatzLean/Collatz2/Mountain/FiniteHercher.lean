import CollatzLean.Collatz2.Mountain.OneMountainExclusion

/-!
# Collatz2 Mountain: finite Hercher local lemmas

Hercher (2023) Lemma 8 / Lemma 20 のうち、cycle の cyclicity を使わない
一 mountain 局所部分を current odd-only formalism へ移す。

Lemma 8:

  k consecutive standard odd steps
  => 2^k | n+1
  => 2^k - 1 <= n.

Lemma 20 は実数 `delta = log(3)/log(2)` を使う前の division-free core

  2^(k+1) * n_next < 3^k * (n+1)

として保持する。この整数形は、Hercher の proof で
`n_next < n^delta` を導く直前の exact estimate に対応する。
-/

namespace Collatz2

namespace StandardOddRuns

/-- Hercher Lemma 8: consecutive odd-run の2進合同。 -/
theorem hercherLemma8_dvd
    {k n y : ℕ}
    (R : StandardOddRuns k n y) :
    2 ^ k ∣ n + 1 :=
  R.twoPow_dvd_start_add_one

/-- Hercher Lemma 8: local minimum の size lower bound。 -/
theorem hercherLemma8_lower
    {k n y : ℕ}
    (R : StandardOddRuns k n y) :
    2 ^ k - 1 ≤ n :=
  R.twoPow_sub_one_le_start

end StandardOddRuns

namespace Word.MountainRun

/-- actual mountain 上の Hercher Lemma 8。 -/
theorem hercherLemma8_mountain
    {w : Word} {n next : ℕ}
    (M : Word.MountainRun w n next) :
    2 ^ M.shape.oddRunLength - 1 ≤ n :=
  M.start_ge_twoPow_sub_one

/-- actual mountain 上の Hercher Lemma 20 integer core。 -/
theorem hercherLemma20_integer
    {w : Word} {n next : ℕ}
    (M : Word.MountainRun w n next) :
    2 ^ (M.shape.oddRunLength + 1) * next <
      3 ^ M.shape.oddRunLength * (n + 1) :=
  M.hercherLemma20_divisionFree

/--
Hercher Lemma 20 core を ratio の cross-multiplied formで読む。

  2*next / (n+1) < (3/2)^k

の division-free shadow。
-/
theorem two_mul_next_scaled_lt
    {w : Word} {n next : ℕ}
    (M : Word.MountainRun w n next) :
    (2 * next) * 2 ^ M.shape.oddRunLength <
      (n + 1) * 3 ^ M.shape.oddRunLength := by
  have h := M.hercherLemma20_integer
  rw [pow_succ] at h
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

end Word.MountainRun
end Collatz2
