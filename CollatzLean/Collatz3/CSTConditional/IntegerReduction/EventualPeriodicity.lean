import CollatzLean.Collatz3.CSTConditional.IntegerReduction.ExponentialEscapeReduction
import Mathlib.Tactic.Ring

/-!
# Collatz3 CSTConditional IntegerReduction: 周期 exponent tail の剛性

同じ正 exponent stream を二つの奇整数 recurrence が実現するなら、
全有限 prefix の canonical residue が同じなので初期値は一意である。

この一意性を tail に適用すると、exponent stream が period `p>0` で純周期なら
value も `p` 後に同じ値へ戻らなければならない。
一方 period block が coefficient-expanding

`2^H < 3^p`

なら affine translation の正性により同値 return は不可能。

従って expanding な eventually-periodic exponent tail は排除される。
これは独立整数 recurrence の定理であり、actual Collatz orbit を使わない。
-/

namespace Collatz3
namespace IntegerReduction

/-- 自然数列の time shift。 -/
def shiftSeq
    (a : ℕ → ℕ)
    (start : ℕ) : ℕ → ℕ :=
  fun n => a (start + n)

/-- positive exponent stream では prefix depth は index 以上。 -/
theorem index_le_prefixDepth
    {e : ℕ → ℕ}
    (hPos : ∀ n : ℕ, 0 < e n)
    (m : ℕ) :
    m ≤ prefixDepth e m := by
  induction m with
  | zero => simp [prefixDepth, prefixWord]
  | succ m ih =>
      rw [prefixDepth_succ]
      have hm := hPos m
      omega

private theorem nat_lt_twoPow_succ
    (n : ℕ) :
    n < 2 ^ (n + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega, pow_succ]
      have hPos : 0 < 2 ^ (n + 1) := by positivity
      omega

/--
同じ positive exponent stream を実現する二つの奇整数 recurrence は開始値が一致する。
-/
theorem oddRecurrence_start_unique
    {e y z : ℕ → ℕ}
    (hy : RunsOddRecurrence e y)
    (hz : RunsOddRecurrence e z) :
    y 0 = z 0 := by
  let m : ℕ := max (y 0) (z 0)
  have hDepth : m ≤ prefixDepth e m :=
    index_le_prefixDepth hy.exponent_pos m
  have hPowMono :
      2 ^ (m + 1) ≤ 2 ^ (prefixDepth e m + 1) :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega)
  have hyLt : y 0 < 2 ^ (prefixDepth e m + 1) := by
    have h0 : y 0 ≤ m := Nat.le_max_left _ _
    exact lt_of_le_of_lt h0 (lt_of_lt_of_le (nat_lt_twoPow_succ m) hPowMono)
  have hzLt : z 0 < 2 ^ (prefixDepth e m + 1) := by
    have h0 : z 0 ≤ m := Nat.le_max_right _ _
    exact lt_of_le_of_lt h0 (lt_of_lt_of_le (nat_lt_twoPow_succ m) hPowMono)
  have hyMod := hy.start_mod_eq_canonicalResidue m
  have hzMod := hz.start_mod_eq_canonicalResidue m
  rw [Nat.mod_eq_of_lt hyLt] at hyMod
  rw [Nat.mod_eq_of_lt hzLt] at hzMod
  omega

/-- recurrence は shift しても同じ形。 -/
theorem RunsOddRecurrence.shift
    {e y : ℕ → ℕ}
    (h : RunsOddRecurrence e y)
    (start : ℕ) :
    RunsOddRecurrence (shiftSeq e start) (shiftSeq y start) := by
  intro n
  have hn := h (start + n)
  dsimp [shiftSeq]
  simpa [Nat.add_assoc] using hn

/-- exponent tail が period `p` なら、`p` だけずらした value tail も同じ exponent stream を走る。 -/
theorem RunsOddRecurrence.shift_period
    {e y : ℕ → ℕ}
    (h : RunsOddRecurrence e y)
    {start p : ℕ}
    (hPer : ∀ n : ℕ, e (start + p + n) = e (start + n)) :
    RunsOddRecurrence (shiftSeq e start) (shiftSeq y (start + p)) := by
  intro n
  have hn := h (start + p + n)
  rcases hn with ⟨he, hyOdd, hEq⟩
  refine ⟨?_, hyOdd, ?_⟩
  · dsimp [shiftSeq]
    rw [← hPer n]
    exact he
  · have hEq' := hEq
    rw [hPer n] at hEq'
    dsimp [shiftSeq]
    simpa [Nat.add_assoc] using hEq'

/--
periodic exponent tail では recurrence value も一周期後に同じ値へ戻る。
-/
theorem value_eq_add_period_of_exponent_periodic
    {e y : ℕ → ℕ}
    (h : RunsOddRecurrence e y)
    {start p : ℕ}
    (hPer : ∀ n : ℕ, e (start + p + n) = e (start + n)) :
    y (start + p) = y start := by
  have h₀ := h.shift start
  have h₁ := h.shift_period hPer
  have hEq := oddRecurrence_start_unique h₀ h₁
  simpa [shiftSeq] using hEq.symm

/--
純周期 tail の一周期 block が coefficient-expanding なら矛盾。

`2^H < 3^p` と positive affine translation のため、同値 return は起こせない。
-/
theorem not_eventuallyPeriodic_of_period_expanding
    {e y : ℕ → ℕ}
    (h : RunsOddRecurrence e y)
    {start p : ℕ}
    (hp : 0 < p)
    (hPer : ∀ n : ℕ, e (start + p + n) = e (start + n))
    (hExpand :
      2 ^ Word.twoSteps (streamWord e start p) < 3 ^ p) :
    False := by
  have hReturn : y (start + p) = y start :=
    value_eq_add_period_of_exponent_periodic h hPer
  have hShift := h.shift start
  have hPrefix := hShift.prefixEquation p
  have hDepth :
      prefixDepth (shiftSeq e start) p =
        Word.twoSteps (streamWord e start p) := by
    clear hp hPer hExpand hReturn hPrefix
    induction p with
    | zero =>
        simp [prefixDepth, prefixWord, streamWord]
    | succ p ih =>
        rw [prefixDepth_succ, streamWord_succ, Word.twoSteps_append]
        simp [shiftSeq, ih]
  have hAffinePos : 0 < prefixAffine (shiftSeq e start) p := by
    cases p with
    | zero => simp at hp
    | succ q =>
        rw [prefixAffine_succ]
        positivity
  have hyPos : 0 < y start := by
    rcases h.value_odd start with ⟨q, hq⟩
    omega
  have hEq :
      2 ^ Word.twoSteps (streamWord e start p) * y start =
        3 ^ p * y start + prefixAffine (shiftSeq e start) p := by
    rw [← hDepth]
    simpa [shiftSeq, hReturn] using hPrefix
  have hLeft :
      2 ^ Word.twoSteps (streamWord e start p) * y start <
        3 ^ p * y start :=
    (Nat.mul_lt_mul_right hyPos).2 hExpand
  omega

end IntegerReduction
end Collatz3
