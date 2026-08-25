import CollatzLean.Collatz2.CSTMicro.FerrersBoundarySturmian

/-!
# Critical Sturmian one positions = Beatty positions

`β = log₂ 3` を Lean の実数対数として導入せず、

  floor (n * β)

を power inequality だけで特徴付ける。

`beattyIndex n` は `3^n ≤ 2^(q+1)` を初めて満たす `q`。
`n > 0` では最小性から

  2^q < 3^n ≤ 2^(q+1)

であり、数学的に `q = floor (n * log₂ 3)`。

この index が critical upper mechanical/Sturmian word の
`(n+1)` 個目の `true` の位置であることを証明する。
-/

namespace Collatz2
namespace CSTMicro

/-- `3^n` を上から挟む 2 冪は必ず存在する。 -/
theorem exists_beatty_upper (n : ℕ) :
    ∃ q : ℕ, 3 ^ n ≤ 2 ^ (q + 1) := by
  induction n with
  | zero =>
      exact ⟨0, by norm_num⟩
  | succ n ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨q + 2, ?_⟩
      rw [pow_succ]
      have hmul :
          3 ^ n * 3 ≤ 2 ^ (q + 1) * 4 :=
        Nat.mul_le_mul hq (by norm_num)
      calc
        3 ^ n * 3 ≤ 2 ^ (q + 1) * 4 := hmul
        _ = 2 ^ ((q + 2) + 1) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]

/--
`floor (n log₂ 3)` の exact power-form version。

`3^n ≤ 2^(q+1)` を初めて満たす q を取る。
-/
def beattyIndex (n : ℕ) : ℕ :=
  Nat.find (exists_beatty_upper n)

/-- Beatty index 自身は upper inequality を満たす。 -/
theorem beattyIndex_upper (n : ℕ) :
    3 ^ n ≤ 2 ^ (beattyIndex n + 1) := by
  exact Nat.find_spec (exists_beatty_upper n)

/-- Beatty index の最小性。 -/
theorem beattyIndex_le_of_upper
    {n q : ℕ}
    (h : 3 ^ n ≤ 2 ^ (q + 1)) :
    beattyIndex n ≤ q := by
  exact Nat.find_min' (exists_beatty_upper n) h

/-- Beatty index より下では upper inequality はまだ成立しない。 -/
theorem not_beatty_upper_below
    {n q : ℕ}
    (hq : q < beattyIndex n) :
    ¬ (3 ^ n ≤ 2 ^ (q + 1)) := by
  intro h
  have hmin := beattyIndex_le_of_upper h
  omega

theorem beattyIndex_lower (n : ℕ) :
    2 ^ beattyIndex n ≤ 3 ^ n := by
  let q := beattyIndex n
  by_cases hq0 : q = 0
  · have hidx0 : beattyIndex n = 0 := by
      simpa [q] using hq0
    rw [hidx0]
    have hpos : 0 < 3 ^ n := Nat.pow_pos (by norm_num)
    omega
  · have hqPos : 0 < q := Nat.pos_of_ne_zero hq0
    let r := q - 1
    have hrLt : r < q := by
      dsimp [r]
      omega
    have hnot :
        ¬ (3 ^ n ≤ 2 ^ (r + 1)) := by
      apply not_beatty_upper_below (n := n) (q := r)
      simpa [q] using hrLt
    have hrSucc : r + 1 = q := by
      dsimp [r]
      omega
    have hnotQ :
        ¬ (3 ^ n ≤ 2 ^ q) := by
      simpa [hrSucc] using hnot
    have hlt :
        2 ^ q < 3 ^ n := by
      exact Nat.lt_of_not_ge hnotQ
    simpa [q] using Nat.le_of_lt hlt

/-- `n>0` では lower inequality は strict。 -/
theorem beattyIndex_lower_strict_of_pos
    {n : ℕ}
    (hn : 0 < n) :
    2 ^ beattyIndex n < 3 ^ n := by
  let q := beattyIndex n
  have hqPos : 0 < q := by
    by_contra hq0
    have hqEq : q = 0 := by omega
    have hup := beattyIndex_upper n
    rw [show beattyIndex n = 0 by simpa [q] using hqEq] at hup
    have hthree : 3 ≤ 3 ^ n := by
      cases n with
      | zero => omega
      | succ t =>
          rw [pow_succ]
          have hp : 0 < 3 ^ t := Nat.pow_pos (by omega)
          nlinarith
    norm_num at hup
    omega
  let r := q - 1
  have hrLt : r < q := by
    simp [r]
    omega
  have hnot := not_beatty_upper_below (n := n) (q := r) (by simpa [q] using hrLt)
  have hrSucc : r + 1 = q := by
    simp [r]
    omega
  have hnot' : ¬ (3 ^ n ≤ 2 ^ q) := by
    simpa [hrSucc, q] using hnot
  have hlt : 2 ^ q < 3 ^ n := by
    exact Nat.lt_of_not_ge hnot'
  simpa [q] using hlt

/--
`2^s < 3^r` なら、`r` rank 進む間に Beatty index は少なくとも `s` 増える。

特定の `r=2, s=3` に依存しない power-form の増分下界。
-/
theorem beattyIndex_add_lower_of_twoPow_lt_threePow
    {k r s : ℕ}
    (h : 2 ^ s < 3 ^ r) :
    beattyIndex k + s ≤ beattyIndex (k + r) := by
  have hLower := beattyIndex_lower k
  have hStrict :
      2 ^ (beattyIndex k + s) < 3 ^ (k + r) := by
    calc
      2 ^ (beattyIndex k + s)
          = 2 ^ beattyIndex k * 2 ^ s := by
              rw [pow_add]
      _ ≤ 3 ^ k * 2 ^ s := by
            exact Nat.mul_le_mul_right (2 ^ s) hLower
      _ < 3 ^ k * 3 ^ r := by
            exact Nat.mul_lt_mul_of_pos_left h (by positivity)
      _ = 3 ^ (k + r) := by
            rw [pow_add]
  by_contra hnot
  have hIndex :
      beattyIndex (k + r) < beattyIndex k + s := by
    omega
  have hUpper := beattyIndex_upper (k + r)
  have hExpLe :
      beattyIndex (k + r) + 1 ≤ beattyIndex k + s := by
    omega
  have hPowLe :
      2 ^ (beattyIndex (k + r) + 1) ≤
        2 ^ (beattyIndex k + s) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hExpLe
  exact (not_lt_of_ge (le_trans hUpper hPowLe)) hStrict

/--
`3^r ≤ 2^s` なら、`r` rank 進む間の Beatty index 増分は高々 `s`。

一 step `+2` upper bound を含む一般形。
-/
theorem beattyIndex_add_upper_of_threePow_le_twoPow
    {k r s : ℕ}
    (h : 3 ^ r ≤ 2 ^ s) :
    beattyIndex (k + r) ≤ beattyIndex k + s := by
  apply beattyIndex_le_of_upper
  have hUpper := beattyIndex_upper k
  calc
    3 ^ (k + r)
        = 3 ^ k * 3 ^ r := by
            rw [pow_add]
    _ ≤ 2 ^ (beattyIndex k + 1) * 2 ^ s :=
      Nat.mul_le_mul hUpper h
    _ = 2 ^ ((beattyIndex k + s) + 1) := by
      rw [← pow_add]
      congr 1
      omega

/--
隣接する dyadic bracket
`2^t < 3^m ≤ 2^(t+1)` は Beatty index を exact に `t` へ固定する。
-/
theorem beattyIndex_eq_of_adjacent_dyadic_bracket
    {m t : ℕ}
    (hLow : 2 ^ t < 3 ^ m)
    (hHigh : 3 ^ m ≤ 2 ^ (t + 1)) :
    beattyIndex m = t := by
  apply Nat.le_antisymm
  · exact beattyIndex_le_of_upper hHigh
  · by_contra hnot
    have hLt : beattyIndex m < t := by
      omega
    have hUpper := beattyIndex_upper m
    have hExpLe : beattyIndex m + 1 ≤ t := by
      omega
    have hPowLe :
        2 ^ (beattyIndex m + 1) ≤ 2 ^ t :=
      Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) hExpLe
    exact (not_lt_of_ge (le_trans hUpper hPowLe)) hLow

/-- `beattyIndex 0 = 0`。 -/
@[simp] theorem beattyIndex_zero : beattyIndex 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply beattyIndex_le_of_upper
  norm_num

/-- Beatty index は strict に増加する。 -/
theorem beattyIndex_lt_succ (n : ℕ) :
    beattyIndex n < beattyIndex (n + 1) := by
  let q := beattyIndex n
  have hlower := beattyIndex_lower n
  have hstrict : 2 ^ (q + 1) < 3 ^ (n + 1) := by
    rw [pow_succ, pow_succ]
    have hp : 0 < 2 ^ q := Nat.pow_pos (by omega)
    nlinarith
  by_contra hnot
  have hle : beattyIndex (n + 1) ≤ q := by omega
  have hu := beattyIndex_upper (n + 1)
  have hpow :
      2 ^ (beattyIndex (n + 1) + 1) ≤ 2 ^ (q + 1) :=
    Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) (by omega)
  omega

/-- Beatty index は strict monotone。 -/
theorem beattyIndex_strictMono
    {a b : ℕ}
    (h : a < b) :
    beattyIndex a < beattyIndex b := by
  induction b with
  | zero => omega
  | succ b ih =>
      by_cases hab : a = b
      · subst a
        exact beattyIndex_lt_succ b
      · have hab' : a < b := by omega
        exact lt_trans (ih hab') (beattyIndex_lt_succ b)

/--
Beatty position の直前までにちょうど n 個の one がある。
-/
theorem criticalPrefixHeight_beattyIndex (n : ℕ) :
    criticalPrefixHeight (beattyIndex n) = n := by
  cases n with
  | zero =>
      simp
  | succ n =>
      let q := beattyIndex (n + 1)
      have hqPos : 0 < q := by
        by_contra hq0
        have hqEq : q = 0 := by
          omega
        have hup := beattyIndex_upper (n + 1)
        rw [
          show beattyIndex (n + 1) = 0 by
            simpa [q] using hqEq
        ] at hup
        have hthree : 3 ≤ 3 ^ (n + 1) := by
          rw [pow_succ]
          have hp : 0 < 3 ^ n :=
            Nat.pow_pos (by omega)
          nlinarith
        norm_num at hup
        omega
      have hExp : 2 ^ q < 3 ^ (n + 1) := by
        simpa [q] using
          beattyIndex_lower_strict_of_pos
            (show 0 < n + 1 by omega)
      have hcritLe : criticalHeight q ≤ n + 1 :=
        criticalHeight_le_of_expanding hExp
      have hUpper := beattyIndex_upper (n + 1)
      have hUpperQ :
          3 ^ n * 3 ≤ 2 ^ q * 2 := by
        simpa [q, pow_succ] using hUpper
      have hPrev : 3 ^ n ≤ 2 ^ q := by
        by_contra hnot
        have hgt : 2 ^ q < 3 ^ n := by
          exact Nat.lt_of_not_ge hnot
        have htwoPos : 0 < (2 : ℕ) := by
          norm_num
        have hmul :
            2 ^ q * 2 < 3 ^ n * 2 :=
          (Nat.mul_lt_mul_right htwoPos).2 hgt
        have hp : 0 < 3 ^ n :=
          Nat.pow_pos (by norm_num)
        have h23 :
            3 ^ n * 2 < 3 ^ n * 3 :=
          (Nat.mul_lt_mul_left hp).2 (by norm_num)
        have hcontra :
            2 ^ q * 2 < 3 ^ n * 3 :=
          lt_trans hmul h23
        exact (not_lt_of_ge hUpperQ) hcontra
      have hcritGe : n + 1 ≤ criticalHeight q := by
        by_contra hnot
        have hleN : criticalHeight q ≤ n := by
          omega
        have hpow :
            3 ^ criticalHeight q ≤ 3 ^ n :=
          Nat.pow_le_pow_right
            (by omega : 0 < (3 : ℕ))
            hleN
        have hcExp := criticalHeight_expanding q
        omega
      have hcritEq : criticalHeight q = n + 1 := by
        omega
      change criticalPrefixHeight q = n + 1
      cases hq : q with
      | zero =>
          have hne : q ≠ 0 :=
            Nat.ne_of_gt hqPos
          exact (hne hq).elim
      | succ t =>
          rw [hq] at hcritEq
          simpa [criticalPrefixHeight] using hcritEq

/--
`floor(n log₂3)` の位置は critical Sturmian word の true step。
-/
theorem criticalSturmianBit_beattyIndex (n : ℕ) :
    criticalSturmianBit (beattyIndex n) = true := by
  let q := beattyIndex n
  have hBefore : criticalPrefixHeight q = n := by
    simpa [q] using criticalPrefixHeight_beattyIndex n
  have hmono := criticalPrefixHeight_mono q
  have hstep := criticalPrefixHeight_succ_le q
  have hUpper := beattyIndex_upper n
  have hAfter : criticalPrefixHeight (q + 1) = n + 1 := by
    have hge : n + 1 ≤ criticalPrefixHeight (q + 1) := by
      by_contra hnot
      have heq : criticalPrefixHeight (q + 1) = n := by
        rw [hBefore] at hmono hstep
        omega
      have hq1Pos : 0 < q + 1 := by omega
      have hcritEq : criticalHeight (q + 1) = n := by
        simpa [criticalPrefixHeight_eq_criticalHeight_of_pos hq1Pos] using heq
      have hExp := criticalHeight_expanding (q + 1)
      rw [hcritEq] at hExp
      have hUpperQ :
          3 ^ n ≤ 2 ^ (q + 1) := by
        simpa [q] using hUpper
      exact (not_lt_of_ge hUpperQ) hExp
    rw [hBefore] at hstep
    omega
  apply (criticalSturmianBit_eq_true_iff q).2
  rw [hBefore, hAfter]

/--
Beatty positionでは prefix height が `n -> n+1` と exact に増える。
これが「(n+1) 個目の one の位置 = floor(n log₂3)」の power-form。
-/
theorem beattyIndex_is_nth_critical_one (n : ℕ) :
    criticalPrefixHeight (beattyIndex n) = n ∧
      criticalPrefixHeight (beattyIndex n + 1) = n + 1 := by
  constructor
  · exact criticalPrefixHeight_beattyIndex n
  · have hbit := criticalSturmianBit_beattyIndex n
    have hstep := criticalPrefixHeight_step (beattyIndex n)
    have hBefore := criticalPrefixHeight_beattyIndex n
    rw [hbit] at hstep
    rw [hBefore] at hstep
    simpa [bitNat] using hstep

/-- critical prefix height の global monotonicity。 -/
theorem criticalPrefixHeight_mono_of_le
    {a b : ℕ}
    (h : a ≤ b) :
    criticalPrefixHeight a ≤ criticalPrefixHeight b := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst a
      exact le_rfl
  | succ b ih =>
      by_cases hab : a = b + 1
      · subst a
        exact le_rfl
      · have hab' : a ≤ b := by omega
        exact le_trans (ih hab') (criticalPrefixHeight_mono b)

/--
critical word で true が出る位置は、その直前 height の Beatty index に一意。
-/
theorem critical_true_position_eq_beattyIndex
    {i : ℕ}
    (hbit : criticalSturmianBit i = true) :
    i = beattyIndex (criticalPrefixHeight i) := by
  let m := criticalPrefixHeight i
  let q := beattyIndex m
  have hqHeight : criticalPrefixHeight q = m := by
    simpa [q, m] using criticalPrefixHeight_beattyIndex m
  have hiStep := criticalPrefixHeight_step i
  rw [hbit] at hiStep
  have hiAfter : criticalPrefixHeight (i + 1) = m + 1 := by
    simpa [m, bitNat] using hiStep
  have hqBit : criticalSturmianBit q = true := by
    simpa [q] using criticalSturmianBit_beattyIndex m
  have hqStep := criticalPrefixHeight_step q
  rw [hqBit] at hqStep
  rw [hqHeight] at hqStep
  have hqAfter : criticalPrefixHeight (q + 1) = m + 1 := by
    simpa [bitNat] using hqStep
  by_contra hne
  by_cases hiq : i < q
  · have hmon :=
      criticalPrefixHeight_mono_of_le
        (show i + 1 ≤ q by omega)
    rw [hiAfter, hqHeight] at hmon
    omega
  · have hneQ : i ≠ q := by
      simpa [q, m] using hne
    have hqi : q < i := by
      omega
    have hmon :=
      criticalPrefixHeight_mono_of_le
        (show q + 1 ≤ i by omega)
    change criticalPrefixHeight (q + 1) ≤ m at hmon
    rw [hqAfter] at hmon
    omega

end CSTMicro
end Collatz2
