import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Monotone suffix Hensel chain

このファイルは Collatz / Ferrers / Beatty / restarted geometry から独立した
純粋な整数算術だけを扱う。

長さ `w` の chain を

  q_w = 0,
  3 q_i = 2 q_{i+1} + 2^(delta_i) - 1,
  delta_0 = 1,
  delta_(i+1) - delta_i in {0,1}

で抽象化する。

ここでは現在確実に証明できる局所 rigidity だけを入れる。

* `delta_i` は正。
* `i < w` なら `q_i` は奇数。
* terminal exponent `delta_(w-1)` は偶数。
* 次状態 `(q_(i+1), delta_(i+1))` に対する staircase predecessor は高々一つ。
* 従って actual chain の内部 backward transition は deterministic。

「terminal exponent > 2 の branch は有限時間で必ず死ぬ」という global termination、
および full suffix Hensel rigidity はこのファイルでは仮定も主張もしない。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
monotone `0/1` staircase と全 suffix quotient が満たす純粋 Hensel chain。

`q` と `delta` は全自然数上の関数として持つが、意味があるのは
`0 <= i <= width` の範囲だけである。
-/
structure MonotoneSuffixHenselChain where
  width : ℕ
  width_pos : 0 < width
  delta : ℕ → ℕ
  q : ℕ → ℤ
  delta_zero : delta 0 = 1
  delta_step :
    ∀ i : ℕ, i + 1 < width →
      delta (i + 1) = delta i ∨
        delta (i + 1) = delta i + 1
  q_terminal : q width = 0
  recurrence :
    ∀ i : ℕ, i < width →
      3 * q i =
        2 * q (i + 1) + (2 : ℤ) ^ delta i - 1

namespace MonotoneSuffixHenselChain

/-- staircase は `delta_0 = 1` から始まり下がらないので、occupied index の exponent は正。 -/
theorem delta_pos
    (C : MonotoneSuffixHenselChain)
    {i : ℕ}
    (hi : i < C.width) :
    0 < C.delta i := by
  induction i with
  | zero =>
      rw [C.delta_zero]
      omega
  | succ i ih =>
      have hiPrev : i < C.width := by omega
      have hPrev : 0 < C.delta i := ih hiPrev
      have hStep := C.delta_step i (by omega)
      change 0 < C.delta (i + 1)
      rcases hStep with hSame | hUp
      · rw [hSame]
        exact hPrev
      · rw [hUp]
        omega

/-- `2^n mod 3` は exponent の parity だけで決まる。 -/
private theorem twoPow_mod_three
    (n : ℕ) :
    (2 : ℤ) ^ n % 3 =
      if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hnlt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
      have hnCases : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hnCases with hn | hn
      · have hsucc : (n + 1) % 2 = 1 := by omega
        rw [pow_succ, Int.mul_emod, ih]
        norm_num [hn, hsucc, Nat.succ_eq_add_one]
      · have hsucc : (n + 1) % 2 = 0 := by omega
        rw [pow_succ, Int.mul_emod, ih]
        norm_num [hn, hsucc, Nat.succ_eq_add_one]

/-- `3` はどの `2` の冪も割らない。 -/
private theorem three_not_dvd_twoPow
    (n : ℕ) :
    ¬ (3 : ℤ) ∣ (2 : ℤ) ^ n := by
  intro hDiv
  rcases hDiv with ⟨z, hz⟩
  have hMod : (2 : ℤ) ^ n % 3 = 0 := by
    rw [hz]
    simp
  rw [twoPow_mod_three n] at hMod
  by_cases hn : n % 2 = 0
  · norm_num [hn] at hMod
  · norm_num [hn] at hMod

/-- `3^e` と `2^a` は coprime なので、dyadic factor を 3-adic divisibility から消せる。 -/
theorem threePow_dvd_cancel_twoPow
    {e a : ℕ}
    {z : ℤ}
    (hDiv :
      (3 : ℤ) ^ e ∣ (2 : ℤ) ^ a * z) :
    (3 : ℤ) ^ e ∣ z := by
  have hThreeTwo : IsCoprime (3 : ℤ) (2 : ℤ) := by
    refine ⟨1, -1, ?_⟩
    norm_num
  have hCoprime :
      IsCoprime ((3 : ℤ) ^ e) ((2 : ℤ) ^ a) := by
    exact hThreeTwo.pow
  exact hCoprime.dvd_of_dvd_mul_left hDiv

/-- positive-length の quotient `q_i` は偶数ではない、すなわち奇数。 -/
theorem q_not_even
    (C : MonotoneSuffixHenselChain)
    {i : ℕ}
    (hi : i < C.width) :
    ¬ (2 : ℤ) ∣ C.q i := by
  intro hEven
  rcases hEven with ⟨a, ha⟩
  have hDelta : 0 < C.delta i := C.delta_pos hi
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hDelta)
  have hPowEven :
      (2 : ℤ) ∣ (2 : ℤ) ^ C.delta i := by
    refine ⟨(2 : ℤ) ^ d, ?_⟩
    rw [hd, pow_succ]
    ring
  rcases hPowEven with ⟨b, hb⟩
  have hRec := C.recurrence i hi
  rw [ha, hb] at hRec
  omega

/-- terminal recurrence と `q_width = 0` から terminal exponent は偶数。 -/
theorem terminal_delta_mod_two_eq_zero
    (C : MonotoneSuffixHenselChain) :
    C.delta (C.width - 1) % 2 = 0 := by
  have hw : 0 < C.width := C.width_pos
  have hi : C.width - 1 < C.width := by omega
  have hRec := C.recurrence (C.width - 1) hi
  have hIdx : C.width - 1 + 1 = C.width := by omega
  rw [hIdx, C.q_terminal] at hRec
  have hDiv :
      (3 : ℤ) ∣
        (2 : ℤ) ^ C.delta (C.width - 1) - 1 := by
    refine ⟨C.q (C.width - 1), ?_⟩
    linarith
  rcases hDiv with ⟨z, hz⟩
  have hPowMod :
      (2 : ℤ) ^ C.delta (C.width - 1) % 3 = 1 := by
    have hz' :
        (2 : ℤ) ^ C.delta (C.width - 1) = 3 * z + 1 := by
      linarith
    rw [hz']
    simp
  rw [twoPow_mod_three (C.delta (C.width - 1))] at hPowMod
  by_contra hne
  have hlt : C.delta (C.width - 1) % 2 < 2 :=
    Nat.mod_lt _ (by norm_num)
  have hodd : C.delta (C.width - 1) % 2 = 1 := by omega
  norm_num [hodd] at hPowMod

/--
右側 state `(qNext, deltaNext)` に対する staircase predecessor。

predecessor exponent は `deltaNext` と同じか一つ小さいかのどちらかで、
recurrence を exact に満たすことを要求する。
-/
def IsBackwardPredecessor
    (qNext : ℤ)
    (deltaNext deltaPrev : ℕ)
    (qPrev : ℤ) : Prop :=
  (deltaPrev = deltaNext ∨ deltaPrev + 1 = deltaNext) ∧
    3 * qPrev =
      2 * qNext + (2 : ℤ) ^ deltaPrev - 1

/--
固定した右側 state に対する staircase predecessor は高々一つ。

二つの候補 exponent が異なるなら差は exact に 1 であり、
二つの recurrence の差から `3 | 2^d` が出て矛盾する。
-/
theorem backwardPredecessor_unique
    {qNext : ℤ}
    {deltaNext d₁ d₂ : ℕ}
    {q₁ q₂ : ℤ}
    (h₁ : IsBackwardPredecessor qNext deltaNext d₁ q₁)
    (h₂ : IsBackwardPredecessor qNext deltaNext d₂ q₂) :
    d₁ = d₂ ∧ q₁ = q₂ := by
  rcases h₁ with ⟨hd₁, hrec₁⟩
  rcases h₂ with ⟨hd₂, hrec₂⟩
  have hd : d₁ = d₂ := by
    rcases hd₁ with h₁Same | h₁Down
    · rcases hd₂ with h₂Same | h₂Down
      · omega
      · have hD : d₁ = d₂ + 1 := by omega
        have hPow :
            (2 : ℤ) ^ d₁ = 2 * (2 : ℤ) ^ d₂ := by
          rw [hD, pow_succ]
          ring
        have hThree :
            (3 : ℤ) ∣ (2 : ℤ) ^ d₂ := by
          refine ⟨q₁ - q₂, ?_⟩
          rw [hPow] at hrec₁
          linarith
        exact (three_not_dvd_twoPow d₂ hThree).elim
    · rcases hd₂ with h₂Same | h₂Down
      · have hD : d₂ = d₁ + 1 := by omega
        have hPow :
            (2 : ℤ) ^ d₂ = 2 * (2 : ℤ) ^ d₁ := by
          rw [hD, pow_succ]
          ring
        have hThree :
            (3 : ℤ) ∣ (2 : ℤ) ^ d₁ := by
          refine ⟨q₂ - q₁, ?_⟩
          rw [hPow] at hrec₂
          linarith
        exact (three_not_dvd_twoPow d₁ hThree).elim
      · omega
  have hq : q₁ = q₂ := by
    rw [← hd] at hrec₂
    linarith
  exact ⟨hd, hq⟩

/-- actual chain の内部一段は `IsBackwardPredecessor` を満たす。 -/
theorem actual_isBackwardPredecessor
    (C : MonotoneSuffixHenselChain)
    {i : ℕ}
    (hi : i + 1 < C.width) :
    IsBackwardPredecessor
      (C.q (i + 1))
      (C.delta (i + 1))
      (C.delta i)
      (C.q i) := by
  constructor
  · rcases C.delta_step i hi with hSame | hUp
    · exact Or.inl hSame.symm
    · exact Or.inr hUp.symm
  · exact C.recurrence i (by omega)

/--
actual chain の右側 state を固定すると、内部 predecessor は deterministic。

これは global termination を主張しない。存在する predecessor が actual predecessor と
一致する、という局所一意性だけである。
-/
theorem backward_deterministic
    (C : MonotoneSuffixHenselChain)
    {i : ℕ}
    (hi : i + 1 < C.width)
    {d : ℕ}
    {qPrev : ℤ}
    (hPrev :
      IsBackwardPredecessor
        (C.q (i + 1))
        (C.delta (i + 1))
        d
        qPrev) :
    d = C.delta i ∧ qPrev = C.q i := by
  exact
    backwardPredecessor_unique
      hPrev
      (C.actual_isBackwardPredecessor hi)

end MonotoneSuffixHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
