import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselChain

/-!
# Monotone suffix Hensel chain: finite terminal certificates through exponent 36

このファイルは Collatz / Ferrers / Beatty geometry から独立した pure arithmetic 層。

右端 state

  (delta, q)

から一段左の predecessor は `IsBackwardPredecessor` で表される。
既存 theorem `backwardPredecessor_unique` により、fixed right state に対する
predecessor は高々一つである。

ここでは terminal exponent `4,6,...,36` について、右端から deterministic に
逆向きに辿る certificate を与える。各 certificate は最大 7 step で
predecessor 不存在 state に到達する。

重要なのは「全 staircase word を列挙」しないこと。
各 terminal exponent につき一本道の certificate を一つだけ検証する。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

namespace MonotoneSuffixHenselChain

/-- `delta_i ≤ i+1`。`delta_0=1` と一段増分 `0/1` だけから従う。 -/
theorem delta_le_index_add_one
    (C : MonotoneSuffixHenselChain)
    {i : ℕ}
    (hi : i < C.width) :
    C.delta i ≤ i + 1 := by
  induction i with
  | zero =>
      rw [C.delta_zero]
  | succ i ih =>
      have hiPrev : i < C.width := by omega
      have hPrev := ih hiPrev
      have hStep := C.delta_step i hi
      rcases hStep with hSame | hUp
      · rw [hSame]
        omega
      · rw [hUp]
        omega

/-- terminal exponent は width 以下。 -/
theorem terminal_delta_le_width
    (C : MonotoneSuffixHenselChain) :
    C.delta (C.width - 1) ≤ C.width := by
  have hi : C.width - 1 < C.width := by
    have hw := C.width_pos
    omega
  have h := C.delta_le_index_add_one hi
  omega

/-- terminal recurrence を右端 state の形にしたもの。 -/
theorem terminal_recurrence_eq
    (C : MonotoneSuffixHenselChain) :
    3 * C.q (C.width - 1) =
      (2 : ℤ) ^ C.delta (C.width - 1) - 1 := by
  have hi : C.width - 1 < C.width := by
    have hw := C.width_pos
    omega
  have hRec := C.recurrence (C.width - 1) hi
  have hIdx : C.width - 1 + 1 = C.width := by
    have hw := C.width_pos
    omega
  rw [hIdx, C.q_terminal] at hRec
  linarith

/-- concrete backward certificate で使う state。 -/
structure BackwardHenselState where
  delta : ℕ
  q : ℤ
  deriving DecidableEq, Repr

/--
`k` 回 predecessor を辿ると、そこで predecessor 不存在になる certificate。

`step` の向きは

  right state `s`  <- predecessor `prev`

である。
-/
inductive BackwardDiesWithin : BackwardHenselState → ℕ → Prop
  | dead {s : BackwardHenselState}
      (hdead :
        ∀ d : ℕ, ∀ q : ℤ,
          ¬ IsBackwardPredecessor s.q s.delta d q) :
      BackwardDiesWithin s 0
  | step {s prev : BackwardHenselState} {k : ℕ}
      (hpred :
        IsBackwardPredecessor s.q s.delta prev.delta prev.q)
      (hrest : BackwardDiesWithin prev k) :
      BackwardDiesWithin s (k + 1)

/-- `2^n mod 3` は exponent parity だけで決まる。 -/
private theorem finite36_twoPow_mod_three
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
private theorem finite36_three_not_dvd_twoPow
    (n : ℕ) :
    ¬ (3 : ℤ) ∣ (2 : ℤ) ^ n := by
  intro hDiv
  rcases hDiv with ⟨z, hz⟩
  have hMod : (2 : ℤ) ^ n % 3 = 0 := by
    rw [hz]
    simp
  rw [finite36_twoPow_mod_three n] at hMod
  by_cases hn : n % 2 = 0
  · norm_num [hn] at hMod
  · norm_num [hn] at hMod

/--
`qNext ≡ 2 (mod 3)` の代わりに `3 ∣ qNext-2` と書いた dead-state criterion。
このとき recurrence は `3 ∣ 2^d` を強制して矛盾する。
-/
theorem no_backwardPredecessor_of_three_dvd_q_sub_two
    {qNext : ℤ}
    {deltaNext : ℕ}
    (hMod : (3 : ℤ) ∣ qNext - 2) :
    ∀ d : ℕ, ∀ qPrev : ℤ,
      ¬ IsBackwardPredecessor qNext deltaNext d qPrev := by
  intro d qPrev hPred
  rcases hPred with ⟨_hDelta, hRec⟩
  rcases hMod with ⟨z, hz⟩
  have hPow : (3 : ℤ) ∣ (2 : ℤ) ^ d := by
    refine ⟨qPrev - 2 * z - 1, ?_⟩
    linarith
  exact finite36_three_not_dvd_twoPow d hPow

/--
actual predecessor と certificate predecessor は一意性により一致する。
-/
private theorem actual_predecessor_eq_certificate
    (C : MonotoneSuffixHenselChain)
    {s prev : BackwardHenselState}
    {i : ℕ}
    (hi : i + 1 < C.width)
    (hDelta :
      C.delta (i + 1) = s.delta)
    (hQ :
      C.q (i + 1) = s.q)
    (hPred :
      IsBackwardPredecessor
        s.q s.delta prev.delta prev.q) :
    C.delta i = prev.delta ∧
      C.q i = prev.q := by
  have hActual :=
    C.actual_isBackwardPredecessor hi
  rw [hDelta, hQ] at hActual
  have hUnique :=
    backwardPredecessor_unique hPred hActual
  exact ⟨hUnique.1.symm, hUnique.2.symm⟩

/--
actual state `i` が certificate の right state と一致しているなら、
一つ左の actual state は certificate predecessor と一致する。
-/
private theorem backward_certificate_step_actual
    (C : MonotoneSuffixHenselChain)
    {s prev : BackwardHenselState}
    {i : ℕ}
    (hi : i < C.width)
    (hiPos : 0 < i)
    (hDelta : C.delta i = s.delta)
    (hQ : C.q i = s.q)
    (hPred :
      IsBackwardPredecessor
        s.q s.delta prev.delta prev.q) :
    C.delta (i - 1) = prev.delta ∧
      C.q (i - 1) = prev.q := by
  let j := i - 1
  have hjStep :
      j + 1 < C.width := by
    dsimp [j]
    omega
  have hActual :=
    C.actual_isBackwardPredecessor hjStep
  have hIdx :
      j + 1 = i := by
    dsimp [j]
    omega
  rw [hIdx, hDelta, hQ] at hActual
  have hUnique :=
    backwardPredecessor_unique hPred hActual
  exact ⟨hUnique.1.symm, hUnique.2.symm⟩

theorem backwardDiesWithin_not_actual
    (C : MonotoneSuffixHenselChain)
    {s : BackwardHenselState}
    {k i : ℕ}
    (hDies : BackwardDiesWithin s k)
    (hi : i < C.width)
    (hk : k < i)
    (hDelta : C.delta i = s.delta)
    (hQ : C.q i = s.q) :
    False := by
  induction hDies generalizing i with
  | dead hdead =>
      have hiPos : 0 < i := by
        omega
      let j := i - 1
      have hjStep :
          j + 1 < C.width := by
        dsimp [j]
        omega
      have hActual :=
        C.actual_isBackwardPredecessor hjStep
      have hIdx :
          j + 1 = i := by
        dsimp [j]
        omega
      rw [hIdx, hDelta, hQ] at hActual
      exact hdead _ _ hActual
  | step hpred hrest ih =>
      have hiPos : 0 < i := by
        omega
      have hPrev :=
        backward_certificate_step_actual
          C hi hiPos hDelta hQ hpred
      apply ih (i := i - 1)
      · omega
      · omega
      · exact hPrev.1
      · exact hPrev.2

/--
actual one-step predecessor を concrete candidate に固定する補助定理。
width 4 の surviving arithmetic chain を読むときにも使う。
-/
theorem previous_state_eq_of_candidate
    (C : MonotoneSuffixHenselChain)
    {i dNext dPrev : ℕ}
    {qNext qPrev : ℤ}
    (hi : i + 1 < C.width)
    (hDeltaNext : C.delta (i + 1) = dNext)
    (hQNext : C.q (i + 1) = qNext)
    (hCandidate :
      IsBackwardPredecessor qNext dNext dPrev qPrev) :
    C.delta i = dPrev ∧ C.q i = qPrev := by
  have hActual := C.actual_isBackwardPredecessor hi
  rw [hDeltaNext, hQNext] at hActual
  have hUnique := backwardPredecessor_unique hCandidate hActual
  exact ⟨hUnique.1.symm, hUnique.2.symm⟩

/-! ## concrete deterministic terminal certificates -/

private theorem terminal_four_dies :
    BackwardDiesWithin ⟨4, 5⟩ 0 := by
  apply BackwardDiesWithin.dead
  exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_six_dies :
    BackwardDiesWithin ⟨6, 21⟩ 1 := by
  apply BackwardDiesWithin.step (prev := ⟨6, 35⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.dead
    exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_eight_dies :
    BackwardDiesWithin ⟨8, 85⟩ 5 := by
  apply BackwardDiesWithin.step (prev := ⟨7, 99⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.step (prev := ⟨6, 87⟩)
    · norm_num [IsBackwardPredecessor]
    · apply BackwardDiesWithin.step (prev := ⟨6, 79⟩)
      · norm_num [IsBackwardPredecessor]
      · apply BackwardDiesWithin.step (prev := ⟨5, 63⟩)
        · norm_num [IsBackwardPredecessor]
        · apply BackwardDiesWithin.step (prev := ⟨4, 47⟩)
          · norm_num [IsBackwardPredecessor]
          · apply BackwardDiesWithin.dead
            exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_ten_dies :
    BackwardDiesWithin ⟨10, 341⟩ 0 := by
  apply BackwardDiesWithin.dead
  exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_twelve_dies :
    BackwardDiesWithin ⟨12, 1365⟩ 7 := by
  apply BackwardDiesWithin.step (prev := ⟨12, 2275⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.step (prev := ⟨11, 2199⟩)
    · norm_num [IsBackwardPredecessor]
    · apply BackwardDiesWithin.step (prev := ⟨10, 1807⟩)
      · norm_num [IsBackwardPredecessor]
      · apply BackwardDiesWithin.step (prev := ⟨9, 1375⟩)
        · norm_num [IsBackwardPredecessor]
        · apply BackwardDiesWithin.step (prev := ⟨9, 1087⟩)
          · norm_num [IsBackwardPredecessor]
          · apply BackwardDiesWithin.step (prev := ⟨9, 895⟩)
            · norm_num [IsBackwardPredecessor]
            · apply BackwardDiesWithin.step (prev := ⟨9, 767⟩)
              · norm_num [IsBackwardPredecessor]
              · apply BackwardDiesWithin.dead
                exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_fourteen_dies :
    BackwardDiesWithin ⟨14, 5461⟩ 1 := by
  apply BackwardDiesWithin.step (prev := ⟨13, 6371⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.dead
    exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_sixteen_dies :
    BackwardDiesWithin ⟨16, 21845⟩ 0 := by
  apply BackwardDiesWithin.dead
  exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_eighteen_dies :
    BackwardDiesWithin ⟨18, 87381⟩ 4 := by
  apply BackwardDiesWithin.step (prev := ⟨18, 145635⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.step (prev := ⟨18, 184471⟩)
    · norm_num [IsBackwardPredecessor]
    · apply BackwardDiesWithin.step (prev := ⟨17, 166671⟩)
      · norm_num [IsBackwardPredecessor]
      · apply BackwardDiesWithin.step (prev := ⟨16, 132959⟩)
        · norm_num [IsBackwardPredecessor]
        · apply BackwardDiesWithin.dead
          exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_twenty_dies :
    BackwardDiesWithin ⟨20, 349525⟩ 2 := by
  apply BackwardDiesWithin.step (prev := ⟨19, 407779⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.step (prev := ⟨19, 446615⟩)
    · norm_num [IsBackwardPredecessor]
    · apply BackwardDiesWithin.dead
      exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_twentyTwo_dies :
    BackwardDiesWithin ⟨22, 1398101⟩ 0 := by
  apply BackwardDiesWithin.dead
  exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_twentyFour_dies :
    BackwardDiesWithin ⟨24, 5592405⟩ 1 := by
  apply BackwardDiesWithin.step (prev := ⟨24, 9320675⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.dead
    exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_twentySix_dies :
    BackwardDiesWithin ⟨26, 22369621⟩ 4 := by
  apply BackwardDiesWithin.step (prev := ⟨25, 26097891⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.step (prev := ⟨24, 22990999⟩)
    · norm_num [IsBackwardPredecessor]
    · apply BackwardDiesWithin.step (prev := ⟨23, 18123535⟩)
      · norm_num [IsBackwardPredecessor]
      · apply BackwardDiesWithin.step (prev := ⟨23, 14878559⟩)
        · norm_num [IsBackwardPredecessor]
        · apply BackwardDiesWithin.dead
          exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_twentyEight_dies :
    BackwardDiesWithin ⟨28, 89478485⟩ 0 := by
  apply BackwardDiesWithin.dead
  exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_thirty_dies :
    BackwardDiesWithin ⟨30, 357913941⟩ 3 := by
  apply BackwardDiesWithin.step (prev := ⟨30, 596523235⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.step (prev := ⟨29, 576639127⟩)
    · norm_num [IsBackwardPredecessor]
    · apply BackwardDiesWithin.step (prev := ⟨29, 563383055⟩)
      · norm_num [IsBackwardPredecessor]
      · apply BackwardDiesWithin.dead
        exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_thirtyTwo_dies :
    BackwardDiesWithin ⟨32, 1431655765⟩ 1 := by
  apply BackwardDiesWithin.step (prev := ⟨31, 1670265059⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.dead
    exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_thirtyFour_dies :
    BackwardDiesWithin ⟨34, 5726623061⟩ 0 := by
  apply BackwardDiesWithin.dead
  exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

private theorem terminal_thirtySix_dies :
    BackwardDiesWithin ⟨36, 22906492245⟩ 2 := by
  apply BackwardDiesWithin.step (prev := ⟨36, 38177487075⟩)
  · norm_num [IsBackwardPredecessor]
  · apply BackwardDiesWithin.step (prev := ⟨36, 48358150295⟩)
    · norm_num [IsBackwardPredecessor]
    · apply BackwardDiesWithin.dead
      exact no_backwardPredecessor_of_three_dvd_q_sub_two (by norm_num)

/-- concrete terminal exponent と certificate から contradiction を得る共通 wrapper。 -/
private theorem false_of_terminal_certificate
    (C : MonotoneSuffixHenselChain)
    {D : ℕ}
    {q : ℤ}
    {k : ℕ}
    (hD : C.delta (C.width - 1) = D)
    (hQ : C.q (C.width - 1) = q)
    (hCert : BackwardDiesWithin ⟨D, q⟩ k)
    (hk : k < C.width - 1) :
    False := by
  apply C.backwardDiesWithin_not_actual
    (s := ⟨D, q⟩)
    (k := k)
    (i := C.width - 1)
    hCert
  · have hw := C.width_pos
    omega
  · exact hk
  · exact hD
  · exact hQ

/--
terminal exponent が even `4..36` に入る MonotoneSuffixHenselChain は存在しない。

finite 部分は 17 個の terminal state のみで、各 state の backward path は
既存 predecessor uniqueness により一本道である。
-/
theorem no_chain_of_terminal_delta_four_to_thirtySix
    (C : MonotoneSuffixHenselChain)
    (hLower : 4 ≤ C.delta (C.width - 1))
    (hUpper : C.delta (C.width - 1) ≤ 36) :
    False := by
  have hEven := C.terminal_delta_mod_two_eq_zero
  have hDLeW := C.terminal_delta_le_width
  have hTerm := C.terminal_recurrence_eq
  have hCases :
      C.delta (C.width - 1) = 4 ∨
      C.delta (C.width - 1) = 6 ∨
      C.delta (C.width - 1) = 8 ∨
      C.delta (C.width - 1) = 10 ∨
      C.delta (C.width - 1) = 12 ∨
      C.delta (C.width - 1) = 14 ∨
      C.delta (C.width - 1) = 16 ∨
      C.delta (C.width - 1) = 18 ∨
      C.delta (C.width - 1) = 20 ∨
      C.delta (C.width - 1) = 22 ∨
      C.delta (C.width - 1) = 24 ∨
      C.delta (C.width - 1) = 26 ∨
      C.delta (C.width - 1) = 28 ∨
      C.delta (C.width - 1) = 30 ∨
      C.delta (C.width - 1) = 32 ∨
      C.delta (C.width - 1) = 34 ∨
      C.delta (C.width - 1) = 36 := by
    omega
  rcases hCases with hD | hD | hD | hD | hD | hD | hD | hD | hD |
      hD | hD | hD | hD | hD | hD | hD | hD
  · have hQ : C.q (C.width - 1) = 5 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_four_dies (by omega)
  · have hQ : C.q (C.width - 1) = 21 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_six_dies (by omega)
  · have hQ : C.q (C.width - 1) = 85 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_eight_dies (by omega)
  · have hQ : C.q (C.width - 1) = 341 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_ten_dies (by omega)
  · have hQ : C.q (C.width - 1) = 1365 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_twelve_dies (by omega)
  · have hQ : C.q (C.width - 1) = 5461 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_fourteen_dies (by omega)
  · have hQ : C.q (C.width - 1) = 21845 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_sixteen_dies (by omega)
  · have hQ : C.q (C.width - 1) = 87381 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_eighteen_dies (by omega)
  · have hQ : C.q (C.width - 1) = 349525 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_twenty_dies (by omega)
  · have hQ : C.q (C.width - 1) = 1398101 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_twentyTwo_dies (by omega)
  · have hQ : C.q (C.width - 1) = 5592405 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_twentyFour_dies (by omega)
  · have hQ : C.q (C.width - 1) = 22369621 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_twentySix_dies (by omega)
  · have hQ : C.q (C.width - 1) = 89478485 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_twentyEight_dies (by omega)
  · have hQ : C.q (C.width - 1) = 357913941 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_thirty_dies (by omega)
  · have hQ : C.q (C.width - 1) = 1431655765 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_thirtyTwo_dies (by omega)
  · have hQ : C.q (C.width - 1) = 5726623061 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_thirtyFour_dies (by omega)
  · have hQ : C.q (C.width - 1) = 22906492245 := by
      rw [hD] at hTerm
      norm_num at hTerm
      omega
    exact C.false_of_terminal_certificate hD hQ terminal_thirtySix_dies (by omega)

end MonotoneSuffixHenselChain

end ExternalArithmetic
end CSTMicro
end Collatz2
