import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.MonotoneSuffixHenselFinite36
import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.BeattyFactorRepeat
import CollatzLean.Collatz2.CSTMicro.MultiCorner.RestartedSuffixHenselBeattyArithmetic


/-!
# Restarted suffix Hensel chain: widths 4 through 36

actual restarted terminal straight packet の finite-width 部分を閉じる。

* width = 4:
  pure Hensel chain には terminal exponent 2 の surviving chain が一つ残る。
  backward determinism で入口 quotient `q_0 = 1` を強制し、restart が要求する
  extra `3` digit から `3 ∣ q_0` を得て矛盾する。

* 5 ≤ width ≤ 36:
  Beatty arithmetic から terminal exponent `D ≥ 3`。
  terminal parity と合わせて `D ≥ 4`。さらに staircase から `D ≤ width ≤ 36`。
  `MonotoneSuffixHenselFinite36` の deterministic terminal certificate により
  chain 自体が存在できない。

従ってこの範囲では全 Beatty/Sturmian word の列挙は不要である。
-/

namespace Collatz2
namespace CSTMicro
namespace MultiCorner

open ExternalArithmetic

namespace RestartedTerminalStraightPacket

/-! ## Beatty terminal exponent の下界 -/

/-- `n ≥ 4` なら `2^(n+2) < 3^n`。 -/
private theorem finite36_twoPow_add_two_lt_threePow_four_add
    (k : ℕ) :
    2 ^ ((4 + k) + 2) < 3 ^ (4 + k) := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      calc
        2 ^ ((4 + (k + 1)) + 2)
            = 2 ^ ((4 + k) + 2) * 2 := by
                rw [
                  show (4 + (k + 1)) + 2 =
                    ((4 + k) + 2) + 1 by omega,
                  pow_succ
                ]
        _ < 3 ^ (4 + k) * 2 := by
              exact
                (Nat.mul_lt_mul_right
                  (by norm_num : 0 < (2 : ℕ))).2 ih
        _ < 3 ^ (4 + k) * 3 := by
              exact
                (Nat.mul_lt_mul_left
                  (by positivity : 0 < 3 ^ (4 + k))).2
                  (by norm_num : (2 : ℕ) < 3)
        _ = 3 ^ (4 + (k + 1)) := by
              rw [
                show 4 + (k + 1) =
                  (4 + k) + 1 by omega,
                pow_succ
              ]

/-- `n ≥ 4` 版。 -/
private theorem finite36_twoPow_add_two_lt_threePow
    {n : ℕ}
    (hn : 4 ≤ n) :
    2 ^ (n + 2) < 3 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact finite36_twoPow_add_two_lt_threePow_four_add k

/-- `n ≥ 4` なら Beatty index は `n+2` 以上。 -/
private theorem finite36_beattyIndex_add_two_le
    {n : ℕ}
    (hn : 4 ≤ n) :
    n + 2 ≤ beattyIndex n := by
  have hStrict := finite36_twoPow_add_two_lt_threePow hn
  by_contra hnot
  have hBetaLe : beattyIndex n ≤ n + 1 := by omega
  have hUpper := beattyIndex_upper n
  have hPowLe :
      2 ^ (beattyIndex n + 1) ≤ 2 ^ (n + 2) := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) (by omega)
  omega

/--
width ≥ 5 なら actual Beatty staircase の terminal exponent は 4 以上。

`n = width-1` とすると

  delta_n - 1 = beta(b+n) - beta(b) - n,

かつ Beatty additivity の carry は 0/1。
`n ≥ 4` では `beta(n) ≥ n+2` なので結論する。
-/
theorem suffixHenselDelta_terminal_ge_three_of_five_le_width
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hWidth : 5 ≤ S.width) :
    3 ≤ S.suffixHenselDelta (S.width - 1) := by
  let n : ℕ := S.width - 1
  have hnFour : 4 ≤ n := by
    dsimp [n]
    omega
  have hBeta :
      n + 2 ≤ beattyIndex n :=
    finite36_beattyIndex_add_two_le hnFour
  have hBetaZ :
      (n : ℤ) + 2 ≤ (beattyIndex n : ℤ) := by
    exact_mod_cast hBeta
  have hAddLower :
      beattyIndex S.b + beattyIndex n ≤
        beattyIndex (S.b + n) := by
    rcases
        ExternalArithmetic.beattyIndex_add_eq_add_or_add_one
          S.b n with
      hNoCarry | hCarry
    · rw [hNoCarry]
    · rw [hCarry]
      omega
  have hAddLowerZ :
      (beattyIndex S.b : ℤ) +
          (beattyIndex n : ℤ) ≤
        (beattyIndex (S.b + n) : ℤ) := by
    exact_mod_cast hAddLower
  have hDelta :=
    S.suffixHenselDelta_cast_sub_one n
  have hDeltaLowerZ :
      (3 : ℤ) ≤
        (S.suffixHenselDelta n : ℤ) := by
    linarith
  have hDeltaLower :
      3 ≤ S.suffixHenselDelta n := by
    exact_mod_cast hDeltaLowerZ
  simpa [n] using hDeltaLower

/-! ## restart extra digit を q₀ へ輸送 -/

/--
extra `3^(width+1)` divisibility は normalized entrance quotient に
少なくとも一つ余分な `3` を強制する。
-/
private theorem three_dvd_suffixHenselQuotient_zero_of_extra
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hExtra :
      (3 : ℤ) ^ (S.width + 1) ∣
        (singleCornerDefect S.b S.width : ℤ)) :
    (3 : ℤ) ∣ S.suffixHenselQuotient hStart 0 := by
  have hTailExtra :
      (3 : ℤ) ^ (S.width + 1) ∣
        restartedClosedTailZ P S.b P.terminalCriticalStart := by
    rw [S.tail_eq_singleCornerDefect]
    exact hExtra
  have hFactor :=
    S.restartedClosedTailZ_eq_pow_mul_suffixHenselUnit
      (i := 0) (r := S.width) (by omega)
  simp only [Nat.add_zero] at hFactor
  have hEnd := S.terminalCriticalStart_eq_b_add_width
  rw [← hEnd] at hFactor
  rw [hFactor] at hTailExtra
  have hUnitExtra :
      (3 : ℤ) ^ (S.width + 1) ∣
        S.suffixHenselUnit 0 S.width :=
    MonotoneSuffixHenselChain.threePow_dvd_cancel_twoPow hTailExtra
  have hSpec :=
    S.suffixHenselQuotient_spec hStart
      (i := 0) (Nat.zero_le S.width)
  simp only [Nat.sub_zero] at hSpec
  rcases hUnitExtra with ⟨z, hz⟩
  have hEq :
      (3 : ℤ) ^ S.width * S.suffixHenselQuotient hStart 0 =
        (3 : ℤ) ^ S.width * (3 * z) := by
    calc
      (3 : ℤ) ^ S.width * S.suffixHenselQuotient hStart 0 =
          S.suffixHenselUnit 0 S.width := hSpec.symm
      _ = (3 : ℤ) ^ (S.width + 1) * z := hz
      _ = (3 : ℤ) ^ S.width * (3 * z) := by
        rw [pow_succ]
        ring
  have hPowNe : (3 : ℤ) ^ S.width ≠ 0 := by
    positivity
  have hZero :
      (3 : ℤ) ^ S.width *
          (S.suffixHenselQuotient hStart 0 - 3 * z) = 0 := by
    calc
      (3 : ℤ) ^ S.width *
          (S.suffixHenselQuotient hStart 0 - 3 * z) =
        (3 : ℤ) ^ S.width * S.suffixHenselQuotient hStart 0 -
          (3 : ℤ) ^ S.width * (3 * z) := by ring
      _ = 0 := by rw [hEq]; ring
  have hDiff :
      S.suffixHenselQuotient hStart 0 - 3 * z = 0 := by
    rcases mul_eq_zero.mp hZero with hPowZero | hDiffZero
    · exact (hPowNe hPowZero).elim
    · exact hDiffZero
  have hQEq :
      S.suffixHenselQuotient hStart 0 = 3 * z :=
    sub_eq_zero.mp hDiff
  exact ⟨z, hQEq⟩

/-! ## width = 4 -/

/--
width 4 の terminal exponent 2 branch は backward determinism により

  (delta_3,q_3) = (2,1),
  (delta_2,q_2) = (1,1),
  (delta_1,q_1) = (1,1),
  (delta_0,q_0) = (1,1)

に固定される。extra digit は `3 ∣ q_0` を要求するため矛盾する。
terminal exponent 4 branch は pure finite certificate で即座に死ぬ。
-/
private theorem false_of_width_eq_four_and_extra
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hWidth : S.width = 4)
    (hExtra :
      (3 : ℤ) ^ (S.width + 1) ∣
        (singleCornerDefect S.b S.width : ℤ)) :
    False := by
  let C := S.toMonotoneSuffixHenselChain hStart
  have hCW : C.width = 4 := by
    simpa [C, toMonotoneSuffixHenselChain] using hWidth
  have hTermPos : 0 < C.delta (C.width - 1) := by
    apply C.delta_pos
    have hw := C.width_pos
    omega
  have hTermEven := C.terminal_delta_mod_two_eq_zero
  have hTermLe := C.terminal_delta_le_width
  have hCases :
      C.delta (C.width - 1) = 2 ∨
        C.delta (C.width - 1) = 4 := by
    omega
  rcases hCases with hD2 | hD4
  · have hD3 : C.delta 3 = 2 := by
      simpa [hCW] using hD2
    have h3lt : 3 < C.width := by omega
    have hRec3 := C.recurrence 3 h3lt
    have hQ4 : C.q 4 = 0 := by
      simpa [hCW] using C.q_terminal
    rw [hD3, hQ4] at hRec3
    norm_num at hRec3
    have hQ3 : C.q 3 = 1 := by omega
    have h2 :=
      C.previous_state_eq_of_candidate
        (i := 2)
        (dNext := 2)
        (dPrev := 1)
        (qNext := 1)
        (qPrev := 1)
        h3lt
        hD3
        hQ3
        (by norm_num [MonotoneSuffixHenselChain.IsBackwardPredecessor])
    have h2lt : 2 < C.width := by omega
    have h1 :=
      C.previous_state_eq_of_candidate
        (i := 1)
        h2lt
        h2.1
        h2.2
        (dNext := 1)
        (dPrev := 1)
        (qNext := 1)
        (qPrev := 1)
        (by norm_num [MonotoneSuffixHenselChain.IsBackwardPredecessor])
    have h1lt : 1 < C.width := by omega
    have h0 :=
      C.previous_state_eq_of_candidate
        (i := 0)
        h1lt
        h1.1
        h1.2
        (dNext := 1)
        (dPrev := 1)
        (qNext := 1)
        (qPrev := 1)
        (by norm_num [MonotoneSuffixHenselChain.IsBackwardPredecessor])
    have hThreeDiv :=
      S.three_dvd_suffixHenselQuotient_zero_of_extra hStart hExtra
    have hThreeDivC : (3 : ℤ) ∣ C.q 0 := by
      simpa [C, toMonotoneSuffixHenselChain] using hThreeDiv
    rw [h0.2] at hThreeDivC
    norm_num at hThreeDivC
  · exact
      C.no_chain_of_terminal_delta_four_to_thirtySix
        (by omega)
        (by omega)

/-! ## widths 4..36 の closure -/

/--
actual restarted packet の width `4..36` に対する finite arithmetic closure。

既存 open axiom と同じ negated extra-divisibility 形式だが、上端 `36` の範囲では theorem。
-/
theorem restartedSingleCorner_noExtraThreeAdic_four_to_thirtySix
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hLower : 4 ≤ S.width)
    (hUpper : S.width ≤ 36) :
    ¬ (3 : ℤ) ^ (S.width + 1) ∣
      (singleCornerDefect S.b S.width : ℤ) := by
  intro hExtra
  by_cases hFour : S.width = 4
  · exact S.false_of_width_eq_four_and_extra hStart hFour hExtra
  · have hFive : 5 ≤ S.width := by omega
    let C := S.toMonotoneSuffixHenselChain hStart
    have hDeltaLowerS :
        3 ≤ S.suffixHenselDelta (S.width - 1) :=
      S.suffixHenselDelta_terminal_ge_three_of_five_le_width hFive
    have hDeltaThreeC :
        3 ≤ C.delta (C.width - 1) := by
      simpa [C, toMonotoneSuffixHenselChain] using hDeltaLowerS
    have hDeltaEvenC := C.terminal_delta_mod_two_eq_zero
    have hDeltaLowerC :
        4 ≤ C.delta (C.width - 1) := by
      omega
    have hDeltaUpperC :
        C.delta (C.width - 1) ≤ 36 := by
      have hLeW := C.terminal_delta_le_width
      have hCW : C.width = S.width := by
        rfl
      omega
    exact
      C.no_chain_of_terminal_delta_four_to_thirtySix
        hDeltaLowerC hDeltaUpperC

/--
geometry が与える extra digit と直前 theorem を合わせると、
width `4..36` の actual restarted packet 自体が存在できない。
-/
theorem false_of_width_four_to_thirtySix
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hLower : 4 ≤ S.width)
    (hUpper : S.width ≤ 36) :
    False := by
  have hNo :=
    S.restartedSingleCorner_noExtraThreeAdic_four_to_thirtySix
      hStart hLower hUpper
  have hExtraTail := S.tail_extra_threeAdic_dvd hStart
  have hExtraDefect :
      (3 : ℤ) ^ (S.width + 1) ∣
        (singleCornerDefect S.b S.width : ℤ) := by
    rw [← S.tail_eq_singleCornerDefect]
    exact hExtraTail
  exact hNo hExtraDefect


/-! ## widths 1..3 の extra-digit closure -/

/--
width `1..3` では pure Hensel chain が残る場合もあるが、
restart extra digit は入口 quotient に `3 ∣ q₀` を強制する。
backward determinism で各 surviving chain の `q₀ = 1` を読み、矛盾させる。
-/
private theorem false_of_width_le_three_and_extra
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hWidth : S.width ≤ 3)
    (hExtra :
      (3 : ℤ) ^ (S.width + 1) ∣
        (singleCornerDefect S.b S.width : ℤ)) :
    False := by
  let C := S.toMonotoneSuffixHenselChain hStart
  have hCW : C.width = S.width := by
    rfl
  have hThreeDiv :=
    S.three_dvd_suffixHenselQuotient_zero_of_extra hStart hExtra
  have hThreeDivC : (3 : ℤ) ∣ C.q 0 := by
    simpa [C, toMonotoneSuffixHenselChain] using hThreeDiv
  have hCases :
      S.width = 1 ∨ S.width = 2 ∨ S.width = 3 := by
    have hPos := S.width_pos
    omega
  rcases hCases with hW1 | hW23
  · have hC1 : C.width = 1 := by
      omega
    have hRec0 := C.recurrence 0 (by omega)
    have hQ1 : C.q 1 = 0 := by
      simpa [hC1] using C.q_terminal
    rw [C.delta_zero, hQ1] at hRec0
    norm_num at hRec0
    omega
  · rcases hW23 with hW2 | hW3
    · have hC2 : C.width = 2 := by
        omega
      have hPos1 : 0 < C.delta 1 := by
        exact C.delta_pos (by omega)
      have hEven1 : C.delta 1 % 2 = 0 := by
        simpa [hC2] using C.terminal_delta_mod_two_eq_zero
      have hLe1 : C.delta 1 ≤ 2 := by
        have h := C.terminal_delta_le_width
        simpa [hC2] using h
      have hD1 : C.delta 1 = 2 := by
        omega
      have hRec1 := C.recurrence 1 (by omega)
      have hQ2 : C.q 2 = 0 := by
        simpa [hC2] using C.q_terminal
      rw [hD1, hQ2] at hRec1
      norm_num at hRec1
      have hQ1 : C.q 1 = 1 := by
        omega
      have hRec0 := C.recurrence 0 (by omega)
      rw [C.delta_zero, hQ1] at hRec0
      norm_num at hRec0
      have hQ0 : C.q 0 = 1 := by
        omega
      rw [hQ0] at hThreeDivC
      norm_num at hThreeDivC
    · have hC3 : C.width = 3 := by
        omega
      have hPos2 : 0 < C.delta 2 := by
        exact C.delta_pos (by omega)
      have hEven2 : C.delta 2 % 2 = 0 := by
        simpa [hC3] using C.terminal_delta_mod_two_eq_zero
      have hLe2 : C.delta 2 ≤ 3 := by
        have h := C.terminal_delta_le_width
        simpa [hC3] using h
      have hD2 : C.delta 2 = 2 := by
        omega
      have hRec2 := C.recurrence 2 (by omega)
      have hQ3 : C.q 3 = 0 := by
        simpa [hC3] using C.q_terminal
      rw [hD2, hQ3] at hRec2
      norm_num at hRec2
      have hQ2 : C.q 2 = 1 := by
        omega
      have h1 :=
        C.previous_state_eq_of_candidate
          (i := 1)
          (dNext := 2)
          (dPrev := 1)
          (qNext := 1)
          (qPrev := 1)
          (by omega)
          hD2
          hQ2
          (by
            norm_num [MonotoneSuffixHenselChain.IsBackwardPredecessor])
      have h0 :=
        C.previous_state_eq_of_candidate
          (i := 0)
          (dNext := 1)
          (dPrev := 1)
          (qNext := 1)
          (qPrev := 1)
          (by omega)
          h1.1
          h1.2
          (by
            norm_num [MonotoneSuffixHenselChain.IsBackwardPredecessor])
      rw [h0.2] at hThreeDivC
      norm_num at hThreeDivC

/--
actual restarted packet の全 finite range `width ≤ 36` を一括で閉じる。
width positive は packet 自身が持つので、`1..3` と `4..36` の二分だけでよい。
-/
theorem restartedSingleCorner_noExtraThreeAdic_le_thirtySix
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hUpper : S.width ≤ 36) :
    ¬ (3 : ℤ) ^ (S.width + 1) ∣
      (singleCornerDefect S.b S.width : ℤ) := by
  intro hExtra
  by_cases hSmall : S.width ≤ 3
  · exact S.false_of_width_le_three_and_extra hStart hSmall hExtra
  · have hLower : 4 ≤ S.width := by
      omega
    exact
      (S.restartedSingleCorner_noExtraThreeAdic_four_to_thirtySix
        hStart hLower hUpper) hExtra

/--
geometry が与える extra digit と finite arithmetic closure を合わせると、
actual restarted packet は `width ≤ 36` を取れない。
-/
theorem false_of_width_le_thirtySix
    {P : PureBProfileObstruction}
    {N : LastTwoExposedNormalForm P}
    (S : RestartedTerminalStraightPacket P N)
    (hStart : 0 < P.criticalizationStart)
    (hUpper : S.width ≤ 36) :
    False := by
  have hNo :=
    S.restartedSingleCorner_noExtraThreeAdic_le_thirtySix
      hStart hUpper
  have hExtraTail := S.tail_extra_threeAdic_dvd hStart
  have hExtraDefect :
      (3 : ℤ) ^ (S.width + 1) ∣
        (singleCornerDefect S.b S.width : ℤ) := by
    rw [← S.tail_eq_singleCornerDefect]
    exact hExtraTail
  exact hNo hExtraDefect

end RestartedTerminalStraightPacket

end MultiCorner
end CSTMicro
end Collatz2
