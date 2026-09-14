import CollatzLean.Collatz3.Bridge.SurvivorCompletionConsequences
import CollatzLean.Collatz3.Bridge.InfiniteSurvivorEscape

/-!
# Collatz3 Bridge: future-minimum anchor 上の completion cocycle

actual infinite coefficient survivor は `+∞` へ発散するため、任意に遠く

* actual future minimum、
* value `> 1`、
* exponent `= 1`

を同時に満たす anchor が存在する。

このファイルでは、その既存 theorem と completion lift/cocycle を結合する。
新しい orbit notion は導入しない。

重要な点は、任意に遠い anchor で

`q_n = 2 t_(n+1) - t_n`

となり、

`2^E_n | 3^(n+1) q_n + 1`

だが `2^(E_n+1)` は割り切らない、という exact finite-branch 状態が現れること。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
任意に遠い future-minimum `e_n=1` anchor では defect / extra depth は
据え置きか `+1` のどちらか。
-/
theorem exists_futureMinimum_completionDepthStep_after
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (start : ℕ) :
    ∃ n : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n ∧
      O.exponent n = 1 ∧
      (O.endpointCompletionExtraDepth (n + 1) = O.endpointCompletionExtraDepth n ∨
        O.endpointCompletionExtraDepth (n + 1) = O.endpointCompletionExtraDepth n + 1) ∧
      (infiniteSurvivorDefect O.exponent (n + 1) =
          infiniteSurvivorDefect O.exponent n ∨
        infiniteSurvivorDefect O.exponent (n + 1) =
          infiniteSurvivorDefect O.exponent n + 1) := by
  rcases
      O.exists_futureMinimum_exponent_eq_one_after_of_infiniteCoefficientSurvivor
        SInf start with
    ⟨n, hStart, hMin, hOne, he⟩
  refine ⟨n, hStart, hMin, hOne, he, ?_, ?_⟩
  · exact
      O.endpointCompletionExtraDepth_succ_eq_self_or_succ_of_exponent_eq_one
        SInf he
  · exact
      O.infiniteSurvivorDefect_succ_eq_self_or_succ_of_exponent_eq_one
        SInf he

/--
任意に遠い future-minimum `e_n=1` anchor で、幅 `n` と `n+1` の
自然数 completion lift を同時に取れる。

future minimum を actual start `x` より先まで送ることで
`x < 2^D_n` を自動的に満たす。
-/
theorem exists_futureMinimum_consecutiveCompletionNatLifts_after
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (start : ℕ) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ t u : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n ∧
      O.exponent n = 1 ∧
      O.endpointCompletionStart SInf hn =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent n * t ∧
      0 < t ∧
      t % 2 = 1 ∧
      t < 2 ^ (O.endpointCompletionExtraDepth n + 1) ∧
      2 ^ O.endpointCompletionExtraDepth n *
          O.endpointCompletionEnd SInf (by omega : 0 < n) =
        O.value n + 3 ^ n * t ∧
      O.endpointCompletionStart SInf (by omega : 0 < n + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (n + 1) * u ∧
      0 < u ∧
      u % 2 = 1 ∧
      u < 2 ^ (O.endpointCompletionExtraDepth (n + 1) + 1) ∧
      2 ^ O.endpointCompletionExtraDepth (n + 1) *
          O.endpointCompletionEnd SInf (by omega : 0 < n + 1) =
        O.value (n + 1) + 3 ^ (n + 1) * u := by
  let base := max start (O.value 0)
  rcases
      O.exists_futureMinimum_exponent_eq_one_after_of_infiniteCoefficientSurvivor
        SInf base with
    ⟨n, hBase, hMin, hOne, he⟩
  have hStart : start < n := by
    exact lt_of_le_of_lt (Nat.le_max_left _ _) hBase
  have hxN : O.value 0 + 1 ≤ n := by
    have hxBase : O.value 0 ≤ base := Nat.le_max_right _ _
    omega
  have hxN1 : O.value 0 + 1 ≤ n + 1 := by omega
  rcases O.exists_endpointCompletionNatLift_of_start_succ_le SInf hxN with
    ⟨t, hStartT, htPos, htOdd, htBound, hEndT⟩
  rcases O.exists_endpointCompletionNatLift_of_start_succ_le SInf hxN1 with
    ⟨u, hStartU, huPos, huOdd, huBound, hEndU⟩
  exact
    ⟨n, by omega, t, u,
      hStart, hMin, hOne, he,
      hStartT, htPos, htOdd, htBound, hEndT,
      hStartU, huPos, huOdd, huBound, hEndU⟩

/--
任意に遠い future-minimum anchor で exact completion cocycle が成立する。

この theorem は、自然数 lift の存在・奇数性・上界と、signed step `q_n` の

* `q_n = 2u-t`,
* `q_n ≠ 0`,
* `-2^(E_n+1) < q_n < 2^(E_n+3)`,
* `2^E_n` は `3^(n+1)q_n+1` を割り切る、
* `2^(E_n+1)` は割り切らない

を一つの有限 packet として与える。
-/
theorem exists_futureMinimum_exactCompletionCocycle_after
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (start : ℕ) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ t u : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n ∧
      O.exponent n = 1 ∧
      O.endpointCompletionStart SInf hn =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent n * t ∧
      O.endpointCompletionStart SInf (by omega : 0 < n + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (n + 1) * u ∧
      0 < t ∧ t % 2 = 1 ∧
      0 < u ∧ u % 2 = 1 ∧
      endpointCompletionLiftStep O n t u = 2 * (u : ℤ) - (t : ℤ) ∧
      endpointCompletionLiftStep O n t u ≠ 0 ∧
      -((2 : ℤ) ^ (O.endpointCompletionExtraDepth n + 1)) <
          endpointCompletionLiftStep O n t u ∧
      endpointCompletionLiftStep O n t u <
          (2 : ℤ) ^ (O.endpointCompletionExtraDepth n + 3) ∧
      ((2 : ℤ) ^ O.endpointCompletionExtraDepth n ∣
        (3 : ℤ) ^ (n + 1) * endpointCompletionLiftStep O n t u + 1) ∧
      ¬ ((2 : ℤ) ^ (O.endpointCompletionExtraDepth n + 1) ∣
        (3 : ℤ) ^ (n + 1) * endpointCompletionLiftStep O n t u + 1) := by
  rcases O.exists_futureMinimum_consecutiveCompletionNatLifts_after SInf start with
    ⟨n, hn, t, u,
      hStart, hMin, hOne, he,
      hStartT, htPos, htOdd, htBound, hEndT,
      hStartU, huPos, huOdd, huBound, hEndU⟩
  have hStepEq :=
    O.endpointCompletionLiftStep_eq_two_mul_sub_of_exponent_eq_one
      (t := t) (u := u) he
  have htOddProp : Odd t := odd_of_mod_two_eq_one htOdd
  have hStepNe :=
    O.endpointCompletionLiftStep_ne_zero
      (m := n) (t := t) (u := u)
      (SInf.exponent_pos n) htOddProp
  have hBounds :=
    O.endpointCompletionLiftStep_bounds_of_exponent_eq_one
      SInf he htBound huBound
  have hExact :=
    O.endpointCompletion_endpoint_cocycle_exact_twoDepth
      SInf hn hStartT hStartU
  exact
    ⟨n, hn, t, u,
      hStart, hMin, hOne, he,
      hStartT, hStartU,
      htPos, htOdd, huPos, huOdd,
      hStepEq, hStepNe,
      hBounds.1, hBounds.2,
      hExact.1, hExact.2⟩


/--
任意に遠い future-minimum anchor で、cocycle の深さを defect だけで書いた形。

`E_n = δ_n+1` を代入すると

* `-2^(δ_n+2) < q_n < 2^(δ_n+4)`,
* `2^(δ_n+1)` は `3^(n+1)q_n+1` を割る、
* `2^(δ_n+2)` は割らない。

A 型のように `δ_n` が大きい場合でも integer lift step は定数倍幅にしか存在しない、
という finite-branch 形を直接使うための wrapper。
-/
theorem exists_futureMinimum_exactCompletionCocycle_defect_after
    (O : Collatz3.OddOrbit)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    (start : ℕ) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ t u : ℕ,
      start < n ∧
      O.FutureMinimumAt n ∧
      1 < O.value n ∧
      O.exponent n = 1 ∧
      O.endpointCompletionStart SInf hn =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent n * t ∧
      O.endpointCompletionStart SInf (by omega : 0 < n + 1) =
        O.value 0 + 2 ^ infinitePrefixDepth O.exponent (n + 1) * u ∧
      -((2 : ℤ) ^ (infiniteSurvivorDefect O.exponent n + 2)) <
          endpointCompletionLiftStep O n t u ∧
      endpointCompletionLiftStep O n t u <
          (2 : ℤ) ^ (infiniteSurvivorDefect O.exponent n + 4) ∧
      ((2 : ℤ) ^ (infiniteSurvivorDefect O.exponent n + 1) ∣
        (3 : ℤ) ^ (n + 1) * endpointCompletionLiftStep O n t u + 1) ∧
      ¬ ((2 : ℤ) ^ (infiniteSurvivorDefect O.exponent n + 2) ∣
        (3 : ℤ) ^ (n + 1) * endpointCompletionLiftStep O n t u + 1) := by
  rcases O.exists_futureMinimum_consecutiveCompletionNatLifts_after SInf start with
    ⟨n, hn, t, u,
      hStart, hMin, hOne, he,
      hStartT, htPos, htOdd, htBound, hEndT,
      hStartU, huPos, huOdd, huBound, hEndU⟩
  have hBounds :=
    O.endpointCompletionLiftStep_bounds_defect_of_exponent_eq_one
      SInf he htBound huBound
  have hExact :=
    O.endpointCompletion_endpoint_cocycle_exact_defectDepth
      SInf hn hStartT hStartU
  exact
    ⟨n, hn, t, u,
      hStart, hMin, hOne, he,
      hStartT, hStartU,
      hBounds.1, hBounds.2,
      hExact.1, hExact.2⟩

end OddOrbit
end Collatz3
