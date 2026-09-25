import CollatzLean.Collatz3.Mersenne.TargetTwoSourceOneArithmetic
import CollatzLean.Collatz3.Mersenne.TwoHoleM5Modular
import CollatzLean.Collatz3.Arithmetic.ThreeOrderModTwoPow
import Std.Data.HashSet.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.nativeDecide false
set_option linter.style.longLine false
set_option exponentiation.threshold 1024
/-!
# Collatz3 Mersenne: target-two `n=1` の finite sieve 内部化

`TargetTwoSourceOneArithmetic` で得た explicit depth bound と、two-hole 側ですでに
使っている M₅ / tail-loop infrastructure を組み合わせ、A2 target `n=1` の
bounded residual を repository 内部で閉じる。

巨大な `k < 2^512` を直接列挙しない。有限計算は次の5段階に分ける。

1. `7 * 73` 上の 12 × 9 × 9 の cheap sieve で 68 状態まで落とす。
2. `7 * 73 * 2593` へ lift し、81 / 648-period で 8410 状態へ絞る。
3. `7 * 19 * 73 * 163 * 2593 = (M₅/729)/487` へ lift し、162-period で 419 状態へ絞る。
4. M₅ の unit quotient 上で 486 / 1944-period へ lift し、1133 状態を得る。
5. 3-adic factor を含む縮小 sieve で最終3状態へ落とす。

この前置 sieve により、最終 classification が評価する membership 判定は
従来の約 478 万回から約 34 万回まで減る。

ここで `J = (k-6) mod p₃` とする。最終 survivor は

* `J = 0, R = 3, L = 7`,
* `J = 0, R = 5, L = 5`,
* `J = 0, R = 8, L = 2`

の3状態だけになる。元 equation の `mod 16` で `r<4` を得るので、実際には
`r=3, L≡7 (mod 486)` だけが残る。hole residue も M₅ 上で `{2,5}` に固定する。

最後は `mod 2^515`。`k<2^512` なら `ord_(2^515)(3)=2^513` の injective window 内に
入る。`L,a,b` の 486-residue から低位515 bit の候補は18通りしかなく、それぞれの
canonical exponent を native certificate で固定すると、全候補が

* `k≥2^512`、または
* `k mod 1944 ≠ 6`

のどちらかになる。従って `k≥7` branch は不可能。

このファイルでは新しい外部数論仮定を導入しない。
-/

namespace Collatz3
namespace Mersenne

@[ext]
private structure SourceOneKRL where
  j : ℕ
  r : ℕ
  L : ℕ
  deriving DecidableEq, Repr

/-! ## 共通 meet-in-the-middle -/

private def pairSumAt (m a b : ℕ) [NeZero m] : ZMod m :=
  (2 : ZMod m) ^ a + (2 : ZMod m) ^ b

private def pairValuesAt (m p : ℕ) [NeZero m] : List ℕ :=
  (List.range p).flatMap fun a =>
    (List.range p).map fun b =>
      (pairSumAt m a b).val

private def pairSetAt (m p : ℕ) [NeZero m] : Std.HashSet ℕ :=
  Std.HashSet.ofList (pairValuesAt m p)

private theorem pairSetAt_contains
    {m p : ℕ} [NeZero m]
    (A B : Fin p) :
    (pairSetAt m p).contains (pairSumAt m A.1 B.1).val = true := by
  have hMem :
      (pairSumAt m A.1 B.1).val ∈ pairValuesAt m p := by
    unfold pairValuesAt
    apply List.mem_flatMap.mpr
    refine ⟨A.1, List.mem_range.mpr A.2, ?_⟩
    apply List.mem_map.mpr
    exact ⟨B.1, List.mem_range.mpr B.2, rfl⟩
  simpa only [
    pairSetAt,
    Std.HashSet.contains_ofList,
    List.contains_eq_mem,
    decide_eq_true_eq
  ] using hMem

/--
`2^p=1` の unit modulus 上で、target-two `n=1` equation の hole pair を
meet-in-the-middle の need residue へ移す。
-/
private def sourceOneNeedAt
    (m p k r L : ℕ) [NeZero m] : ZMod m :=
  (2 : ZMod m) ^ L - 1 -
    (((3 : ZMod m) ^ k - 1) * (2 : ZMod m) ^ (p - r))

private theorem pairSum_eq_sourceOneNeedAt
    {m p k r L a b : ℕ} [NeZero m]
    (hr : r < p)
    (hTwoPeriod : (2 : ZMod m) ^ p = 1)
    (hEq : TargetTwoHoleModEquation m k 1 r L a b) :
    pairSumAt m a b = sourceOneNeedAt m p k r L := by
  let X : ZMod m :=
    (2 : ZMod m) ^ L - 1 - (2 : ZMod m) ^ a - (2 : ZMod m) ^ b
  have hInv :
      (2 : ZMod m) ^ r * (2 : ZMod m) ^ (p - r) = 1 := by
    rw [← pow_add]
    have hsum : r + (p - r) = p := Nat.add_sub_of_le (Nat.le_of_lt hr)
    rw [hsum, hTwoPeriod]
  have hMain :
      (3 : ZMod m) ^ k - 1 = (2 : ZMod m) ^ r * X := by
    unfold TargetTwoHoleModEquation at hEq
    norm_num at hEq
    dsimp [X]
    linear_combination hEq
  have hCancel :
      ((2 : ZMod m) ^ r * X) * (2 : ZMod m) ^ (p - r) = X := by
    calc
      ((2 : ZMod m) ^ r * X) * (2 : ZMod m) ^ (p - r)
          = X * ((2 : ZMod m) ^ r * (2 : ZMod m) ^ (p - r)) := by ring
      _ = X := by rw [hInv]; simp
  unfold pairSumAt sourceOneNeedAt
  rw [hMain, hCancel]
  dsimp [X]
  ring

private theorem shiftedDepthMod12
    {k : ℕ}
    (hk6 : 6 ≤ k) :
    k % 12 = (6 + ((k - 6) % 12)) % 12 := by
  have hk : k = 6 + (k - 6) := by omega
  calc
    k % 12 = (6 + (k - 6)) % 12 := by
      exact congrArg (fun x : ℕ => x % 12) hk
    _ = ((6 % 12) + ((k - 6) % 12)) % 12 := by
      rw [Nat.add_mod]
    _ = (6 + ((k - 6) % 12)) % 12 := by norm_num

private theorem shiftedDepthMod648
    {k : ℕ}
    (hk6 : 6 ≤ k) :
    k % 648 = (6 + ((k - 6) % 648)) % 648 := by
  have hk : k = 6 + (k - 6) := by omega
  calc
    k % 648 = (6 + (k - 6)) % 648 := by
      exact congrArg (fun x : ℕ => x % 648) hk
    _ = ((6 % 648) + ((k - 6) % 648)) % 648 := by
      rw [Nat.add_mod]
    _ = (6 + ((k - 6) % 648)) % 648 := by norm_num

private theorem shiftedDepthMod1944
    {k : ℕ}
    (hk6 : 6 ≤ k) :
    k % 1944 = (6 + ((k - 6) % 1944)) % 1944 := by
  have hk : k = 6 + (k - 6) := by omega
  calc
    k % 1944 = (6 + (k - 6)) % 1944 := by
      exact congrArg (fun x : ℕ => x % 1944) hk
    _ = ((6 % 1944) + ((k - 6) % 1944)) % 1944 := by
      rw [Nat.add_mod]
    _ = (6 + ((k - 6) % 1944)) % 1944 := by norm_num

/-! ## Stage 0: `7*73` -/

/--
最初の cheap sieve。`ord(2)` は 9、`ord(3)` は 12 なので、
648 × 81 × 81 の全面走査へ入る前に 12 × 9 × 9 へ落とす。
-/
private def sourceOneStageZeroModulus : ℕ := 511

private instance sourceOneStageZeroModulus_neZero :
    NeZero sourceOneStageZeroModulus :=
  ⟨by norm_num [sourceOneStageZeroModulus]⟩

private theorem sourceOneStageZeroPeriods :
    Pow23Periods sourceOneStageZeroModulus 9 12 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · -- case refine_1: 512 ≡ 1 [MOD 511]
    decide
  · -- case refine_2: 3^12 ≡ 1 [MOD 511]
    decide

private def sourceOneStageZeroCandidates : List SourceOneKRL :=
  let S := pairSetAt sourceOneStageZeroModulus 9
  (List.range 12).flatMap fun J =>
    (List.range 9).flatMap fun R =>
      ((List.range 9).filter fun T =>
        S.contains
          (sourceOneNeedAt sourceOneStageZeroModulus 9
            ((6 + J) % 12) R T).val).map fun T =>
        ⟨J, R, T⟩

private theorem sourceOneStageZero_mem
    (J : Fin 12) (R T A B : Fin 9)
    (hEq :
      TargetTwoHoleModEquation sourceOneStageZeroModulus
        ((6 + J.1) % 12) 1 R.1 T.1 A.1 B.1) :
    SourceOneKRL.mk J.1 R.1 T.1 ∈ sourceOneStageZeroCandidates := by
  have hPair := pairSum_eq_sourceOneNeedAt
    (m := sourceOneStageZeroModulus) (p := 9)
    R.2 sourceOneStageZeroPeriods.two_period hEq
  have hContains := pairSetAt_contains
    (m := sourceOneStageZeroModulus) (p := 9) A B
  have hNeed :
      (pairSetAt sourceOneStageZeroModulus 9).contains
        (sourceOneNeedAt sourceOneStageZeroModulus 9
          ((6 + J.1) % 12) R.1 T.1).val = true := by
    rw [← hPair]
    exact hContains
  unfold sourceOneStageZeroCandidates
  apply List.mem_flatMap.mpr
  refine ⟨J.1, List.mem_range.mpr J.2, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨R.1, List.mem_range.mpr R.2, ?_⟩
  apply List.mem_map.mpr
  refine ⟨T.1, ?_, rfl⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_range.mpr T.2, by simpa using hNeed⟩

/-! ## Stage 1: `7*73*2593` -/

/--
Stage 0 の 68 survivor だけを 648 × 81 × 81 へ lift する。
`7` を加えても period は `(81,648)` のまま。
-/
private def sourceOneStageOneModulus : ℕ := 1325023

private instance sourceOneStageOneModulus_neZero :
    NeZero sourceOneStageOneModulus :=
  ⟨by norm_num [sourceOneStageOneModulus]⟩

private theorem sourceOneStageOnePeriods :
    Pow23Periods sourceOneStageOneModulus 81 648 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> native_decide

private def sourceOneStageOneCandidates : List SourceOneKRL :=
  let S := pairSetAt sourceOneStageOneModulus 81
  sourceOneStageZeroCandidates.flatMap fun t =>
    (List.range 54).flatMap fun iJ =>
      (List.range 9).flatMap fun iR =>
        ((List.range 9).filter fun iL =>
          let J := t.j + 12 * iJ
          let R := t.r + 9 * iR
          let T := t.L + 9 * iL
          S.contains
            (sourceOneNeedAt sourceOneStageOneModulus 81
              ((6 + J) % 648) R T).val).map fun iL =>
          ⟨t.j + 12 * iJ, t.r + 9 * iR, t.L + 9 * iL⟩

private theorem sourceOneStageOne_mem
    (J : Fin 648) (R T A B : Fin 81)
    (hPrev :
      SourceOneKRL.mk (J.1 % 12) (R.1 % 9) (T.1 % 9) ∈
        sourceOneStageZeroCandidates)
    (hEq :
      TargetTwoHoleModEquation sourceOneStageOneModulus
        ((6 + J.1) % 648) 1 R.1 T.1 A.1 B.1) :
    SourceOneKRL.mk J.1 R.1 T.1 ∈ sourceOneStageOneCandidates := by
  have hPair := pairSum_eq_sourceOneNeedAt
    (m := sourceOneStageOneModulus) (p := 81)
    R.2 sourceOneStageOnePeriods.two_period hEq
  have hContains := pairSetAt_contains
    (m := sourceOneStageOneModulus) (p := 81) A B
  have hNeed :
      (pairSetAt sourceOneStageOneModulus 81).contains
        (sourceOneNeedAt sourceOneStageOneModulus 81
          ((6 + J.1) % 648) R.1 T.1).val = true := by
    rw [← hPair]
    exact hContains
  have hiJ : J.1 / 12 < 54 := by omega
  have hiR : R.1 / 9 < 9 := by omega
  have hiT : T.1 / 9 < 9 := by omega
  have hJrep : J.1 % 12 + 12 * (J.1 / 12) = J.1 :=
    Nat.mod_add_div J.1 12
  have hRrep : R.1 % 9 + 9 * (R.1 / 9) = R.1 :=
    Nat.mod_add_div R.1 9
  have hTrep : T.1 % 9 + 9 * (T.1 / 9) = T.1 :=
    Nat.mod_add_div T.1 9
  unfold sourceOneStageOneCandidates
  apply List.mem_flatMap.mpr
  refine ⟨SourceOneKRL.mk (J.1 % 12) (R.1 % 9) (T.1 % 9), hPrev, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨J.1 / 12, List.mem_range.mpr hiJ, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨R.1 / 9, List.mem_range.mpr hiR, ?_⟩
  apply List.mem_map.mpr
  refine ⟨T.1 / 9, ?_, ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hiT, ?_⟩
    simpa [hJrep, hRrep, hTrep] using hNeed
  · apply SourceOneKRL.ext <;> simp [hJrep, hRrep, hTrep]

/-! ## Stage 2: `7*19*73*163*2593` -/

private def sourceOneStageTwoModulus : ℕ := 4103596231

private instance sourceOneStageTwoModulus_neZero :
    NeZero sourceOneStageTwoModulus :=
  ⟨by norm_num [sourceOneStageTwoModulus]⟩

private theorem sourceOneStageTwoPeriods :
    Pow23Periods sourceOneStageTwoModulus 162 648 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> native_decide

private def sourceOneStageTwoCandidates : List SourceOneKRL :=
  let S := pairSetAt sourceOneStageTwoModulus 162
  sourceOneStageOneCandidates.flatMap fun t =>
    (List.range 2).flatMap fun iR =>
      ((List.range 2).filter fun iL =>
        let R := t.r + 81 * iR
        let T := t.L + 81 * iL
        S.contains
          (sourceOneNeedAt sourceOneStageTwoModulus 162
            ((6 + t.j) % 648) R T).val).map fun iL =>
        ⟨t.j, t.r + 81 * iR, t.L + 81 * iL⟩

private theorem sourceOneStageTwo_mem
    (J : Fin 648) (R T A B : Fin 162)
    (hPrev :
      SourceOneKRL.mk J.1 (R.1 % 81) (T.1 % 81) ∈
        sourceOneStageOneCandidates)
    (hEq :
      TargetTwoHoleModEquation sourceOneStageTwoModulus
        ((6 + J.1) % 648) 1 R.1 T.1 A.1 B.1) :
    SourceOneKRL.mk J.1 R.1 T.1 ∈ sourceOneStageTwoCandidates := by
  have hPair := pairSum_eq_sourceOneNeedAt
    (m := sourceOneStageTwoModulus) (p := 162)
    R.2 sourceOneStageTwoPeriods.two_period hEq
  have hContains := pairSetAt_contains
    (m := sourceOneStageTwoModulus) (p := 162) A B
  have hNeed :
      (pairSetAt sourceOneStageTwoModulus 162).contains
        (sourceOneNeedAt sourceOneStageTwoModulus 162
          ((6 + J.1) % 648) R.1 T.1).val = true := by
    rw [← hPair]
    exact hContains
  have hiR : R.1 / 81 < 2 := by omega
  have hiT : T.1 / 81 < 2 := by omega
  have hRrep : R.1 % 81 + 81 * (R.1 / 81) = R.1 :=
    Nat.mod_add_div R.1 81
  have hTrep : T.1 % 81 + 81 * (T.1 / 81) = T.1 :=
    Nat.mod_add_div T.1 81
  unfold sourceOneStageTwoCandidates
  apply List.mem_flatMap.mpr
  refine ⟨SourceOneKRL.mk J.1 (R.1 % 81) (T.1 % 81), hPrev, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨R.1 / 81, List.mem_range.mpr hiR, ?_⟩
  apply List.mem_map.mpr
  refine ⟨T.1 / 81, ?_, ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hiT, ?_⟩
    simpa [hRrep, hTrep] using hNeed
  · apply SourceOneKRL.ext <;> simp [hRrep, hTrep]

/-! ## Stage 3: M₅ unit quotient -/

private def sourceOneUnitModulus : ℕ := 1998451364497

private instance sourceOneUnitModulus_neZero : NeZero sourceOneUnitModulus :=
  ⟨by norm_num [sourceOneUnitModulus]⟩

private theorem sourceOneUnitPeriods :
    Pow23Periods sourceOneUnitModulus 486 1944 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> native_decide

private def sourceOneStageThreeCandidates : List SourceOneKRL :=
  let S := pairSetAt sourceOneUnitModulus 486
  sourceOneStageTwoCandidates.flatMap fun t =>
    (List.range 3).flatMap fun iJ =>
      (List.range 3).flatMap fun iR =>
        ((List.range 3).filter fun iL =>
          let J := t.j + 648 * iJ
          let R := t.r + 162 * iR
          let T := t.L + 162 * iL
          S.contains
            (sourceOneNeedAt sourceOneUnitModulus 486
              ((6 + J) % 1944) R T).val).map fun iL =>
          ⟨t.j + 648 * iJ, t.r + 162 * iR, t.L + 162 * iL⟩

private theorem sourceOneStageThree_mem
    (J : Fin 1944) (R T A B : Fin 486)
    (hPrev :
      SourceOneKRL.mk (J.1 % 648) (R.1 % 162) (T.1 % 162) ∈
        sourceOneStageTwoCandidates)
    (hEq :
      TargetTwoHoleModEquation sourceOneUnitModulus
        ((6 + J.1) % 1944) 1 R.1 T.1 A.1 B.1) :
    SourceOneKRL.mk J.1 R.1 T.1 ∈ sourceOneStageThreeCandidates := by
  have hPair := pairSum_eq_sourceOneNeedAt
    (m := sourceOneUnitModulus) (p := 486)
    R.2 sourceOneUnitPeriods.two_period hEq
  have hContains := pairSetAt_contains
    (m := sourceOneUnitModulus) (p := 486) A B
  have hNeed :
      (pairSetAt sourceOneUnitModulus 486).contains
        (sourceOneNeedAt sourceOneUnitModulus 486
          ((6 + J.1) % 1944) R.1 T.1).val = true := by
    rw [← hPair]
    exact hContains
  have hiJ : J.1 / 648 < 3 := by omega
  have hiR : R.1 / 162 < 3 := by omega
  have hiT : T.1 / 162 < 3 := by omega
  have hJrep : J.1 % 648 + 648 * (J.1 / 648) = J.1 :=
    Nat.mod_add_div J.1 648
  have hRrep : R.1 % 162 + 162 * (R.1 / 162) = R.1 :=
    Nat.mod_add_div R.1 162
  have hTrep : T.1 % 162 + 162 * (T.1 / 162) = T.1 :=
    Nat.mod_add_div T.1 162
  unfold sourceOneStageThreeCandidates
  apply List.mem_flatMap.mpr
  refine ⟨SourceOneKRL.mk (J.1 % 648) (R.1 % 162) (T.1 % 162), hPrev, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨J.1 / 648, List.mem_range.mpr hiJ, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨R.1 / 162, List.mem_range.mpr hiR, ?_⟩
  apply List.mem_map.mpr
  refine ⟨T.1 / 162, ?_, ?_⟩
  · apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr hiT, ?_⟩
    simpa [hJrep, hRrep, hTrep] using hNeed
  · apply SourceOneKRL.ext <;> simp [hJrep, hRrep, hTrep]

/-! ## Stage 4: M₅ 全体 -/

private theorem sourceOneM5TwoPeriod :
    (2 : ZMod TwoHoleM5.modulus) ^ 486 = 1 := by
  have h := TwoHoleM5.twoLoop.loop_at_tail
  simpa using h

private instance sourceOneM5Modulus_neZero :
    NeZero TwoHoleM5.modulus :=
  ⟨by norm_num [TwoHoleM5.modulus]⟩

private def sourceOneStageFourCandidates : List SourceOneKRL :=
  let S := pairSetAt TwoHoleM5.modulus 486
  sourceOneStageThreeCandidates.filter fun t =>
    S.contains
      (sourceOneNeedAt TwoHoleM5.modulus 486
        (6 + t.j) t.r t.L).val

private theorem sourceOneStageFour_mem
    (J : Fin 1944) (R T A B : Fin 486)
    (hPrev : SourceOneKRL.mk J.1 R.1 T.1 ∈ sourceOneStageThreeCandidates)
    (hEq :
      TargetTwoHoleModEquation TwoHoleM5.modulus
        (6 + J.1) 1 R.1 T.1 A.1 B.1) :
    SourceOneKRL.mk J.1 R.1 T.1 ∈ sourceOneStageFourCandidates := by
  have hPair := pairSum_eq_sourceOneNeedAt
    (m := TwoHoleM5.modulus) (p := 486)
    R.2 sourceOneM5TwoPeriod hEq
  have hContains := pairSetAt_contains
    (m := TwoHoleM5.modulus) (p := 486) A B
  have hNeed :
      (pairSetAt TwoHoleM5.modulus 486).contains
        (sourceOneNeedAt TwoHoleM5.modulus 486
          (6 + J.1) R.1 T.1).val = true := by
    rw [← hPair]
    exact hContains
  unfold sourceOneStageFourCandidates
  apply List.mem_filter.mpr
  exact ⟨hPrev, by simpa using hNeed⟩

/--
Stage 4 用の縮小 modulus。

405081243 = 3^6 * 7 * 163 * 487。
M₅ 全体を使わなくても、Stage 3 survivor はこの modulus だけで
最終3状態まで分離できる。
-/
private def sourceOneStageFourSieveModulus : ℕ := 405081243

private instance sourceOneStageFourSieveModulus_neZero :
    NeZero sourceOneStageFourSieveModulus :=
  ⟨by norm_num [sourceOneStageFourSieveModulus]⟩

private theorem sourceOneStageFourSieveModulus_dvd :
    sourceOneStageFourSieveModulus ∣ TwoHoleM5.modulus := by
  norm_num [
    sourceOneStageFourSieveModulus,
    TwoHoleM5.modulus
  ]

/-- pair sum は divisor modulus への射影と可換。 -/
private theorem pairSumAt_project
    {m n a b : ℕ}
    [NeZero m] [NeZero n]
    (hDvd : m ∣ n) :
    ZMod.castHom hDvd (ZMod m) (pairSumAt n a b) =
      pairSumAt m a b := by
  unfold pairSumAt
  simp only [
    map_add,
    map_pow,
    map_ofNat
  ]

/-- source-one need も divisor modulus への射影と可換。 -/
private theorem sourceOneNeedAt_project
    {m n p k r L : ℕ}
    [NeZero m] [NeZero n]
    (hDvd : m ∣ n) :
    ZMod.castHom hDvd (ZMod m)
        (sourceOneNeedAt n p k r L) =
      sourceOneNeedAt m p k r L := by
  unfold sourceOneNeedAt
  simp only [
    map_sub,
    map_mul,
    map_pow,
    map_one,
    map_ofNat
  ]

private def sourceOneStageFourSieveCandidates :
    List SourceOneKRL :=
  let S := pairSetAt sourceOneStageFourSieveModulus 486
  sourceOneStageThreeCandidates.filter fun t =>
    S.contains
      (sourceOneNeedAt
        sourceOneStageFourSieveModulus 486
        (6 + t.j) t.r t.L).val

private theorem sourceOneStageFour_mem_sieve
    {t : SourceOneKRL}
    (ht : t ∈ sourceOneStageFourCandidates) :
    t ∈ sourceOneStageFourSieveCandidates := by
  unfold sourceOneStageFourCandidates at ht
  rcases List.mem_filter.mp ht with ⟨hPrev, hFull⟩
  have hValues :
      (sourceOneNeedAt TwoHoleM5.modulus 486
        (6 + t.j) t.r t.L).val ∈
        pairValuesAt TwoHoleM5.modulus 486 := by
    simpa only [
      pairSetAt,
      Std.HashSet.contains_ofList,
      List.contains_eq_mem,
      decide_eq_true_eq
    ] using hFull
  rcases List.mem_flatMap.mp hValues with
    ⟨a, haRange, ha⟩
  rcases List.mem_map.mp ha with
    ⟨b, hbRange, hab⟩
  let A : Fin 486 :=
    ⟨a, List.mem_range.mp haRange⟩
  let B : Fin 486 :=
    ⟨b, List.mem_range.mp hbRange⟩
  have hFullEq :
      pairSumAt TwoHoleM5.modulus A.1 B.1 =
        sourceOneNeedAt TwoHoleM5.modulus 486
          (6 + t.j) t.r t.L := by
    apply ZMod.val_injective
    simpa [A, B] using hab
  have hSmallRaw :=
    congrArg
      (ZMod.castHom
        sourceOneStageFourSieveModulus_dvd
        (ZMod sourceOneStageFourSieveModulus))
      hFullEq
  have hSmallEq :
      pairSumAt sourceOneStageFourSieveModulus
          A.1 B.1 =
        sourceOneNeedAt sourceOneStageFourSieveModulus 486
          (6 + t.j) t.r t.L := by
    rw [
      pairSumAt_project
        sourceOneStageFourSieveModulus_dvd,
      sourceOneNeedAt_project
        sourceOneStageFourSieveModulus_dvd
    ] at hSmallRaw
    exact hSmallRaw
  have hContains :=
    pairSetAt_contains
      (m := sourceOneStageFourSieveModulus)
      (p := 486) A B
  have hNeed :
      (pairSetAt sourceOneStageFourSieveModulus 486).contains
        (sourceOneNeedAt sourceOneStageFourSieveModulus 486
          (6 + t.j) t.r t.L).val = true := by
    rw [← hSmallEq]
    exact hContains
  unfold sourceOneStageFourSieveCandidates
  apply List.mem_filter.mpr
  exact ⟨hPrev, by simpa using hNeed⟩

/--
前置 sieve 強化後の最終 classification。

計算上の候補数は

* Stage 0: 68
* Stage 1: 8410
* Stage 2: 419
* Stage 3: 1133
* Stage 4 sieve: 3

で、`decide` がたどる membership 判定は約 34 万回。
-/
private theorem sourceOneStageFourSieve_classification :
    ∀ t ∈ sourceOneStageFourSieveCandidates,
      t.j = 0 ∧
        ((t.r = 3 ∧ t.L = 7) ∨
          (t.r = 5 ∧ t.L = 5) ∨
          (t.r = 8 ∧ t.L = 2)) := by
  native_decide

/--
段階 sieve の最終 certificate。実計算する triple は最後には3個だけ。
-/
private theorem sourceOneStageFour_classification :
    ∀ t ∈ sourceOneStageFourCandidates,
      t.j = 0 ∧
        ((t.r = 3 ∧ t.L = 7) ∨
          (t.r = 5 ∧ t.L = 5) ∨
          (t.r = 8 ∧ t.L = 2)) := by
  intro t ht
  exact
    sourceOneStageFourSieve_classification
      t
      (sourceOneStageFour_mem_sieve ht)

/-- exact `n=1` equation を M₅ の3 survivor へ送る。 -/
theorem TargetTwoHoleEquation.source_one_m5_classification
    {k r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (hEq : TargetTwoHoleEquation k 1 r L a b) :
    (k - 6) % 1944 = 0 ∧
      (((r % 486 = 3) ∧ (L % 486 = 7)) ∨
        ((r % 486 = 5) ∧ (L % 486 = 5)) ∨
        ((r % 486 = 8) ∧ (L % 486 = 2))) := by
  let J0 : Fin 12 :=
    ⟨(k - 6) % 12, Nat.mod_lt _ (by norm_num)⟩
  let R0 : Fin 9 := ⟨r % 9, Nat.mod_lt _ (by norm_num)⟩
  let T0 : Fin 9 := ⟨L % 9, Nat.mod_lt _ (by norm_num)⟩
  let A0 : Fin 9 := ⟨a % 9, Nat.mod_lt _ (by norm_num)⟩
  let B0 : Fin 9 := ⟨b % 9, Nat.mod_lt _ (by norm_num)⟩
  have hMod0 :=
    (hEq.to_mod sourceOneStageZeroModulus).reduce sourceOneStageZeroPeriods
  have hk0 := shiftedDepthMod12 (k := k) (by omega : 6 ≤ k)
  have hEq0 :
      TargetTwoHoleModEquation sourceOneStageZeroModulus
        ((6 + J0.1) % 12) 1 R0.1 T0.1 A0.1 B0.1 := by
    dsimp [J0, R0, T0, A0, B0]
    rw [← hk0]
    simpa using hMod0
  have hMem0 := sourceOneStageZero_mem J0 R0 T0 A0 B0 hEq0
  let J1 : Fin 648 :=
    ⟨(k - 6) % 648, Nat.mod_lt _ (by norm_num)⟩
  let R1 : Fin 81 := ⟨r % 81, Nat.mod_lt _ (by norm_num)⟩
  let T1 : Fin 81 := ⟨L % 81, Nat.mod_lt _ (by norm_num)⟩
  let A1 : Fin 81 := ⟨a % 81, Nat.mod_lt _ (by norm_num)⟩
  let B1 : Fin 81 := ⟨b % 81, Nat.mod_lt _ (by norm_num)⟩
  have hJ10 : J1.1 % 12 = J0.1 := by
    dsimp [J1, J0]
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hR10 : R1.1 % 9 = R0.1 := by
    dsimp [R1, R0]
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hT10 : T1.1 % 9 = T0.1 := by
    dsimp [T1, T0]
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hMod1 :=
    (hEq.to_mod sourceOneStageOneModulus).reduce sourceOneStageOnePeriods
  have hk1 := shiftedDepthMod648 (k := k) (by omega : 6 ≤ k)
  have hEq1 :
      TargetTwoHoleModEquation sourceOneStageOneModulus
        ((6 + J1.1) % 648) 1 R1.1 T1.1 A1.1 B1.1 := by
    dsimp [J1, R1, T1, A1, B1]
    rw [← hk1]
    simpa using hMod1
  have hMem1 :
      SourceOneKRL.mk J1.1 R1.1 T1.1 ∈ sourceOneStageOneCandidates := by
    apply sourceOneStageOne_mem J1 R1 T1 A1 B1
    · simpa [hJ10, hR10, hT10] using hMem0
    · exact hEq1
  let J2 : Fin 648 := J1
  let R2 : Fin 162 := ⟨r % 162, Nat.mod_lt _ (by norm_num)⟩
  let T2 : Fin 162 := ⟨L % 162, Nat.mod_lt _ (by norm_num)⟩
  let A2 : Fin 162 := ⟨a % 162, Nat.mod_lt _ (by norm_num)⟩
  let B2 : Fin 162 := ⟨b % 162, Nat.mod_lt _ (by norm_num)⟩
  have hR21 : R2.1 % 81 = R1.1 := by
    dsimp [R2, R1]
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hT21 : T2.1 % 81 = T1.1 := by
    dsimp [T2, T1]
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hMod2 := (hEq.to_mod sourceOneStageTwoModulus).reduce sourceOneStageTwoPeriods
  have hEq2 :
      TargetTwoHoleModEquation sourceOneStageTwoModulus
        ((6 + J2.1) % 648) 1 R2.1 T2.1 A2.1 B2.1 := by
    dsimp [J2, J1, R2, T2, A2, B2]
    rw [← hk1]
    simpa using hMod2
  have hMem2 : SourceOneKRL.mk J2.1 R2.1 T2.1 ∈ sourceOneStageTwoCandidates := by
    apply sourceOneStageTwo_mem J2 R2 T2 A2 B2
    · simpa [J2, hR21, hT21] using hMem1
    · exact hEq2
  let J3 : Fin 1944 :=
    ⟨(k - 6) % 1944, Nat.mod_lt _ (by norm_num)⟩
  let R3 : Fin 486 := ⟨r % 486, Nat.mod_lt _ (by norm_num)⟩
  let T3 : Fin 486 := ⟨L % 486, Nat.mod_lt _ (by norm_num)⟩
  let A3 : Fin 486 := ⟨a % 486, Nat.mod_lt _ (by norm_num)⟩
  let B3 : Fin 486 := ⟨b % 486, Nat.mod_lt _ (by norm_num)⟩
  have hJ32 : J3.1 % 648 = J2.1 := by
    dsimp [J3, J2, J1]
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hR32 : R3.1 % 162 = R2.1 := by
    dsimp [R3, R2]
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hT32 : T3.1 % 162 = T2.1 := by
    dsimp [T3, T2]
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
  have hMod3 := (hEq.to_mod sourceOneUnitModulus).reduce sourceOneUnitPeriods
  have hk3 := shiftedDepthMod1944 (k := k) (by omega : 6 ≤ k)
  have hEq3 :
      TargetTwoHoleModEquation sourceOneUnitModulus
        ((6 + J3.1) % 1944) 1 R3.1 T3.1 A3.1 B3.1 := by
    dsimp [J3, R3, T3, A3, B3]
    rw [← hk3]
    simpa using hMod3
  have hMem3 : SourceOneKRL.mk J3.1 R3.1 T3.1 ∈ sourceOneStageThreeCandidates := by
    apply sourceOneStageThree_mem J3 R3 T3 A3 B3
    · simpa [hJ32, hR32, hT32] using hMem2
    · exact hEq3
  have hMod4 := (hEq.to_mod TwoHoleM5.modulus).reduce_tailLoop TwoHoleM5.loops
  have hkNot : ¬ k < 6 := by omega
  have hEq4 :
      TargetTwoHoleModEquation TwoHoleM5.modulus
        (6 + J3.1) 1 R3.1 T3.1 A3.1 B3.1 := by
    dsimp [J3, R3, T3, A3, B3]
    simpa [tailLoopExponent, hkNot] using hMod4
  have hMem4 := sourceOneStageFour_mem J3 R3 T3 A3 B3 hMem3 hEq4
  have hClass := sourceOneStageFour_classification
    (SourceOneKRL.mk J3.1 R3.1 T3.1) hMem4
  dsimp [J3, R3, T3] at hClass
  exact hClass

/-! ## survivor から `r=3` と hole residue を回収 -/

private theorem sourceOne_exitDepth_lt_four
    {k r L a b : ℕ}
    (hkmod : k % 1944 = 6)
    (hEq : TargetTwoHoleEquation k 1 r L a b) :
    r < 4 := by
  have hk4 : k % 4 = 2 := by
    have hmod : (k % 1944) % 4 = k % 4 := by
      simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd]
    rw [hkmod] at hmod
    norm_num at hmod
    omega
  by_contra hNot
  have hr4 : 4 ≤ r := by omega
  have hMod := hEq.to_mod 16
  unfold TargetTwoHoleModEquation at hMod
  have hThreePeriod : (3 : ZMod 16) ^ 4 = 1 := by decide
  have hThree : (3 : ZMod 16) ^ k = (3 : ZMod 16) ^ 2 := by
    rw [pow_eq_pow_mod_of_pow_eq_one (3 : ZMod 16) (e := k) hThreePeriod]
    rw [hk4]
  have hRZero : (2 : ZMod 16) ^ r = 0 := by
    simpa using ZMod.natCast_pow_eq_zero_of_le 2 hr4
  rw [hThree, hRZero] at hMod
  norm_num at hMod
  exact (by decide : (9 : ZMod 16) ≠ 1) hMod

/--
`sourceOne_final_hole_pairs` 専用の縮小 modulus。

`355023 = 729 * 487`。
この modulus だけで、`A,B < 486` における
`2^A + 2^B = 36` の解は `(2,5),(5,2)` に一意化される。
-/
private def sourceOneFinalPairSieveModulus : ℕ := 355023

private instance sourceOneFinalPairSieveModulus_neZero :
    NeZero sourceOneFinalPairSieveModulus :=
  ⟨by norm_num [sourceOneFinalPairSieveModulus]⟩

/-- `729*487` は M₅ の divisor。 -/
private theorem sourceOneFinalPairSieveModulus_dvd :
    sourceOneFinalPairSieveModulus ∣ TwoHoleM5.modulus := by
  norm_num [
    sourceOneFinalPairSieveModulus,
    TwoHoleM5.modulus
  ]

/--
縮小 modulus `729*487` 上の最終 pair certificate。

M₅ 全体で 486² 個を評価する代わりに、
固定された pair-sum equation だけを小さい modulus 上で検査する。
-/
private theorem sourceOneFinalPairSieve_classification :
    ∀ A B : Fin 486,
      (2 : ZMod sourceOneFinalPairSieveModulus) ^ A.1 +
          (2 : ZMod sourceOneFinalPairSieveModulus) ^ B.1 =
        (36 : ZMod sourceOneFinalPairSieveModulus) →
      (A.1 = 2 ∧ B.1 = 5) ∨
        (A.1 = 5 ∧ B.1 = 2) := by
  native_decide

private theorem sourceOne_final_hole_pairs :
    ∀ A B : Fin 486,
      TargetTwoHoleModEquation TwoHoleM5.modulus
        6 1 3 7 A.1 B.1 →
      (A.1 = 2 ∧ B.1 = 5) ∨
        (A.1 = 5 ∧ B.1 = 2) := by
  intro A B hEq
  /-
  固定値 k=6, n=1, r=3, L=7 を代入すると

    3^6 = 2^3 (2^7 - 1 - 2^A - 2^B) + 1

  なので

    8 (2^A + 2^B) = 8 * 36

  を得る。
  -/
  have hEq' := hEq
  unfold TargetTwoHoleModEquation at hEq'
  norm_num at hEq'
  have hScaled :
      (8 : ZMod TwoHoleM5.modulus) *
          ((2 : ZMod TwoHoleM5.modulus) ^ A.1 +
            (2 : ZMod TwoHoleM5.modulus) ^ B.1) =
        (8 : ZMod TwoHoleM5.modulus) *
          (36 : ZMod TwoHoleM5.modulus) := by
    linear_combination hEq'
  /- M₅ は奇数なので 8 は unit。 -/
  have hEightUnit :
      IsUnit (8 : ZMod TwoHoleM5.modulus) := by
    exact
      (ZMod.isUnit_iff_coprime 8 TwoHoleM5.modulus).2
        (by norm_num [TwoHoleM5.modulus])
  have hPairM5 :
      (2 : ZMod TwoHoleM5.modulus) ^ A.1 +
          (2 : ZMod TwoHoleM5.modulus) ^ B.1 =
        (36 : ZMod TwoHoleM5.modulus) :=
    hEightUnit.mul_left_cancel hScaled
  /-
  M₅ 上の pair equality を
  355023 = 729 * 487 へ射影する。
  -/
  have hSmallRaw :=
    congrArg
      (ZMod.castHom
        sourceOneFinalPairSieveModulus_dvd
        (ZMod sourceOneFinalPairSieveModulus))
      hPairM5
  have hSmall :
      (2 : ZMod sourceOneFinalPairSieveModulus) ^ A.1 +
          (2 : ZMod sourceOneFinalPairSieveModulus) ^ B.1 =
        (36 : ZMod sourceOneFinalPairSieveModulus) := by
    simpa only [
      map_add,
      map_pow,
      map_ofNat
    ] using hSmallRaw
  exact sourceOneFinalPairSieve_classification A B hSmall

/-- M₅ survivor と mod16 から、T1 の residue data を一意化する。 -/
theorem TargetTwoHoleEquation.source_one_final_residue
    {k r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (hEq : TargetTwoHoleEquation k 1 r L a b) :
    k % 1944 = 6 ∧
      r = 3 ∧
      L % 486 = 7 ∧
      (((a % 486 = 2) ∧ (b % 486 = 5)) ∨
        ((a % 486 = 5) ∧ (b % 486 = 2))) := by
  have hClass := hEq.source_one_m5_classification hk7
  rcases hClass with ⟨hJ, hRLT⟩
  have hkmod : k % 1944 = 6 := by
    have hk : k = 6 + (k - 6) := by omega
    rw [hk, Nat.add_mod, hJ]
  have hrLt := sourceOne_exitDepth_lt_four hkmod hEq
  have hrMod : r % 486 = r := Nat.mod_eq_of_lt (by omega)
  have hr3 : r = 3 := by
    rw [hrMod] at hRLT
    rcases hRLT with h | h | h
    · exact h.1
    · omega
    · omega
  have hL7 : L % 486 = 7 := by
    rw [hr3, Nat.mod_eq_of_lt (by norm_num : 3 < 486)] at hRLT
    rcases hRLT with h | h | h
    · exact h.2
    · omega
    · omega
  let A : Fin 486 := ⟨a % 486, Nat.mod_lt _ (by norm_num)⟩
  let B : Fin 486 := ⟨b % 486, Nat.mod_lt _ (by norm_num)⟩
  have hMod := (hEq.to_mod TwoHoleM5.modulus).reduce_tailLoop TwoHoleM5.loops
  have hkNot : ¬ k < 6 := by omega
  have hJrep : (k - 6) % 1944 = 0 := hJ
  have hFinite :
      TargetTwoHoleModEquation TwoHoleM5.modulus
        6 1 3 7 A.1 B.1 := by
    dsimp [A, B]
    simpa [tailLoopExponent, hkNot, hJrep, hr3, hL7] using hMod
  have hAB := sourceOne_final_hole_pairs A B hFinite
  dsimp [A, B] at hAB
  exact ⟨hkmod, hr3, hL7, hAB⟩

/-! ## `mod 2^515` の18 template -/

private abbrev sourceOneTwoAdicModulus : ℕ := 2 ^ 515

private theorem sourceOne_L_pow_options
    {L : ℕ}
    (hLmod : L % 486 = 7)
    (hLne : L ≠ 7) :
    (2 : ZMod sourceOneTwoAdicModulus) ^ (L + 3) = 0 ∨
      (2 : ZMod sourceOneTwoAdicModulus) ^ (L + 3) =
        (2 : ZMod sourceOneTwoAdicModulus) ^ 496 := by
  have hDecomp := Nat.mod_add_div L 486
  rw [hLmod] at hDecomp
  by_cases hOne : L / 486 = 1
  · right
    have hL : L = 493 := by omega
    rw [hL]
  · left
    have hZero : L / 486 ≠ 0 := by
      intro hz
      have : L = 7 := by omega
      exact hLne this
    have hTwo : 2 ≤ L / 486 := by omega
    have hLarge : 515 ≤ L + 3 := by omega
    change (2 : ZMod (2 ^ 515)) ^ (L + 3) = 0
    exact ZMod.natCast_pow_eq_zero_of_le 2 hLarge

private theorem sourceOne_holeTwo_pow_options
    {a : ℕ}
    (haMod : a % 486 = 2) :
    (2 : ZMod sourceOneTwoAdicModulus) ^ (a + 3) =
        (2 : ZMod sourceOneTwoAdicModulus) ^ 5 ∨
      (2 : ZMod sourceOneTwoAdicModulus) ^ (a + 3) =
        (2 : ZMod sourceOneTwoAdicModulus) ^ 491 ∨
      (2 : ZMod sourceOneTwoAdicModulus) ^ (a + 3) = 0 := by
  have hDecomp := Nat.mod_add_div a 486
  rw [haMod] at hDecomp
  by_cases hZero : a / 486 = 0
  · left
    have ha : a = 2 := by omega
    rw [ha]
  · by_cases hOne : a / 486 = 1
    · right; left
      have ha : a = 488 := by omega
      rw [ha]
    · right; right
      have hTwo : 2 ≤ a / 486 := by omega
      have hLarge : 515 ≤ a + 3 := by omega
      change (2 : ZMod (2 ^ 515)) ^ (a + 3) = 0
      exact ZMod.natCast_pow_eq_zero_of_le 2 hLarge

private theorem sourceOne_holeFive_pow_options
    {b : ℕ}
    (hbMod : b % 486 = 5) :
    (2 : ZMod sourceOneTwoAdicModulus) ^ (b + 3) =
        (2 : ZMod sourceOneTwoAdicModulus) ^ 8 ∨
      (2 : ZMod sourceOneTwoAdicModulus) ^ (b + 3) =
        (2 : ZMod sourceOneTwoAdicModulus) ^ 494 ∨
      (2 : ZMod sourceOneTwoAdicModulus) ^ (b + 3) = 0 := by
  have hDecomp := Nat.mod_add_div b 486
  rw [hbMod] at hDecomp
  by_cases hZero : b / 486 = 0
  · left
    have hb : b = 5 := by omega
    rw [hb]
  · by_cases hOne : b / 486 = 1
    · right; left
      have hb : b = 491 := by omega
      rw [hb]
    · right; right
      have hTwo : 2 ≤ b / 486 := by omega
      have hLarge : 515 ≤ b + 3 := by omega
      change (2 : ZMod (2 ^ 515)) ^ (b + 3) = 0
      exact ZMod.natCast_pow_eq_zero_of_le 2 hLarge

private theorem sourceOne_L_ne_seven
    {k r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (hr3 : r = 3)
    (hLmod : L % 486 = 7)
    (hAB :
      ((a % 486 = 2) ∧ (b % 486 = 5)) ∨
        ((a % 486 = 5) ∧ (b % 486 = 2)))
    (hab : a < b)
    (hbDeep : b + 1 < L)
    (hEq : TargetTwoHoleEquation k 1 r L a b) :
    L ≠ 7 := by
  intro hL
  subst L
  have hb6 : b < 6 := by omega
  have ha486 : a < 486 := by omega
  have hb486 : b < 486 := by omega
  rcases hAB with hAB | hAB
  · have ha : a = 2 := by
      rw [Nat.mod_eq_of_lt ha486] at hAB
      exact hAB.1
    have hb : b = 5 := by
      rw [Nat.mod_eq_of_lt hb486] at hAB
      exact hAB.2
    have hFixed := hEq
    unfold TargetTwoHoleEquation at hFixed
    rw [hr3, ha, hb] at hFixed
    norm_num at hFixed
    have hNat : 3 ^ k = 729 := by exact_mod_cast hFixed
    have hPow : 3 ^ 7 ≤ 3 ^ k :=
      Nat.pow_le_pow_right (by norm_num : 0 < 3) hk7
    rw [hNat] at hPow
    norm_num at hPow
  · rw [Nat.mod_eq_of_lt ha486, Nat.mod_eq_of_lt hb486] at hAB
    omega

/--
18個の low-bit template に対応する canonical exponent。
各値は `0 ≤ K < 2^513` の唯一の `3^K` exponent window に正規化してある。
-/
private def sourceOneTemplateExponent
    (top : Fin 2) (h2 h5 : Fin 3) : ℕ :=
  let values : List ℕ := [
    2594303346877015559690129119776140682650122443191598898354190319202726040514672471481996247188599634437265020788133703162234339468232660735042646330270470,
    13564746933405076420793399108920242465128161785343280942246632903051236032399521576735316729016170575674513710799460789706844852686352779344988482722818630,
    23874661466753775975221152490724109746500937950837691812657442720970301564332668054379596255236752012451533571341397558514668615069961913346128502737824326,
    11049630855115085814815536929272613214192504003246929201130746756544751857929569328997460002710417443214649765555838106286911710486496530007354819841500526,
    4565100026321670095239639420057400587607858585617624707560471212323792963360310741851553829478027546991527716371820563136380665212717322218836142695646382,
    23698029769428433042554193980947957933886566305965361334924807501524975126777706897864327480801542901349118773144079558340673390458692297521091542761866414,
    12094656011680155821453180337851479281234221346599430501777599806144352587860770853483951474895288039861402637969395456476031552230679798352823721812698478,
    17012572191666963288334477488823104851502221416105386819273684331265263756342645493954556259518644537053750492108217475677232667977424121591443304458486958,
    9329886074888532036500982053301969942822197495268336691190897733022917859612947696363581314508353036031277832507504369174017627599505957000831406512538798,
    25044699390947959443525433787201190674417701760882050488363337138007180176884426437029144022120235519499254896063685970800622336429287040613496978027275014,
    1173173347029486240208312643312327080701803164951350912995626399840442039837919580104937641230882612022465720221263661523124370973003035563813966758505030,
    11483087880378185794636066025116194362074579330445761783406436217759507571771066057749217167451464048799485580763200430330948133356612169564953986773510726,
    17674820005312131828072076007384635104568727349342184066382921456288447155580924158961438516292469680530677966416701210631238880676467977169492384907666798,
    649971419093139287053707674384553207846494543454210950676447706797937436588613505091402645770668398281700794341940238831028269324937803749255848924021934,
    19782901162199902234368262235275110554125202263801947578040783995999119600006009661104176297094183752639291851114199234035320994570912779051511248990241966,
    18719845161877201834709719415963501171610444692694685367029774505888047885512125683447929988477340277177430838830258560820358722420651245514961286878864750,
    13097443584438432480148545743150257471740857373941973062389660825739408229570948257194405075811285388343923570078337151371880272089644603121863010686862510,
    5414757467660001228315050307629122563060833453104922934306874227497062332841250459603430130800993887321450910477624044868665231711726438531251112740914350
  ]
  values.getD (top.1 * 9 + h2.1 * 3 + h5.1) 0

private def sourceOneTopTerm (top : Fin 2) : ZMod sourceOneTwoAdicModulus :=
  if top.1 = 0 then 0 else (2 : ZMod sourceOneTwoAdicModulus) ^ 496

private def sourceOneHoleTwoTerm (i : Fin 3) : ZMod sourceOneTwoAdicModulus :=
  if i.1 = 0 then (2 : ZMod sourceOneTwoAdicModulus) ^ 5
  else if i.1 = 1 then (2 : ZMod sourceOneTwoAdicModulus) ^ 491
  else 0

private def sourceOneHoleFiveTerm (i : Fin 3) : ZMod sourceOneTwoAdicModulus :=
  if i.1 = 0 then (2 : ZMod sourceOneTwoAdicModulus) ^ 8
  else if i.1 = 1 then (2 : ZMod sourceOneTwoAdicModulus) ^ 494
  else 0

private def sourceOneTemplate
    (top : Fin 2) (h2 h5 : Fin 3) : ZMod sourceOneTwoAdicModulus :=
  sourceOneTopTerm top - 7 - sourceOneHoleTwoTerm h2 - sourceOneHoleFiveTerm h5

/-- 18 template の modular discrete-log certificate。 -/
private theorem sourceOneTemplateCertificate :
    ∀ top : Fin 2, ∀ h2 h5 : Fin 3,
      let K := sourceOneTemplateExponent top h2 h5
      (3 : ZMod sourceOneTwoAdicModulus) ^ K =
          sourceOneTemplate top h2 h5 ∧
        K < 2 ^ 513 ∧
        (K < 2 ^ 512 → K % 1944 ≠ 6) := by
  native_decide

private theorem sourceOne_template_of_options
    {T H2 H5 : ZMod sourceOneTwoAdicModulus}
    (hT : T = 0 ∨ T = (2 : ZMod sourceOneTwoAdicModulus) ^ 496)
    (hH2 :
      H2 = (2 : ZMod sourceOneTwoAdicModulus) ^ 5 ∨
      H2 = (2 : ZMod sourceOneTwoAdicModulus) ^ 491 ∨ H2 = 0)
    (hH5 :
      H5 = (2 : ZMod sourceOneTwoAdicModulus) ^ 8 ∨
      H5 = (2 : ZMod sourceOneTwoAdicModulus) ^ 494 ∨ H5 = 0) :
    ∃ K : ℕ,
      (3 : ZMod sourceOneTwoAdicModulus) ^ K = T - 7 - H2 - H5 ∧
      K < 2 ^ 513 ∧
      (K < 2 ^ 512 → K % 1944 ≠ 6) := by
  rcases hT with hT | hT <;>
    rcases hH2 with hH2 | hH2 | hH2 <;>
    rcases hH5 with hH5 | hH5 | hH5
  all_goals
    subst T
    subst H2
    subst H5
  · refine ⟨sourceOneTemplateExponent ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨2, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨0, by decide⟩ ⟨2, by decide⟩ ⟨2, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨1, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨1, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨1, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨1, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨1, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨1, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨1, by decide⟩
  · refine ⟨sourceOneTemplateExponent ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨2, by decide⟩, ?_⟩
    simpa [sourceOneTemplate, sourceOneTopTerm, sourceOneHoleTwoTerm,
      sourceOneHoleFiveTerm] using
      sourceOneTemplateCertificate ⟨1, by decide⟩ ⟨2, by decide⟩ ⟨2, by decide⟩

/-! ## T1 最終 closure -/

/-- target-two `n=1` の bounded finite residual は完全に内部排除できる。 -/
theorem TargetTwoHoleEquation.source_one_impossible_internal
    {k r L a b : ℕ}
    (hk7 : 7 ≤ k)
    (hr : 0 < r)
    (ha0 : 0 < a)
    (hab : a < b)
    (hbDeep : b + 1 < L)
    (hEq : TargetTwoHoleEquation k 1 r L a b) :
    False := by
  have hBound := hEq.source_one_internal_depth_bound hk7 hr ha0 hab hbDeep
  rw [targetTwoSourceOneInternalDepthBound_eq] at hBound
  have hResidue := hEq.source_one_final_residue hk7
  rcases hResidue with ⟨hk1944, hr3, hLmod, hAB⟩
  have hLne := sourceOne_L_ne_seven
    hk7 hr3 hLmod hAB hab hbDeep hEq
  have hTop := sourceOne_L_pow_options hLmod hLne
  have hEqMod := hEq.to_mod sourceOneTwoAdicModulus
  have hForm :
      (3 : ZMod sourceOneTwoAdicModulus) ^ k =
        (2 : ZMod sourceOneTwoAdicModulus) ^ (L + 3) - 7 -
          (2 : ZMod sourceOneTwoAdicModulus) ^ (a + 3) -
          (2 : ZMod sourceOneTwoAdicModulus) ^ (b + 3) := by
    unfold TargetTwoHoleModEquation at hEqMod
    rw [hr3] at hEqMod
    norm_num at hEqMod
    rw [pow_add, pow_add, pow_add]
    norm_num
    linear_combination hEqMod
  rcases hAB with hAB | hAB
  · have hHole2 := sourceOne_holeTwo_pow_options hAB.1
    have hHole5 := sourceOne_holeFive_pow_options hAB.2
    rcases sourceOne_template_of_options hTop hHole2 hHole5 with
      ⟨K, hKpow, hKord, hKbad⟩
    have hEqPow :
        (3 : ZMod sourceOneTwoAdicModulus) ^ k =
          (3 : ZMod sourceOneTwoAdicModulus) ^ K := by
      calc
        (3 : ZMod sourceOneTwoAdicModulus) ^ k
            = (2 : ZMod sourceOneTwoAdicModulus) ^ (L + 3) - 7 -
                (2 : ZMod sourceOneTwoAdicModulus) ^ (a + 3) -
                (2 : ZMod sourceOneTwoAdicModulus) ^ (b + 3) := hForm
        _ = (3 : ZMod sourceOneTwoAdicModulus) ^ K := hKpow.symm
    have hOrder :
        orderOf (3 : ZMod sourceOneTwoAdicModulus) = 2 ^ 513 := by
      change orderOf (3 : ZMod (2 ^ 515)) = 2 ^ 513
      exact Arithmetic.orderOf_three_zmod_twoPow 515
        (by norm_num : 3 ≤ 515)
    have hkOrd :
        k < orderOf (3 : ZMod sourceOneTwoAdicModulus) := by
      rw [hOrder]
      omega
    have hKOrd :
        K < orderOf (3 : ZMod sourceOneTwoAdicModulus) := by
      rw [hOrder]
      exact hKord
    have hkEq : k = K :=
      pow_injOn_Iio_orderOf hkOrd hKOrd hEqPow
    subst K
    exact (hKbad hBound) hk1944
  · have hHole2 := sourceOne_holeTwo_pow_options hAB.2
    have hHole5 := sourceOne_holeFive_pow_options hAB.1
    rcases sourceOne_template_of_options hTop hHole2 hHole5 with
      ⟨K, hKpow, hKord, hKbad⟩
    have hEqPow :
        (3 : ZMod sourceOneTwoAdicModulus) ^ k =
          (3 : ZMod sourceOneTwoAdicModulus) ^ K := by
      calc
        (3 : ZMod sourceOneTwoAdicModulus) ^ k
            = (2 : ZMod sourceOneTwoAdicModulus) ^ (L + 3) - 7 -
                (2 : ZMod sourceOneTwoAdicModulus) ^ (a + 3) -
                (2 : ZMod sourceOneTwoAdicModulus) ^ (b + 3) := hForm
        _ = (2 : ZMod sourceOneTwoAdicModulus) ^ (L + 3) - 7 -
              (2 : ZMod sourceOneTwoAdicModulus) ^ (b + 3) -
              (2 : ZMod sourceOneTwoAdicModulus) ^ (a + 3) := by ring
        _ = (3 : ZMod sourceOneTwoAdicModulus) ^ K := hKpow.symm
    have hOrder :
        orderOf (3 : ZMod sourceOneTwoAdicModulus) = 2 ^ 513 := by
      change orderOf (3 : ZMod (2 ^ 515)) = 2 ^ 513
      exact Arithmetic.orderOf_three_zmod_twoPow 515
        (by norm_num : 3 ≤ 515)
    have hkOrd :
        k < orderOf (3 : ZMod sourceOneTwoAdicModulus) := by
      rw [hOrder]
      omega
    have hKOrd :
        K < orderOf (3 : ZMod sourceOneTwoAdicModulus) := by
      rw [hOrder]
      exact hKord
    have hkEq : k = K :=
      pow_injOn_Iio_orderOf hkOrd hKOrd hEqPow
    subst K
    exact (hKbad hBound) hk1944

end Mersenne
end Collatz3
