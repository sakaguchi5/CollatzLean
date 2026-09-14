import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumMinLength
import CollatzLean.Collatz3.Bridge.CoefficientFirstPassage
import CollatzLean.Collatz3.CSTMicro.RoofEnvelope
import Mathlib.Tactic.IntervalCases
set_option linter.style.nativeDecide false
/-!
# Collatz3 Bridge: contracting next future minimum block の sharp 最小長 22

前段 `SurvivorAdjacentFutureMinimumMinLength` では、contracting next-future-minimum block
`i → j` の内部にある最短 contracting odd-prefix `p` を用いて

* `3 * d < p`（`d = value(i+p) - value(i)`）、
* future-minimum gap `Δ = value(j) - value(i)` は `4` 以上、
* `p ≤ r = j-i`

から `13 ≤ r` を得た。

このファイルでは、同じ最短 prefix に対して既存の Beatty-roof affine envelope

`roofAffineBound(p) = Σ 2^(beattyIndex k) * 3^(p-k-1)`

を使い、coarse bound `B ≤ p * 3^(p-1)` を sharpen する。

中心となる必要条件は

`7 * 2^(criticalTwoDepth p) ≤ roofAffineBound(p) + 3 * 3^p`。

一方、`p < 22` では右辺が左辺より strict に小さいことを有限整数算術で確認できる。
従って最短 contracting prefix は `22 ≤ p`、whole block も `22 ≤ r`。

また、前段に隠れていた whole-block の量的制約

`3 * (value j - value i) < j-i`

と、future-minimum gap が正の `4` 倍であることを合わせた

`Δ = 4q`, `0 < q`, `12q < r`

も公開 theorem として切り出す。

旧 first-crossing packet や新しい primitive data は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
長さ `p` の segment の先頭 `k ≤ p` 個は、長さ `k` の segment そのもの。

前段の private 補題と同じ derived fact を、この独立ファイル内でも局所的に使う。
-/
private theorem sharp_segmentWord_take_eq_of_le
    (O : Collatz3.OddOrbit)
    (i p k : ℕ)
    (hk : k ≤ p) :
    (O.segmentWord i p).take k = O.segmentWord i k := by
  induction k generalizing i p with
  | zero =>
      simp
  | succ k ih =>
      cases p with
      | zero =>
          omega
      | succ p =>
          simp only [segmentWord_succ, List.take_succ_cons]
          rw [ih (i := i + 1) (p := p) (by omega)]

/--
contracting next-future-minimum block では、whole block の actual 値差 `Δ` 自体が

`3 * Δ < r`

を満たす。

前段の最短 contracting prefix `p` について `3*d < p` があり、
next future minimum はその prefix endpoint 以下、かつ `p ≤ r` なので従う。
-/
theorem three_mul_nextFutureMinimum_valueGap_lt_length_of_contracting
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hContract :
      3 ^ (j - i) <
        2 ^ Word.twoSteps (O.segmentWord i (j - i))) :
    3 * (O.value j - O.value i) < j - i := by
  rcases O.exists_firstContractingOddPrefix
      (i := i) (r := j - i) hContract with
    ⟨p, hpPos, hpLe, hpContract, hpPrefix⟩
  have hPrefixGap :
      3 * (O.value (i + p) - O.value i) < p :=
    O.three_mul_firstContractingOddPrefixReturnGap_lt_length
      hMin hpPos hpContract hpPrefix
  have hNextLe : O.value j ≤ O.value (i + p) :=
    hNext.2 (i + p) (by omega)
  have hGapLe :
      O.value j - O.value i ≤
        O.value (i + p) - O.value i := by
    omega
  omega

/--
contracting next-future-minimum block の値差は

`Δ = 4q`, `0 < q`, `12q < r`

と書ける。

`4` 倍性は両 future minimum の exponent が `1` であることから来て、
`12q < r` は前定理 `3Δ < r` の言い換えである。
-/
theorem exists_nextFutureMinimum_valueGap_eq_four_mul_and_twelve_mul_lt_of_contracting
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hContract :
      3 ^ (j - i) <
        2 ^ Word.twoSteps (O.segmentWord i (j - i))) :
    ∃ q : ℕ,
      0 < q ∧
        O.value j - O.value i = 4 * q ∧
        12 * q < j - i := by
  have hFour : 4 ≤ O.value j - O.value i :=
    O.four_le_nextFutureMinimum_valueGap S hMin hNext
  have hLt : O.value i < O.value j := by
    omega
  have hei : O.exponent i = 1 :=
    O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor S hMin
  have hej : O.exponent j = 1 :=
    O.nextFutureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor S hNext
  obtain ⟨q, hq⟩ :=
    O.exists_valueGap_eq_four_mul_of_exponent_one hLt hei hej
  have hThree :
      3 * (O.value j - O.value i) < j - i :=
    O.three_mul_nextFutureMinimum_valueGap_lt_length_of_contracting
      hMin hNext hContract
  refine ⟨q, ?_, hq, ?_⟩
  · rw [hq] at hFour
    omega
  · rw [hq] at hThree
    omega

/--
最短 contracting odd-prefix の proper cuts がすべて expanding 側にあるなら、
affine translation は既存の Beatty-roof envelope 以下。

`2^D ≤ 3^k` から `D ≤ beattyIndex k` を復元し、
`affineConst` の prefix-depth finite sum を各項ごとに roof term で抑える。

terminal depth の exact critical equality は仮定しない。
-/
theorem affineConst_firstContractingOddPrefix_le_roofAffineBound
    (O : Collatz3.OddOrbit)
    {i p : ℕ}
    (hPrefix :
      ∀ k : ℕ,
        0 < k →
        k < p →
        2 ^ Word.twoSteps (O.segmentWord i k) ≤ 3 ^ k) :
    Word.affineConst (O.segmentWord i p) ≤
      CSTMicro.roofAffineBound p := by
  let w : Word := O.segmentWord i p
  have hOdd : Word.oddSteps w = p := by
    simp [w]
  rw [← Word.affinePrefixNumerator_eq_affineConst w]
  unfold Word.affinePrefixNumerator CSTMicro.roofAffineBound
  rw [hOdd]
  apply Finset.sum_le_sum
  intro k hk
  have hkLt : k < p := Finset.mem_range.mp hk
  have hCoeff :
      2 ^ Word.prefixTwoDepth w k ≤
        2 ^ Critical.beattyIndex k := by
    have hDepth :
        Word.prefixTwoDepth w k ≤ Critical.beattyIndex k := by
      apply Critical.prefixDepth_le_beatty_of_powerCoefficient
      by_cases hk0 : k = 0
      · subst k
        simp
      · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
        have hTake :
            (O.segmentWord i p).take k = O.segmentWord i k :=
          sharp_segmentWord_take_eq_of_le
            O i p k (Nat.le_of_lt hkLt)
        have hDepthEq :
            Word.prefixTwoDepth w k =
              Word.twoSteps (O.segmentWord i k) := by
          dsimp [w]
          unfold Word.prefixTwoDepth
          rw [hTake]
        rw [hDepthEq]
        exact hPrefix k hkPos hkLt
    exact
      Nat.pow_le_pow_right
        (by decide : 0 < (2 : ℕ)) hDepth
  unfold Word.affinePrefixTerm CSTMicro.roofAffineTerm
  rw [hOdd]
  exact Nat.mul_le_mul_right _ hCoeff

/--
future minimum から始まる最短 contracting odd-prefix `p` には、
Beatty-roof affine envelope に対する sharp 必要条件

`7 * 2^(criticalTwoDepth p) ≤ roofAffineBound(p) + 3 * 3^p`

が成り立つ。

理由は次の通り。

* survivor 上の future minimum start は `1` より大きい奇数なので `x ≥ 3`。
* next future minimum との差は `4` 以上で、その値は prefix endpoint 以下なので
  prefix return gap `d ≥ 4`。
* contracting なので total depth `H ≥ criticalTwoDepth p`。
* exact affine identity
  `B = 3^p*d + (2^H-3^p)*z` と `z = x+d ≥ 7` から
  `7*2^H ≤ B + 3*3^p`。
* `B ≤ roofAffineBound(p)` と `criticalTwoDepth p ≤ H` を合わせる。
-/
theorem firstContractingOddPrefix_sharpRoof_obstruction
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j p : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hpPos : 0 < p)
    (hContract :
      3 ^ p < 2 ^ Word.twoSteps (O.segmentWord i p))
    (hPrefix :
      ∀ k : ℕ,
        0 < k →
        k < p →
        2 ^ Word.twoSteps (O.segmentWord i k) ≤ 3 ^ k) :
    7 * 2 ^ Critical.criticalTwoDepth p ≤
      CSTMicro.roofAffineBound p + 3 * 3 ^ p := by
  let w : Word := O.segmentWord i p
  let x : ℕ := O.value i
  let z : ℕ := O.value (i + p)
  let d : ℕ := z - x
  let H : ℕ := Word.twoSteps w
  let g : ℕ := 2 ^ H - 3 ^ p
  let B : ℕ := Word.affineConst w
  have hRun : Runs w x z := by
    simpa [w, x, z] using O.runsSegment i p
  have hEq :
      2 ^ H * z = 3 ^ p * x + B := by
    have h :=
      (Word.endpointEquation_iff w x z).1 hRun.endpointEquation
    simpa [H, B, w] using h
  have hxz : x ≤ z := by
    dsimp [x, z]
    exact hMin.le_segment_end p
  have hzd : z = x + d := by
    dsimp [d]
    omega
  have hcontract : 3 ^ p < 2 ^ H := by
    simpa [H, w] using hContract
  have hg : 0 < g := by
    dsimp [g]
    exact Nat.sub_pos_of_lt hcontract
  have htwo : 2 ^ H = 3 ^ p + g := by
    dsimp [g]
    exact (Nat.add_sub_of_le hcontract.le).symm
  have hid : B = 3 ^ p * d + g * z := by
    have hcancel :
        3 ^ p * x + (3 ^ p * d + g * z) =
          3 ^ p * x + B := by
      calc
        3 ^ p * x + (3 ^ p * d + g * z)
            = (3 ^ p + g) * z := by
                rw [hzd]
                ring
        _ = 2 ^ H * z := by rw [htwo]
        _ = 3 ^ p * x + B := hEq
    exact (Nat.add_left_cancel hcancel).symm
  have hStartOdd := O.value_odd i
  have hStartGtOne := O.one_lt_value_of_infiniteCoefficientSurvivor S i
  have hxThree : 3 ≤ x := by
    dsimp [x]
    rcases hStartOdd with ⟨a, ha⟩
    omega
  have hFourNext : 4 ≤ O.value j - O.value i :=
    O.four_le_nextFutureMinimum_valueGap S hMin hNext
  have hNextLe : O.value j ≤ z := by
    dsimp [z]
    exact hNext.2 (i + p) (by omega)
  have hdFour : 4 ≤ d := by
    dsimp [d, z, x]
    omega
  have hzSeven : 7 ≤ z := by
    omega
  have hHPos : 0 < H := by
    by_contra hNot
    have hH0 : H = 0 := by omega
    rw [hH0, pow_zero] at hcontract
    have hThreePos : 0 < 3 ^ p := Nat.pow_pos (by decide)
    omega
  have hUpper : 3 ^ p ≤ 2 ^ H := Nat.le_of_lt hcontract
  have hBeatty : Critical.beattyIndex p ≤ H - 1 := by
    apply Critical.beattyIndex_le_of_upper
    simpa [show H - 1 + 1 = H by omega] using hUpper
  have hCriticalDepth : Critical.criticalTwoDepth p ≤ H := by
    unfold Critical.criticalTwoDepth
    omega
  have hCriticalPow :
      2 ^ Critical.criticalTwoDepth p ≤ 2 ^ H :=
    Nat.pow_le_pow_right
      (by decide : 0 < (2 : ℕ)) hCriticalDepth
  have hPd : 4 * 3 ^ p ≤ 3 ^ p * d := by
    have h := Nat.mul_le_mul_left (3 ^ p) hdFour
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hGz : 7 * g ≤ g * z := by
    have h := Nat.mul_le_mul_left g hzSeven
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  have hBLower : 4 * 3 ^ p + 7 * g ≤ B := by
    rw [hid]
    exact Nat.add_le_add hPd hGz
  have hSevenH : 7 * 2 ^ H ≤ B + 3 * 3 ^ p := by
    calc
      7 * 2 ^ H
          = (4 * 3 ^ p + 7 * g) + 3 * 3 ^ p := by
              rw [htwo]
              ring
      _ ≤ B + 3 * 3 ^ p :=
        Nat.add_le_add_right hBLower (3 * 3 ^ p)
  have hRoof : B ≤ CSTMicro.roofAffineBound p := by
    simpa [B, w] using
      O.affineConst_firstContractingOddPrefix_le_roofAffineBound
        hPrefix
  calc
    7 * 2 ^ Critical.criticalTwoDepth p
        ≤ 7 * 2 ^ H := Nat.mul_le_mul_left 7 hCriticalPow
    _ ≤ B + 3 * 3 ^ p := hSevenH
    _ ≤ CSTMicro.roofAffineBound p + 3 * 3 ^ p :=
      Nat.add_le_add_right hRoof (3 * 3 ^ p)

/--
`p < 22` では sharp obstruction の向きが必ず逆になる。

これは orbit の brute-force 検査ではなく、`beattyIndex`, `criticalTwoDepth`,
`roofAffineBound` だけからなる有限整数算術である。
-/
private theorem roofAffineBound_add_threePow_lt_seven_twoPow_of_lt_twentyTwo
    (p : ℕ)
    (hp : p < 22) :
    CSTMicro.roofAffineBound p + 3 * 3 ^ p <
      7 * 2 ^ Critical.criticalTwoDepth p := by
  interval_cases p <;> native_decide

/--
future minimum から始まる最短 contracting odd-prefix は必ず `22` odd steps 以上。

sharp roof obstruction と、`p < 22` に対する有限整数反証を衝突させる。
-/
theorem twentyTwo_le_firstContractingOddPrefix
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j p : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hpPos : 0 < p)
    (hContract :
      3 ^ p < 2 ^ Word.twoSteps (O.segmentWord i p))
    (hPrefix :
      ∀ k : ℕ,
        0 < k →
        k < p →
        2 ^ Word.twoSteps (O.segmentWord i k) ≤ 3 ^ k) :
    22 ≤ p := by
  have hNecessary :=
    O.firstContractingOddPrefix_sharpRoof_obstruction
      S hMin hNext hpPos hContract hPrefix
  by_contra hNot
  have hpLt : p < 22 := by omega
  have hImpossible :=
    roofAffineBound_add_threePow_lt_seven_twoPow_of_lt_twentyTwo p hpLt
  omega

/--
contracting next-future-minimum block の odd-step 長 `r = j-i` は少なくとも `22`。

whole block から最短 contracting prefix `p` を取り、`22 ≤ p ≤ r` を使う。
-/
theorem twentyTwo_le_nextFutureMinimum_length_of_contracting
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hContract :
      3 ^ (j - i) <
        2 ^ Word.twoSteps (O.segmentWord i (j - i))) :
    22 ≤ j - i := by
  rcases O.exists_firstContractingOddPrefix
      (i := i) (r := j - i) hContract with
    ⟨p, hpPos, hpLe, hpContract, hpPrefix⟩
  have hpTwentyTwo : 22 ≤ p :=
    O.twentyTwo_le_firstContractingOddPrefix
      S hMin hNext hpPos hpContract hpPrefix
  omega

/--
next future minimum block の Beatty excess が正なら whole block は strict contracting。
従って current 自身も future minimum なら、その長さは必ず `22` 以上。
-/
theorem twentyTwo_le_nextFutureMinimum_length_of_positive_excess
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hExcess : 0 < O.segmentBeattyExcess i (j - i)) :
    22 ≤ j - i := by
  have hContract :
      3 ^ (j - i) <
        2 ^ Word.twoSteps (O.segmentWord i (j - i)) :=
    (O.nextFutureMinimum_segmentBeattyExcess_pos_iff_threePow_lt_twoPow hNext).1
      hExcess
  exact
    O.twentyTwo_le_nextFutureMinimum_length_of_contracting
      S hMin hNext hContract

/--
`(carry, excess) = (1,1)` の flat next-future-minimum block は長さ `22` 以上。

sharp 長さ下界には carry 自体は不要で、`excess = 1` が与える strict contraction が本質。
三型分類から直接呼び出しやすい conjunction 版を残す。
-/
theorem twentyTwo_le_nextFutureMinimum_length_of_one_one
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hOneOne :
      Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 1) :
    22 ≤ j - i := by
  have hExcessPos : 0 < O.segmentBeattyExcess i (j - i) := by
    rw [hOneOne.2]
    omega
  exact
    O.twentyTwo_le_nextFutureMinimum_length_of_positive_excess
      S hMin hNext hExcessPos

end OddOrbit
end Collatz3
