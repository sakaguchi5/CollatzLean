import CollatzLean.Collatz2.CSTMicro.ExternalArithmetic.PureBSingleCornerLog196StrongClosure

set_option linter.style.emptyLine false
set_option exponentiation.threshold 5300

/-!
# Pure B single-corner: degree 196 route の遠方 threshold 自動化

exact BHZ 初期 band は `ell <= 5287` まで処理する。
このファイルでは `ell >= 5288` だけを既存 degree-196 route に渡す。

重要なのは、196 次 bound を main geometry に戻すことではなく、
十分遠方では

  width(ell+1) <= 2 * width(ell)

となる一方、dyadic lower scale は毎回 exact に 2 倍になること。
したがって `ell=5288` の一回の base inequality から全遠方を帰納できる。
-/

namespace Collatz2
namespace CSTMicro
namespace ExternalArithmetic

/--
`ell >= 511` なら 196 次冪は一段進んでも高々 2 倍。

`512*(ell+2) <= 513*(ell+1)` と
`513^196 <= 2*512^196` を整数演算だけで組み合わせる。
-/
theorem add_two_pow196_le_two_mul_add_one_pow196
    {ell : ℕ}
    (hell : 511 <= ell) :
    (ell + 2) ^ 196 <= 2 * (ell + 1) ^ 196 := by
  have hScale :
      512 * (ell + 2) <= 513 * (ell + 1) := by
    omega
  have hPow := Nat.pow_le_pow_left hScale 196
  rw [mul_pow, mul_pow] at hPow
  have hRatio :
      513 ^ 196 <= 2 * 512 ^ 196 := by
    norm_num
  have hRatioMul :=
    Nat.mul_le_mul_right ((ell + 1) ^ 196) hRatio
  have hCombined :
      512 ^ 196 * (ell + 2) ^ 196 <=
        512 ^ 196 * (2 * (ell + 1) ^ 196) := by
    calc
      512 ^ 196 * (ell + 2) ^ 196
          <= 513 ^ 196 * (ell + 1) ^ 196 := hPow
      _ <= (2 * 512 ^ 196) * (ell + 1) ^ 196 := hRatioMul
      _ = 512 ^ 196 * (2 * (ell + 1) ^ 196) := by
            ring
  exact
    Nat.le_of_mul_le_mul_left hCombined (by positivity)

/--
任意の one-short window constant に対し、十分遠方では
single-corner degree-196 width は一段で高々 2 倍。
-/
theorem singleCornerDyadicLog196Width_succ_le_two_mul
    (W : CriticalSturmianOneShortSquareWindow196)
    {ell : ℕ}
    (hell : 511 <= ell) :
    singleCornerDyadicLog196Width W (ell + 1) <=
      2 * singleCornerDyadicLog196Width W ell := by
  have hPow :=
    add_two_pow196_le_two_mul_add_one_pow196 hell
  have hMain :=
    Nat.mul_le_mul_left
      (terminalOneShortSquareLog196Constant W) hPow
  have hLinear :
      18 + 15 * (ell + 1) <=
        2 * (18 + 15 * ell) := by
    omega
  unfold singleCornerDyadicLog196Width
  calc
    terminalOneShortSquareLog196Constant W * (ell + 2) ^ 196 +
        (18 + 15 * (ell + 1))
        <=
      terminalOneShortSquareLog196Constant W *
          (2 * (ell + 1) ^ 196) +
        2 * (18 + 15 * ell) :=
      Nat.add_le_add hMain hLinear
    _ =
      2 *
        (terminalOneShortSquareLog196Constant W * (ell + 1) ^ 196 +
          (18 + 15 * ell)) := by
      ring

/--
actual BHZ196 window constant は `2^226` 以下。

ここだけで finite convergent table と `criticalPowerPGapC2` の
explicit evaluation を処理する。
-/
theorem actualCriticalSturmianOneShortSquareWindow196_constant_le_pow226
    (R : RhinLinearForm14) :
    (actualCriticalSturmianOneShortSquareWindow196 R).constant ≤ 2 ^ 226 := by
  have hP10 : criticalPowerP 10 = 15601 := by
    norm_num [
      criticalPowerP,
      criticalPowerConvergent,
      criticalInitialConvergent
    ]

  have hC2 : criticalPowerPGapC2 = 2 ^ 225 := by
    norm_num [
      criticalPowerPGapC2,
      criticalPowerPGapC1
    ]

  dsimp [actualCriticalSturmianOneShortSquareWindow196]
  unfold criticalOneShortSquareWindow196Constant
  rw [hP10, hC2]
  norm_num

/--
actual BHZ196 の terminal coefficient は `2^1207` 以下。

`20^196 ≤ 2^980` と actual window constant の
`2^226` majorant を掛け合わせる。
-/
theorem actual_terminalOneShortSquareLog196Constant_le_pow1207
    (R : RhinLinearForm14) :
    terminalOneShortSquareLog196Constant
        (actualCriticalSturmianOneShortSquareWindow196 R) ≤
      2 ^ 1207 := by
  let W := actualCriticalSturmianOneShortSquareWindow196 R

  have hW : W.constant ≤ 2 ^ 226 := by
    simpa [W] using
      actualCriticalSturmianOneShortSquareWindow196_constant_le_pow226 R

  have h20 : 20 ^ 196 ≤ 2 ^ 980 := by
    have hBase : (20 : ℕ) ≤ 2 ^ 5 := by
      norm_num
    have hPow := Nat.pow_le_pow_left hBase 196
    calc
      20 ^ 196 ≤ (2 ^ 5) ^ 196 := hPow
      _ = 2 ^ 980 := by
        rw [← pow_mul]

  unfold terminalOneShortSquareLog196Constant
  calc
    2 * W.constant * 20 ^ 196
        ≤ 2 * (2 ^ 226) * (2 ^ 980) := by
          exact Nat.mul_le_mul
            (Nat.mul_le_mul_left 2 hW) h20
    _ = 2 ^ 1207 := by
      calc
        2 * (2 ^ 226) * (2 ^ 980)
            = (2 ^ 1) * (2 ^ 226) * (2 ^ 980) := by
              norm_num
        _ = 2 ^ (1 + 226 + 980) := by
              rw [← pow_add, ← pow_add]
        _ = 2 ^ 1207 := by
              norm_num

/--
actual BHZ196 width の `ell=5288` における dyadic majorant。

terminal part は `2^3755` 以下、
linear tail はそれより十分小さいため、
全体を `2^3756` で抑える。
-/
theorem actual_singleCornerDyadicLog196Width_le_pow3756
    (R : RhinLinearForm14) :
    singleCornerDyadicLog196Width
        (actualCriticalSturmianOneShortSquareWindow196 R) 5288 ≤
      2 ^ 3756 := by
  let W := actualCriticalSturmianOneShortSquareWindow196 R

  have hTerminal :
      terminalOneShortSquareLog196Constant W ≤ 2 ^ 1207 := by
    simpa [W] using
      actual_terminalOneShortSquareLog196Constant_le_pow1207 R

  have h5289 : (5289 : ℕ) ≤ 2 ^ 13 := by
    norm_num

  have hPoly : 5289 ^ 196 ≤ 2 ^ 2548 := by
    have hPow := Nat.pow_le_pow_left h5289 196
    calc
      5289 ^ 196 ≤ (2 ^ 13) ^ 196 := hPow
      _ = 2 ^ 2548 := by
        rw [← pow_mul]

  have hProduct :
      terminalOneShortSquareLog196Constant W * 5289 ^ 196 ≤
        2 ^ 3755 := by
    calc
      terminalOneShortSquareLog196Constant W * 5289 ^ 196
          ≤ (2 ^ 1207) * (2 ^ 2548) := by
            exact Nat.mul_le_mul hTerminal hPoly
      _ = 2 ^ 3755 := by
            rw [← pow_add]

  have hLinear :
      18 + 15 * 5288 ≤ 2 ^ 17 := by
    norm_num

  have hSmallPow :
      2 ^ 17 ≤ 2 ^ 3755 :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      (by omega)

  have hWidthW :
      singleCornerDyadicLog196Width W 5288 ≤ 2 ^ 3756 := by
    unfold singleCornerDyadicLog196Width
    calc
      terminalOneShortSquareLog196Constant W * 5289 ^ 196 +
          (18 + 15 * 5288)
          ≤ 2 ^ 3755 + 2 ^ 17 := by
            exact Nat.add_le_add hProduct hLinear
      _ ≤ 2 ^ 3755 + 2 ^ 3755 := by
            exact Nat.add_le_add_left hSmallPow _
      _ = 2 ^ 3756 := by
            rw [show 3756 = 3755 + 1 by omega, pow_succ]
            ring_nf

  simpa [W] using hWidthW

/--
`ell=5288` の actual BHZ196 width に係数 `3` と定数 `2` を付けても、
`2^3758` の中に収まる。
-/
theorem actual_three_mul_singleCornerDyadicLog196Width_add_two_le_pow3758
    (R : RhinLinearForm14) :
    3 *
        singleCornerDyadicLog196Width
          (actualCriticalSturmianOneShortSquareWindow196 R) 5288 +
        2 ≤
      2 ^ 3758 := by
  have hWidth :=
    actual_singleCornerDyadicLog196Width_le_pow3756 R

  have hTwo :
      2 ≤ 2 ^ 3756 := by
    have hLarge :
        2 ^ 1 ≤ 2 ^ 3756 :=
      Nat.pow_le_pow_right
        (by omega : 0 < (2 : ℕ))
        (by omega)
    simp only [Nat.reducePow, Nat.reduceLeDiff]

  have hFour :
      4 * 2 ^ 3756 = 2 ^ 3758 := by
    rw [show 3758 = 3756 + 2 by omega, pow_add]
    norm_num

  calc
    3 *
          singleCornerDyadicLog196Width
            (actualCriticalSturmianOneShortSquareWindow196 R) 5288 +
        2
        ≤ 3 * (2 ^ 3756) + 2 := by
          exact Nat.add_le_add_right
            (Nat.mul_le_mul_left 3 hWidth) 2
    _ ≤ 4 * 2 ^ 3756 := by
          omega
    _ = 2 ^ 3758 := hFour

/--
actual BHZ196 width の `ell=5288` base inequality。

実際の width は `2^3756` 以下であり、
係数 `3` と additive constant `2` を吸収しても `2^3758` 以下。
最後に `3758 ≤ 5287` を使って所望の scale に埋め込む。
-/
theorem actual_singleCornerDyadicLog196Width_base_5288
    (R : RhinLinearForm14) :
    3 *
        singleCornerDyadicLog196Width
          (actualCriticalSturmianOneShortSquareWindow196 R) 5288 +
        2 ≤
      2 ^ 5287 := by
  have hThree :
      3 *
          singleCornerDyadicLog196Width
            (actualCriticalSturmianOneShortSquareWindow196 R) 5288 +
          2 ≤
        2 ^ 3758 :=
    actual_three_mul_singleCornerDyadicLog196Width_add_two_le_pow3758 R

  have hFar :
      2 ^ 3758 ≤ 2 ^ 5287 :=
    Nat.pow_le_pow_right
      (by omega : 0 < (2 : ℕ))
      (by omega)

  exact le_trans hThree hFar

/--
`ell >= 5288` では actual degree-196 threshold が dyadic lower scale より小さい。

base `5288` と width doubling を strong induction で接続する。
-/
theorem actual_singleCornerDyadicLog196Width_eventual_threshold
    (R : RhinLinearForm14)
    {ell : ℕ}
    (hell : 5288 <= ell) :
    3 * singleCornerDyadicLog196Width
          (actualCriticalSturmianOneShortSquareWindow196 R) ell + 2 <=
      2 ^ (ell - 1) := by
  revert hell
  induction ell using Nat.strong_induction_on with
  | h ell ih =>
      intro hell
      by_cases hEq : ell = 5288
      · subst ell
        simpa using actual_singleCornerDyadicLog196Width_base_5288 R
      · have hellPrev : 5288 <= ell - 1 := by
          omega
        have hPrevLt : ell - 1 < ell := by
          omega
        have hIH := ih (ell - 1) hPrevLt hellPrev
        have hDouble :=
          singleCornerDyadicLog196Width_succ_le_two_mul
            (actualCriticalSturmianOneShortSquareWindow196 R)
            (ell := ell - 1)
            (by omega)
        have hSucc : ell - 1 + 1 = ell := by
          omega
        rw [hSucc] at hDouble
        have hExp :
            ell - 1 = (ell - 1 - 1) + 1 := by
          omega
        rw [hExp, pow_succ]
        omega

end ExternalArithmetic
end CSTMicro
end Collatz2
