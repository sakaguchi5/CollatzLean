import CollatzLean.Collatz3.CSTConditional.FutureMinimum
import CollatzLean.Collatz3.CSTConditional.ALinearGrowth

/-!
# Collatz3 CSTConditional: future minimum を基点にした defect floor

Global CST 下で future minimum `i` を固定すると、`i` から始まる任意の finite segment は
Beatty roof を越えない。これを global prefix depth / Beatty carry の加法公式へ戻すと、

`δ_i ≤ δ_n`  for every `n ≥ i`

が得られる。

注意すべき点は、これは `δ_n ≤ δ_(n+1)` を全時刻で主張するものではないこと。
block 内では defect が上下し得る。ここで保存するのは future-minimum 基点から見た
one-sided floor だけである。

さらに A 型の thin condition

`n ≤ K * δ_n`

と合わせ、future-minimum defect から先の linear staircase を有限整数不等式として記録する。
新しい A 型 packet / state は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional

/--
Global CST 下では future minimum の defect は、その後の任意の時刻の defect 以下。
-/
theorem futureMinimum_defect_le_future_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {i n : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hin : i ≤ n) :
    infiniteSurvivorDefect O.exponent i ≤
      infiniteSurvivorDefect O.exponent n := by
  let r := n - i
  have hIndex : i + r = n := by
    dsimp [r]
    exact Nat.add_sub_of_le hin
  have hZero :=
    O.segmentBeattyExcess_eq_zero_of_futureMinimum
      (r := r) G hMin
  have hSegLe :
      Word.twoSteps (O.segmentWord i r) ≤ Critical.beattyIndex r := by
    unfold segmentBeattyExcess at hZero
    omega
  have hDepth := O.infinitePrefixDepth_add_eq i r
  have hBeatty := Critical.beattyIndex_add_eq i r
  have hStart := beattyIndex_eq_prefixDepth_add_defect SInf i
  have hEnd := beattyIndex_eq_prefixDepth_add_defect SInf n
  rw [hIndex] at hDepth hBeatty
  omega

/--
linear defect lower bound の late tail では、index が `K*d` を越えれば defect は `d` より大きい。

この補題自体は future-minimum を使わない純粋な finite arithmetic。
-/
theorem defect_lt_of_mul_lt_index_of_linearDefect
    (O : Collatz3.OddOrbit)
    {K N n d : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ n)
    (hIndex : K * d < n) :
    d < infiniteSurvivorDefect O.exponent n := by
  have hMain := hLinear.2 n hLate
  by_contra hNot
  have hd : infiniteSurvivorDefect O.exponent n ≤ d := by omega
  have hMul := Nat.mul_le_mul_left K hd
  omega

/--
future minimum `i` の defect を `d` とすると、
`K*(d+q)` より先では defect は少なくとも `d+q+1`。

これが future-minimum tail の geometric defect staircase の有限核になる。
-/
theorem futureMinimum_defect_add_succ_le_of_scaled_index_lt_of_linearDefect
    (O : Collatz3.OddOrbit)
    {K N i n q : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ i)
    (hin : i ≤ n)
    (hIndex :
      K * (infiniteSurvivorDefect O.exponent i + q) < n) :
    infiniteSurvivorDefect O.exponent i + q + 1 ≤
      infiniteSurvivorDefect O.exponent n := by
  have hLateN : N ≤ n := le_trans hLate hin
  have h :=
    O.defect_lt_of_mul_lt_index_of_linearDefect
      hLinear hLateN hIndex
  omega

/--
Global CST future minimum と linear defect を合わせた late-tail floor package。

* すべての `n≥i` で `δ_n≥δ_i`。
* `n>K*(δ_i+q)` なら `δ_n≥δ_i+q+1`。
-/
theorem futureMinimum_defect_floor_package_of_linearDefect
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (SInf : O.IsInfiniteCoefficientSurvivor)
    {K N i : ℕ}
    (hLinear : O.LinearDefectLowerBound K N)
    (hLate : N ≤ i)
    (hMin : O.FutureMinimumAt i) :
    (∀ n : ℕ, i ≤ n →
      infiniteSurvivorDefect O.exponent i ≤
        infiniteSurvivorDefect O.exponent n) ∧
    (∀ n q : ℕ,
      i ≤ n →
      K * (infiniteSurvivorDefect O.exponent i + q) < n →
      infiniteSurvivorDefect O.exponent i + q + 1 ≤
        infiniteSurvivorDefect O.exponent n) := by
  constructor
  · intro n hin
    exact O.futureMinimum_defect_le_future_of_globalCST G SInf hMin hin
  · intro n q hin hIndex
    exact
      O.futureMinimum_defect_add_succ_le_of_scaled_index_lt_of_linearDefect
        hLinear hLate hin hIndex

end OddOrbit
end Collatz3
