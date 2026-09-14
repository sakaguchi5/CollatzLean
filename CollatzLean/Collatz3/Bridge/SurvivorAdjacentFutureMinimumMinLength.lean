import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimum
import CollatzLean.Collatz3.Core.PrefixAffine

/-!
# Collatz3 Bridge: contracting next future minimum block の最小長 13

隣接 future minimum block が coefficient として strict contracting なら、
その block の途中には「odd boundary で初めて contracting 側へ入る」最短 prefix がある。

このファイルでは旧 `FirstCrossingData` や大きな packet を復活させない。
現行 `OddOrbit`, `Word`, `Runs`, `NextFutureMinimum` のみから、次の鎖を derived theorem として閉じる。

* 最短 contracting prefix `p` の存在。
* すべての proper positive prefix は coefficient-expanding 側、すなわち
  `2^D ≤ 3^k` にある。
* prefix-depth finite sum から `B ≤ p * 3^(p-1)`。
* actual endpoint equation から return gap `d` に対して `3*d < p`。
* infinite coefficient survivor の二つの future minimum は exponent `1` なので、
  その値差は正の `4` の倍数。
* next future minimum は first contracting prefix endpoint 以下なので `4 ≤ d`。
* 従って `12 < p`、すなわち `13 ≤ p`。
* `p ≤ r` なので contracting whole block 自身も `13 ≤ r`。

特に `(carry, excess) = (1,1)` は excess が正なので、この最小長制約を満たす。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
長さ `r` の segment の先頭 `k ≤ r` 個は、長さ `k` の segment そのもの。

既存 `segmentWord` の再帰だけから導く局所補題で、新しい語彙は導入しない。
-/
private theorem segmentWord_take_eq_of_le
    (O : Collatz3.OddOrbit)
    (i r k : ℕ)
    (hk : k ≤ r) :
    (O.segmentWord i r).take k = O.segmentWord i k := by
  induction k generalizing i r with
  | zero =>
      simp
  | succ k ih =>
      cases r with
      | zero =>
          omega
      | succ r =>
          simp only [segmentWord_succ, List.take_succ_cons]
          rw [ih (i := i + 1) (r := r) (by omega)]

/--
strict contracting segment には、odd boundary で初めて contracting になる最短 prefix がある。

`p` は正で `p ≤ r`、terminal では `3^p < 2^H`。
最短性により任意の `0 < k < p` ではまだ
`2^D ≤ 3^k` の expanding 側に留まる。
-/
theorem exists_firstContractingOddPrefix
    (O : Collatz3.OddOrbit)
    {i r : ℕ}
    (hContract :
      3 ^ r < 2 ^ Word.twoSteps (O.segmentWord i r)) :
    ∃ p : ℕ,
      0 < p ∧
      p ≤ r ∧
      3 ^ p < 2 ^ Word.twoSteps (O.segmentWord i p) ∧
      ∀ k : ℕ,
        0 < k →
        k < p →
        2 ^ Word.twoSteps (O.segmentWord i k) ≤ 3 ^ k := by
  have hrPos : 0 < r := by
    by_contra hNot
    have hr0 : r = 0 := by omega
    subst r
    simp at hContract
  let P : ℕ → Prop := fun p =>
    0 < p ∧
      p ≤ r ∧
      3 ^ p < 2 ^ Word.twoSteps (O.segmentWord i p)
  have hex : ∃ p : ℕ, P p := by
    exact ⟨r, hrPos, le_rfl, hContract⟩
  let p : ℕ := Nat.find hex
  have hpSpec : P p := by
    dsimp [p]
    exact Nat.find_spec hex
  refine ⟨p, hpSpec.1, hpSpec.2.1, hpSpec.2.2, ?_⟩
  intro k hkPos hkLt
  by_contra hNot
  have hkContract :
      3 ^ k < 2 ^ Word.twoSteps (O.segmentWord i k) :=
    Nat.lt_of_not_ge hNot
  have hkLeR : k ≤ r :=
    le_trans (Nat.le_of_lt hkLt) hpSpec.2.1
  have hkP : P k :=
    ⟨hkPos, hkLeR, hkContract⟩
  have hpLeK : p ≤ k := by
    dsimp [p]
    exact Nat.find_min' hex hkP
  omega

/--
proper positive prefix がすべて `2^D ≤ 3^k` にある長さ `p` の actual segment では、
affine translation は coarse bound

`B ≤ p * 3^(p-1)`

を満たす。

証明は `affineConst` の prefix-depth finite sum を各項ごとに直接評価する。
旧 weighted-prefix packet は使わない。
-/
private theorem affineConst_segment_le_length_mul_threePow_pred
    (O : Collatz3.OddOrbit)
    {i p : ℕ}
    (hpPos : 0 < p)
    (hPrefix :
      ∀ k : ℕ,
        0 < k →
        k < p →
        2 ^ Word.twoSteps (O.segmentWord i k) ≤ 3 ^ k) :
    Word.affineConst (O.segmentWord i p) ≤
      p * 3 ^ (p - 1) := by
  let w : Word := O.segmentWord i p
  have hOdd : Word.oddSteps w = p := by
    simp [w]
  rw [← Word.affinePrefixNumerator_eq_affineConst w]
  unfold Word.affinePrefixNumerator
  rw [hOdd]
  calc
    (∑ k ∈ Finset.range p, Word.affinePrefixTerm w k)
        ≤ ∑ k ∈ Finset.range p, 3 ^ (p - 1) := by
          apply Finset.sum_le_sum
          intro k hk
          have hkLt : k < p := Finset.mem_range.mp hk
          have hPow :
              2 ^ Word.prefixTwoDepth w k ≤ 3 ^ k := by
            by_cases hk0 : k = 0
            · subst k
              simp
            · have hkPos : 0 < k := Nat.pos_of_ne_zero hk0
              have hTake :
                  (O.segmentWord i p).take k = O.segmentWord i k :=
                segmentWord_take_eq_of_le O i p k (Nat.le_of_lt hkLt)
              have hDepth :
                  Word.prefixTwoDepth w k =
                    Word.twoSteps (O.segmentWord i k) := by
                dsimp [w]
                unfold Word.prefixTwoDepth
                rw [hTake]
              rw [hDepth]
              exact hPrefix k hkPos hkLt
          unfold Word.affinePrefixTerm
          rw [hOdd]
          calc
            2 ^ Word.prefixTwoDepth w k * 3 ^ (p - (k + 1))
                ≤ 3 ^ k * 3 ^ (p - (k + 1)) :=
              Nat.mul_le_mul_right _ hPow
            _ = 3 ^ (p - 1) := by
              have hExp : k + (p - (k + 1)) = p - 1 := by
                omega
              rw [← pow_add, hExp]
    _ = p * 3 ^ (p - 1) := by
      simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]

/--
future minimum から始まる最短 contracting odd-prefix の return gap を
`d = endpoint - start` とすると `3*d < p`。

中心は exact identity

`B = 3^p * d + (2^H - 3^p) * endpoint`

と前定理の `B ≤ p * 3^(p-1)`。
contracting gap と endpoint はともに正なので `3^p*d < B` になり、
共通因子 `3^(p-1)` を消去して得る。
-/
theorem three_mul_firstContractingOddPrefixReturnGap_lt_length
    (O : Collatz3.OddOrbit)
    {i p : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hpPos : 0 < p)
    (hContract :
      3 ^ p < 2 ^ Word.twoSteps (O.segmentWord i p))
    (hPrefix :
      ∀ k : ℕ,
        0 < k →
        k < p →
        2 ^ Word.twoSteps (O.segmentWord i k) ≤ 3 ^ k) :
    3 * (O.value (i + p) - O.value i) < p := by
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
  have hzPos : 0 < z := by
    dsimp [z]
    rcases O.value_odd (i + p) with ⟨q, hq⟩
    omega
  have hgz : 0 < g * z := Nat.mul_pos hg hzPos
  have hLow : 3 ^ p * d < B := by
    rw [hid]
    omega
  have hB : B ≤ p * 3 ^ (p - 1) := by
    simpa [B, w] using
      affineConst_segment_le_length_mul_threePow_pred
        O hpPos hPrefix
  have hChain : 3 ^ p * d < p * 3 ^ (p - 1) :=
    lt_of_lt_of_le hLow hB
  obtain ⟨r, hr⟩ : ∃ r : ℕ, p = r + 1 := by
    exact ⟨p - 1, by omega⟩
  subst p
  have hPowPos : 0 < 3 ^ r := Nat.pow_pos (by omega)
  have hScaled :
      3 ^ r * (3 * d) < 3 ^ r * (r + 1) := by
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hChain
  have hResult : 3 * d < r + 1 :=
    (Nat.mul_lt_mul_left hPowPos).mp hScaled
  simpa [d, z, x] using hResult

/--
指数 `1` の二つの actual odd position で後者の値が大きいなら、
その値差は `4` の正倍数として書ける。

これは各位置の一歩先が odd であることと
`2*y' = 3*y + 1` の exact equation だけから従う。
-/
theorem exists_valueGap_eq_four_mul_of_exponent_one
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hij : O.value i < O.value j)
    (hei : O.exponent i = 1)
    (hej : O.exponent j = 1) :
    ∃ q : ℕ, O.value j - O.value i = 4 * q := by
  have hsi :
      2 * O.value (i + 1) = 3 * O.value i + 1 := by
    have h := (O.step i).equation
    simpa [hei] using h
  have hsj :
      2 * O.value (j + 1) = 3 * O.value j + 1 := by
    have h := (O.step j).equation
    simpa [hej] using h
  rcases O.value_odd (i + 1) with ⟨a, ha⟩
  rcases O.value_odd (j + 1) with ⟨b, hb⟩
  rw [ha] at hsi
  rw [hb] at hsj
  have hab : a < b := by
    omega
  let d : ℕ := O.value j - O.value i
  let t : ℕ := b - a
  have hdPos : 0 < d := by
    dsimp [d]
    omega
  have htPos : 0 < t := by
    dsimp [t]
    omega
  have hrelation : 3 * d = 4 * t := by
    dsimp [d, t]
    omega
  have htd : t < d := by
    omega
  refine ⟨d - t, ?_⟩
  dsimp [d, t] at hrelation htd ⊢
  omega

/--
infinite coefficient survivor 上で、current `i` 自身も future minimum であり、
`j` がその次の tail minimum なら、二つの future-minimum 値差は少なくとも `4`。

両 endpoint の exponent は exact に `1`。
等値は nontrivial repeat になるので survivor では起こらず、値差は正の `4` の倍数になる。
-/
theorem four_le_nextFutureMinimum_valueGap
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    4 ≤ O.value j - O.value i := by
  have hLe : O.value i ≤ O.value j :=
    hMin j (Nat.le_of_lt hNext.1)
  have hiNeOne : O.value i ≠ 1 := by
    exact ne_of_gt (O.one_lt_value_of_infiniteCoefficientSurvivor S i)
  have hNe : O.value i ≠ O.value j := by
    intro hEq
    apply O.no_nontrivialRepeat_of_infiniteCoefficientSurvivor S
    exact ⟨i, j, hNext.1, hEq, hiNeOne⟩
  have hLt : O.value i < O.value j := by
    omega
  have hei : O.exponent i = 1 :=
    O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor S hMin
  have hej : O.exponent j = 1 :=
    O.nextFutureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor S hNext
  obtain ⟨q, hq⟩ :=
    O.exists_valueGap_eq_four_mul_of_exponent_one hLt hei hej
  have hGapPos : 0 < O.value j - O.value i := by
    omega
  rw [hq] at hGapPos ⊢
  have hqPos : 0 < q := by omega
  omega

/--
current future minimum `i` から next future minimum `j` までの whole block が
strict contracting なら、その odd-step 長 `r = j-i` は少なくとも `13`。

whole block 内の最短 contracting prefix `p` を取ると

`4 ≤ d`, `3*d < p`, `p ≤ r`

なので `13 ≤ p ≤ r`。

この theorem は carry を一切仮定しない。したがって `(1,1)` だけでなく、
任意の contracting next-future-minimum block に使える。
-/
theorem thirteen_le_nextFutureMinimum_length_of_contracting
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hContract :
      3 ^ (j - i) <
        2 ^ Word.twoSteps (O.segmentWord i (j - i))) :
    13 ≤ j - i := by
  rcases O.exists_firstContractingOddPrefix
      (i := i) (r := j - i) hContract with
    ⟨p, hpPos, hpLe, hpContract, hpPrefix⟩
  have hThree :
      3 * (O.value (i + p) - O.value i) < p :=
    O.three_mul_firstContractingOddPrefixReturnGap_lt_length
      hMin hpPos hpContract hpPrefix
  have hFour : 4 ≤ O.value j - O.value i :=
    O.four_le_nextFutureMinimum_valueGap S hMin hNext
  have hNextLe : O.value j ≤ O.value (i + p) :=
    hNext.2 (i + p) (by omega)
  have hGapLe :
      O.value j - O.value i ≤
        O.value (i + p) - O.value i := by
    omega
  have hFourReturn : 4 ≤ O.value (i + p) - O.value i :=
    le_trans hFour hGapLe
  omega

/--
next future minimum block の Beatty excess が正なら whole block は strict contracting。
従って current 自身も future minimum である場合、その長さは必ず `13` 以上。
-/
theorem thirteen_le_nextFutureMinimum_length_of_positive_excess
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hExcess : 0 < O.segmentBeattyExcess i (j - i)) :
    13 ≤ j - i := by
  have hContract :
      3 ^ (j - i) <
        2 ^ Word.twoSteps (O.segmentWord i (j - i)) :=
    (O.nextFutureMinimum_segmentBeattyExcess_pos_iff_threePow_lt_twoPow hNext).1
      hExcess
  exact
    O.thirteen_le_nextFutureMinimum_length_of_contracting
      S hMin hNext hContract

/--
`(carry, excess) = (1,1)` の flat next-future-minimum block は長さ `13` 以上。

長さ下界そのものには carry の値は不要で、`excess = 1` が与える strict contraction が本質。
ここでは二条件を一つの conjunction として受け取り、現在の三型分類からそのまま適用できる形にする。
-/
theorem thirteen_le_nextFutureMinimum_length_of_one_one
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hOneOne :
      Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 1) :
    13 ≤ j - i := by
  have hExcessPos : 0 < O.segmentBeattyExcess i (j - i) := by
    rw [hOneOne.2]
    omega
  exact
    O.thirteen_le_nextFutureMinimum_length_of_positive_excess
      S hMin hNext hExcessPos

end OddOrbit
end Collatz3
