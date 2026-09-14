import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimum
import CollatzLean.Collatz3.Critical.RoofAnchor

/-!
# Collatz3 Bridge: 隣接 future minimum defect の三連続上昇禁止

`SurvivorAdjacentFutureMinimum` では、隣接 future minimum block `i → j` に対して

`δ_j + q = δ_i + c`

を得た。ここで `q` は segment Beatty excess、`c ∈ {0,1}` は Beatty carry である。
従って defect が exact に `+1` される block は

* `q = 0`、
* `c = 1`

に限られる。

このファイルでは、この `+1` block が二つ連続した後の一歩 carry を調べる。
新しい primitive definition は導入しない。

中心は完全に整数的な評価である。

1. future minimum から始まる `+1` block の長さを `r` とすると、
   `r = 1`、または `beattyIndex r = beattyIndex (r-1) + 2`。
2. 従ってその長さは
   `2 * 3^r ≤ 3 * 2^(beattyIndex r)`
   を満たす。
3. 二つの `+1` block を掛け合わせると、二つ目の終点 `k` では
   `beattyCarry k 1 = 0`。
4. `k` 自身も future minimum なので `e_k = 1`。従って
   `δ_(k+1) = δ_k`。
5. 次の future minimum `l` では proper-suffix monotonicity により
   `δ_l ≤ δ_k`。

従って隣接 future minimum 列に沿った defect の `+1,+1,+1` は不可能である。

実数 `log₂` phase は使わず、既存の Beatty power-form と actual suffix 幾何だけで閉じる。
-/

namespace Collatz3
namespace Bridge

/--
normalized survivor Sturmian step は、一歩 Beatty carry `beattyCarry m 1` そのもの。

二つの表現を必要な場所で毎回展開しないための derived bridge。
-/
theorem survivorSturmianStep_eq_beattyCarry_one
    (m : ℕ) :
    survivorSturmianStep m = Critical.beattyCarry m 1 := by
  have hm := index_le_beattyIndex m
  have hm1 := index_le_beattyIndex (m + 1)
  have hAdd := Critical.beattyIndex_add_eq m 1
  rw [Critical.beattyIndex_one] at hAdd
  unfold survivorSturmianStep survivorRoofExcess
  omega

end Bridge

namespace OddOrbit

open Bridge

/--
future minimum から始まり defect を `+1` する next block の長さ `r` は、

* `r = 1`、または
* `beattyIndex r = beattyIndex (r-1) + 2`

のどちらか。

`r>1` では先頭 exponent が `1` で、残り proper suffix は strict contracting。
その suffix は critical depth 以上なので、whole depth `beattyIndex r` は
`beattyIndex (r-1)+2` 以上になる。一歩 Beatty 増分の上界 `≤2` と合わせて exact equality を得る。
-/
theorem nextFutureMinimum_defect_succ_length_eq_one_or_beattyJumpTwo
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hRise :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1) :
    j - i = 1 ∨
      Critical.beattyIndex (j - i) =
        Critical.beattyIndex (j - i - 1) + 2 := by
  let r : ℕ := j - i
  have hrPos : 0 < r := by
    dsimp [r]
    exact Nat.sub_pos_of_lt hNext.1
  by_cases hrOne : r = 1
  · left
    simpa [r] using hrOne
  · right
    have hrGt : 1 < r := by omega
    have hExcessZero : O.segmentBeattyExcess i r = 0 := by
      have h := (O.nextFutureMinimum_defect_eq_succ_iff S hNext).1 hRise
      simpa [r] using h.2
    have hDepthEq :
        Word.twoSteps (O.segmentWord i r) = Critical.beattyIndex r := by
      have hDepth :=
        O.nextFutureMinimum_beattyIndex_add_segmentBeattyExcess_eq_segmentTwoSteps
          hNext
      rw [show j - i = r by rfl, hExcessZero] at hDepth
      omega
    have heI : O.exponent i = 1 :=
      O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor S hStart
    have hInternal : i + 1 < j := by
      dsimp [r] at hrGt
      omega
    have hSuffix :=
      O.nextFutureMinimum_properSuffix_criticalTwoDepth_le
        S hNext (k := i + 1) (by omega) hInternal
    have hSuffixLen : j - (i + 1) = r - 1 := by
      dsimp [r]
      omega
    rw [hSuffixLen] at hSuffix
    unfold Critical.criticalTwoDepth at hSuffix
    have hrDecomp : r = (r - 1) + 1 := by omega
    have hTotal :
        Word.twoSteps (O.segmentWord i r) =
          O.exponent i + Word.twoSteps (O.segmentWord (i + 1) (r - 1)) := by
      rw [hrDecomp, O.segmentWord_succ]
      simp
    have hLower :
        Critical.beattyIndex (r - 1) + 2 ≤ Critical.beattyIndex r := by
      omega
    have hUpperRaw := beattyIndex_succ_le_add_two (r - 1)
    have hUpper :
        Critical.beattyIndex r ≤ Critical.beattyIndex (r - 1) + 2 := by
      rw [show r - 1 + 1 = r by omega] at hUpperRaw
      exact hUpperRaw
    have hEq :
        Critical.beattyIndex r = Critical.beattyIndex (r - 1) + 2 :=
      Nat.le_antisymm hUpper hLower
    simpa [r] using hEq

/--
future minimum から始まり defect を `+1` する block 長 `r` の power-form 上界。

`3^r / 2^beattyIndex(r) ≤ 3/2`

を自然数の除算を使わず

`2 * 3^r ≤ 3 * 2^beattyIndex(r)`

と書く。

`r=1` では等号。`r>1` では直前 theorem の Beatty jump `+2` と
`beattyIndex_upper (r-1)` だけから従う。
-/
theorem nextFutureMinimum_defect_succ_length_power_bound
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hRise :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1) :
    2 * 3 ^ (j - i) ≤
      3 * 2 ^ Critical.beattyIndex (j - i) := by
  let r : ℕ := j - i
  have hCases :=
    O.nextFutureMinimum_defect_succ_length_eq_one_or_beattyJumpTwo
      S hStart hNext hRise
  have hCases' :
      r = 1 ∨
        Critical.beattyIndex r = Critical.beattyIndex (r - 1) + 2 := by
    simpa [r] using hCases
  change 2 * 3 ^ r ≤ 3 * 2 ^ Critical.beattyIndex r
  rcases hCases' with hrOne | hJump
  · rw [hrOne]
    norm_num [Critical.beattyIndex_one]
  · have hrPos : 0 < r := by
      dsimp [r]
      exact Nat.sub_pos_of_lt hNext.1
    have hrGt : 1 < r := by
      by_contra hNot
      have hrOne : r = 1 := by
        omega
      rw [hrOne] at hJump
      norm_num [Critical.beattyIndex_one] at hJump
    have hUpper := Critical.beattyIndex_upper (r - 1)
    have hScaled := Nat.mul_le_mul_left 6 hUpper
    have hrDecomp : r = (r - 1) + 1 := by omega
    calc
      2 * 3 ^ r = 6 * 3 ^ (r - 1) := by
        rw [hrDecomp, pow_succ]
        ring_nf
        simp
      _ ≤ 6 * 2 ^ (Critical.beattyIndex (r - 1) + 1) := hScaled
      _ = 3 * 2 ^ Critical.beattyIndex r := by
        rw [hJump]
        rw [show Critical.beattyIndex (r - 1) + 2 =
          (Critical.beattyIndex (r - 1) + 1) + 1 by omega]
        rw [pow_succ]
        ring

/--
二つの defect `+1` next blocks が連続すると、二つ目の終点 `k` の
**次の一歩 Beatty carry は 0**。

実数 phase は使わない。
各 `+1` block 長 `a,b` の power bound

`2*3^a ≤ 3*2^B_a`, `2*3^b ≤ 3*2^B_b`

と `3^i ≤ 2^(B_i+1)` を掛け合わせる。
二つの block carry がともに `1` なので

`B_k = B_i + B_a + B_b + 2`。

最後に `27 < 32` を使うと

`3^(k+1) ≤ 2^(B_k+2)`

となり、Beatty index の最小性から `B_(k+1)=B_k+1`、従って carry は 0。
-/
theorem double_nextFutureMinimum_defect_succ_beattyCarry_one_eq_zero
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hIJ : O.NextFutureMinimum i j)
    (hJK : O.NextFutureMinimum j k)
    (hRiseIJ :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1)
    (hRiseJK :
      infiniteSurvivorDefect O.exponent k =
        infiniteSurvivorDefect O.exponent j + 1) :
    Critical.beattyCarry k 1 = 0 := by
  let a : ℕ := j - i
  let b : ℕ := k - j
  have haPos : 0 < a := by
    dsimp [a]
    exact Nat.sub_pos_of_lt hIJ.1
  have hbPos : 0 < b := by
    dsimp [b]
    exact Nat.sub_pos_of_lt hJK.1
  have hJIndex : i + a = j := by
    dsimp [a]
    exact Nat.add_sub_of_le (Nat.le_of_lt hIJ.1)
  have hKIndex : j + b = k := by
    dsimp [b]
    exact Nat.add_sub_of_le (Nat.le_of_lt hJK.1)
  have hKIndex' : i + a + b = k := by omega
  have hBoundA :
      2 * 3 ^ a ≤ 3 * 2 ^ Critical.beattyIndex a := by
    simpa [a] using
      O.nextFutureMinimum_defect_succ_length_power_bound
        S hStart hIJ hRiseIJ
  have hMinJ : O.FutureMinimumAt j := hIJ.futureMinimumAt
  have hBoundB :
      2 * 3 ^ b ≤ 3 * 2 ^ Critical.beattyIndex b := by
    simpa [b] using
      O.nextFutureMinimum_defect_succ_length_power_bound
        S hMinJ hJK hRiseJK
  have hCarryA : Critical.beattyCarry i a = 1 := by
    have h := (O.nextFutureMinimum_defect_eq_succ_iff S hIJ).1 hRiseIJ
    simpa [a] using h.1
  have hCarryB : Critical.beattyCarry j b = 1 := by
    have h := (O.nextFutureMinimum_defect_eq_succ_iff S hJK).1 hRiseJK
    simpa [b] using h.1
  have hAddA := Critical.beattyIndex_add_eq i a
  rw [hJIndex, hCarryA] at hAddA
  have hAddB := Critical.beattyIndex_add_eq j b
  rw [hKIndex, hCarryB] at hAddB
  have hBk :
      Critical.beattyIndex k =
        Critical.beattyIndex i +
          Critical.beattyIndex a + Critical.beattyIndex b + 2 := by
    omega
  have hUpperI := Critical.beattyIndex_upper i
  have hAB := Nat.mul_le_mul hBoundA hBoundB
  have hAll := Nat.mul_le_mul hUpperI hAB
  have hBase :
      4 * 3 ^ k ≤
        9 * 2 ^
          (Critical.beattyIndex i +
            Critical.beattyIndex a + Critical.beattyIndex b + 1) := by
    calc
      4 * 3 ^ k =
          3 ^ i * ((2 * 3 ^ a) * (2 * 3 ^ b)) := by
        rw [← hKIndex']
        rw [pow_add, pow_add]
        ring
      _ ≤
          2 ^ (Critical.beattyIndex i + 1) *
            ((3 * 2 ^ Critical.beattyIndex a) *
              (3 * 2 ^ Critical.beattyIndex b)) := hAll
      _ =
          9 * 2 ^
            (Critical.beattyIndex i +
              Critical.beattyIndex a + Critical.beattyIndex b + 1) := by
        rw [show
          Critical.beattyIndex i +
              Critical.beattyIndex a + Critical.beattyIndex b + 1 =
            (Critical.beattyIndex i + 1) +
              Critical.beattyIndex a + Critical.beattyIndex b by omega]
        rw [pow_add, pow_add]
        ring
  have hTimesThree := Nat.mul_le_mul_left 3 hBase
  have hScaled :
      4 * 3 ^ (k + 1) ≤
        4 * 2 ^ (Critical.beattyIndex k + 2) := by
    calc
      4 * 3 ^ (k + 1) = 3 * (4 * 3 ^ k) := by
        rw [pow_succ]
        ring
      _ ≤
          3 *
            (9 * 2 ^
              (Critical.beattyIndex i +
                Critical.beattyIndex a + Critical.beattyIndex b + 1)) :=
        hTimesThree
      _ =
          27 * 2 ^
            (Critical.beattyIndex i +
              Critical.beattyIndex a + Critical.beattyIndex b + 1) := by ring
      _ ≤
          32 * 2 ^
            (Critical.beattyIndex i +
              Critical.beattyIndex a + Critical.beattyIndex b + 1) := by
        exact Nat.mul_le_mul_right _ (by norm_num : (27 : ℕ) ≤ 32)
      _ = 4 * 2 ^ (Critical.beattyIndex k + 2) := by
        rw [hBk]
        rw [show
          Critical.beattyIndex i + Critical.beattyIndex a +
                Critical.beattyIndex b + 2 + 2 =
            (Critical.beattyIndex i + Critical.beattyIndex a +
                Critical.beattyIndex b + 1) + 3 by omega]
        rw [pow_add]
        norm_num
        ring
  have hUpperNext :
      3 ^ (k + 1) ≤ 2 ^ (Critical.beattyIndex k + 2) := by
    omega
  have hBeattyLe :
      Critical.beattyIndex (k + 1) ≤ Critical.beattyIndex k + 1 := by
    apply Critical.beattyIndex_le_of_upper
    rw [show (Critical.beattyIndex k + 1) + 1 =
      Critical.beattyIndex k + 2 by omega]
    exact hUpperNext
  have hBeattyLt := Critical.beattyIndex_lt_succ k
  have hBeattyEq :
      Critical.beattyIndex (k + 1) = Critical.beattyIndex k + 1 := by
    omega
  unfold Critical.beattyCarry
  rw [Critical.beattyIndex_one, hBeattyEq]
  omega

/--
二つの defect `+1` next blocks の直後、一歩先 `k+1` の defect は exact に据え置き。

前 theorem の `beattyCarry k 1 = 0` を normalized Sturmian step に戻し、
future minimum `k` の exponent `e_k=1` と defect recurrence に入れる。
-/
theorem double_nextFutureMinimum_defect_succ_next_defect_eq
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hIJ : O.NextFutureMinimum i j)
    (hJK : O.NextFutureMinimum j k)
    (hRiseIJ :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1)
    (hRiseJK :
      infiniteSurvivorDefect O.exponent k =
        infiniteSurvivorDefect O.exponent j + 1) :
    infiniteSurvivorDefect O.exponent (k + 1) =
      infiniteSurvivorDefect O.exponent k := by
  have hCarry :=
    O.double_nextFutureMinimum_defect_succ_beattyCarry_one_eq_zero
      S hStart hIJ hJK hRiseIJ hRiseJK
  have hStep : survivorSturmianStep k = 0 := by
    rw [survivorSturmianStep_eq_beattyCarry_one, hCarry]
  have hMinK : O.FutureMinimumAt k := hJK.futureMinimumAt
  have heK : O.exponent k = 1 :=
    O.futureMinimum_exponent_eq_one_of_infiniteCoefficientSurvivor S hMinK
  have hRec := infiniteSurvivorDefect_succ S k
  rw [hStep, heK] at hRec
  omega

/--
二つの defect `+1` next blocks の後に取る次の future minimum `l` では、
defect は二つ目の終点 `k` より増えない。

`l=k+1` なら直前 theoremで equality。
`k+1<l` なら `k+1` は block `k→l` の proper internal point なので、
既存の proper-suffix defect monotonicity を使う。
-/
theorem double_nextFutureMinimum_defect_succ_nextFutureMinimum_defect_le
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k l : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hIJ : O.NextFutureMinimum i j)
    (hJK : O.NextFutureMinimum j k)
    (hKL : O.NextFutureMinimum k l)
    (hRiseIJ :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1)
    (hRiseJK :
      infiniteSurvivorDefect O.exponent k =
        infiniteSurvivorDefect O.exponent j + 1) :
    infiniteSurvivorDefect O.exponent l ≤
      infiniteSurvivorDefect O.exponent k := by
  have hFlat :=
    O.double_nextFutureMinimum_defect_succ_next_defect_eq
      S hStart hIJ hJK hRiseIJ hRiseJK
  have hkl : k < l := by
    exact hKL.1
  by_cases hl : l = k + 1
  · subst l
    exact Nat.le_of_eq hFlat
  · have hk1l : k + 1 < l := by
      omega
    have hInternal :=
      O.nextFutureMinimum_defect_le_internal
        S hKL (k := k + 1) (by omega) hk1l
    rw [hFlat] at hInternal
    exact hInternal

/--
隣接 future minimum defect の `+1,+1,+1` は不可能。

二回連続で `+1` した時点で、次の future minimum の defect は増えないため。
-/
theorem no_three_consecutive_nextFutureMinimum_defect_rises
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k l : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hIJ : O.NextFutureMinimum i j)
    (hJK : O.NextFutureMinimum j k)
    (hKL : O.NextFutureMinimum k l)
    (hRiseIJ :
      infiniteSurvivorDefect O.exponent j =
        infiniteSurvivorDefect O.exponent i + 1)
    (hRiseJK :
      infiniteSurvivorDefect O.exponent k =
        infiniteSurvivorDefect O.exponent j + 1) :
    infiniteSurvivorDefect O.exponent l ≠
      infiniteSurvivorDefect O.exponent k + 1 := by
  have hLe :=
    O.double_nextFutureMinimum_defect_succ_nextFutureMinimum_defect_le
      S hStart hIJ hJK hKL hRiseIJ hRiseJK
  omega

/--
三本の隣接 future minimum transition がすべて `+1` になる conjunction 自体が false。
呼び出し側で contradiction として使いやすい wrapper。
-/
theorem not_three_consecutive_nextFutureMinimum_defect_rises
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j k l : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hIJ : O.NextFutureMinimum i j)
    (hJK : O.NextFutureMinimum j k)
    (hKL : O.NextFutureMinimum k l) :
    ¬ (
      infiniteSurvivorDefect O.exponent j =
          infiniteSurvivorDefect O.exponent i + 1 ∧
      infiniteSurvivorDefect O.exponent k =
          infiniteSurvivorDefect O.exponent j + 1 ∧
      infiniteSurvivorDefect O.exponent l =
          infiniteSurvivorDefect O.exponent k + 1) := by
  rintro ⟨hIJRise, hJKRise, hKLRise⟩
  exact
    (O.no_three_consecutive_nextFutureMinimum_defect_rises
      S hStart hIJ hJK hKL hIJRise hJKRise) hKLRise

end OddOrbit
end Collatz3
