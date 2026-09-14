import CollatzLean.Collatz3.Bridge.SurvivorAdjacentFutureMinimumSharpMinLength
import CollatzLean.Collatz3.Bridge.InfiniteSurvivorEscape
import CollatzLean.Collatz3.Bridge.CriticalMargin
import CollatzLean.Collatz3.Arithmetic.CriticalGap
import CollatzLean.Collatz3.Critical.BeattyCarry

/-!
# Collatz3 Bridge: contracting future-minimum block の tail rigidity と margin carry threshold

前段では contracting next-future-minimum block に対して、最短 contracting odd-prefix `p` を取り、

* `22 ≤ p ≤ r`,
* `B ≤ roofAffineBound(p)`,
* future-minimum gap は少なくとも `4`,

を得た。

このファイルでは、その sharp roof 算術で捨てていた actual start `x` を保持し、
さらに Beatty carry を `criticalMargin` で exact に読み直す。

第一部では、最短 contracting prefix に対して

`criticalGap(p) * x + 4 * 2^(criticalTwoDepth p) ≤ roofAffineBound(p)`

を証明する。ここから contracting block 長 `r` に対する粗いが一様な start 上界

`x ≤ r * 3^r`

を導き、infinite coefficient survivor の `+∞` 発散と衝突させることで

`∀ R, sufficiently far out, every contracting next-future-minimum block has length > R`

を得る。したがって positive excess、特に `(carry, excess) = (1,1)` の bounded lengths は
orbit tail から完全に消える。

第二部では

`μ(n) = criticalMargin(n)`

に対して Beatty addition を exact に移し、

`μ(a+b) = μ(a) + μ(b) + carry(a,b) - 1`

を証明する。`0 < μ ≤ 1` と `carry ∈ {0,1}` を合わせると

* `carry = 1 ↔ μ(a)+μ(b) ≤ 1`,
* `carry = 0 ↔ 1 < μ(a)+μ(b)`,

となる。これは `(1,1)` と `(0,0)` を同じ margin threshold の両側として読むための
基礎 API である。

新しい primitive orbit data は導入しない。
-/

namespace Collatz3
namespace OddOrbit

open Bridge

/--
最短 contracting odd-prefix `p` に対する start-sensitive sharp roof bound。

`C = criticalTwoDepth p`, `x = value i`, `d = value(i+p)-x` とする。
actual endpoint equation を

`B = (2^H - 3^p) * x + 2^H * d`

と書く。contracting から `C ≤ H`、next future minimum の値差から `4 ≤ d` なので、

`criticalGap(p) * x + 4 * 2^C ≤ B ≤ roofAffineBound(p)`

を得る。
-/
theorem firstContractingOddPrefix_startSensitive_roof_bound
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
    Arithmetic.criticalGap p * O.value i +
        4 * 2 ^ Critical.criticalTwoDepth p ≤
      CSTMicro.roofAffineBound p := by
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
  have hContract' : 3 ^ p < 2 ^ H := by
    simpa [H, w] using hContract
  have hgPos : 0 < g := by
    dsimp [g]
    exact Nat.sub_pos_of_lt hContract'
  have hTwoDecomp : 2 ^ H = 3 ^ p + g := by
    dsimp [g]
    exact (Nat.add_sub_of_le hContract'.le).symm
  have hIdentity : B = g * x + 2 ^ H * d := by
    have hCancel :
        3 ^ p * x + (g * x + 2 ^ H * d) =
          3 ^ p * x + B := by
      calc
        3 ^ p * x + (g * x + 2 ^ H * d)
            = (3 ^ p + g) * x + 2 ^ H * d := by ring
        _ = 2 ^ H * x + 2 ^ H * d := by rw [hTwoDecomp]
        _ = 2 ^ H * (x + d) := by ring
        _ = 2 ^ H * z := by rw [hzd]
        _ = 3 ^ p * x + B := hEq
    exact (Nat.add_left_cancel hCancel).symm
  have hFourNext : 4 ≤ O.value j - O.value i :=
    O.four_le_nextFutureMinimum_valueGap S hMin hNext
  have hNextLe : O.value j ≤ z := by
    dsimp [z]
    exact hNext.2 (i + p) (by omega)
  have hdFour : 4 ≤ d := by
    dsimp [d, z, x]
    omega
  have hHPos : 0 < H := by
    by_contra hNot
    have hH0 : H = 0 := by omega
    rw [hH0, pow_zero] at hContract'
    have hThreePos : 0 < 3 ^ p := Nat.pow_pos (by decide)
    omega
  have hUpper : 3 ^ p ≤ 2 ^ H := Nat.le_of_lt hContract'
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
  have hGapLe : Arithmetic.criticalGap p ≤ g := by
    have hPowLe :
        2 ^ (Critical.beattyIndex p + 1) ≤ 2 ^ H := by
      simpa [Critical.criticalTwoDepth] using hCriticalPow
    unfold Arithmetic.criticalGap
    dsimp [g]
    exact Nat.sub_le_sub_right hPowLe (3 ^ p)
  have hGapMul :
      Arithmetic.criticalGap p * x ≤ g * x :=
    Nat.mul_le_mul_right x hGapLe
  have hFourPow :
      4 * 2 ^ Critical.criticalTwoDepth p ≤ 2 ^ H * d := by
    calc
      4 * 2 ^ Critical.criticalTwoDepth p
          ≤ 4 * 2 ^ H := Nat.mul_le_mul_left 4 hCriticalPow
      _ = 2 ^ H * 4 := by ring
      _ ≤ 2 ^ H * d := Nat.mul_le_mul_left (2 ^ H) hdFour
  have hLower :
      Arithmetic.criticalGap p * x +
          4 * 2 ^ Critical.criticalTwoDepth p ≤ B := by
    rw [hIdentity]
    exact Nat.add_le_add hGapMul hFourPow
  have hRoof : B ≤ CSTMicro.roofAffineBound p := by
    simpa [B, w] using
      O.affineConst_firstContractingOddPrefix_le_roofAffineBound hPrefix
  simpa [x] using le_trans hLower hRoof

/--
contracting next-future-minimum block の start は block 長だけで粗く上から抑えられる。

最短 contracting prefix `p` について critical gap は正なので
`x ≤ criticalGap(p) * x ≤ roofAffineBound(p)`。
さらに `roofAffineBound(p) ≤ p * 3^(p-1)` と `p ≤ r` を使う。

この定理の目的は sharp な数値評価ではなく、固定長範囲に対して start を一様有界にすること。
-/
theorem start_le_length_mul_threePow_of_contracting_nextFutureMinimum
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hContract :
      3 ^ (j - i) <
        2 ^ Word.twoSteps (O.segmentWord i (j - i))) :
    O.value i ≤ (j - i) * 3 ^ (j - i) := by
  rcases O.exists_firstContractingOddPrefix
      (i := i) (r := j - i) hContract with
    ⟨p, hpPos, hpLe, hpContract, hpPrefix⟩
  have hSensitive :=
    O.firstContractingOddPrefix_startSensitive_roof_bound
      S hMin hNext hpPos hpContract hpPrefix
  have hGapPos : 0 < Arithmetic.criticalGap p :=
    Arithmetic.criticalGap_pos p
  have hGapOne : 1 ≤ Arithmetic.criticalGap p := by omega
  have hStartLeGap :
      O.value i ≤ Arithmetic.criticalGap p * O.value i := by
    calc
      O.value i = 1 * O.value i := by simp
      _ ≤ Arithmetic.criticalGap p * O.value i :=
        Nat.mul_le_mul_right (O.value i) hGapOne
  have hGapLeRoof :
      Arithmetic.criticalGap p * O.value i ≤
        CSTMicro.roofAffineBound p := by
    omega
  have hRoofCoarse :
      CSTMicro.roofAffineBound p ≤ p * 3 ^ (p - 1) :=
    CSTMicro.roofAffineBound_le_coarse p
  have hExp : p - 1 ≤ j - i := by omega
  have hPow : 3 ^ (p - 1) ≤ 3 ^ (j - i) :=
    Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) hExp
  have hCoarseToLength :
      p * 3 ^ (p - 1) ≤ (j - i) * 3 ^ (j - i) :=
    Nat.mul_le_mul hpLe hPow
  exact
    le_trans hStartLeGap
      (le_trans hGapLeRoof (le_trans hRoofCoarse hCoarseToLength))

/--
contracting block 長が `R` 以下なら、その future-minimum start は
`R * 3^R` 以下という一様上界を持つ。
-/
theorem start_le_bound_mul_threePow_of_contracting_length_le
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {i j R : ℕ}
    (hMin : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j)
    (hContract :
      3 ^ (j - i) <
        2 ^ Word.twoSteps (O.segmentWord i (j - i)))
    (hLength : j - i ≤ R) :
    O.value i ≤ R * 3 ^ R := by
  have hStart :=
    O.start_le_length_mul_threePow_of_contracting_nextFutureMinimum
      S hMin hNext hContract
  have hPow : 3 ^ (j - i) ≤ 3 ^ R :=
    Nat.pow_le_pow_right (by decide : 0 < (3 : ℕ)) hLength
  have hBound :
      (j - i) * 3 ^ (j - i) ≤ R * 3 ^ R :=
    Nat.mul_le_mul hLength hPow
  exact le_trans hStart hBound

/--
任意の有限長上限 `R` は、infinite coefficient survivor の sufficiently far tail では
contracting next-future-minimum block に現れない。

すなわち contracting block lengths は future-minimum tail に沿って一様に `+∞` へ逃げる。
-/
theorem exists_tail_contracting_nextFutureMinimum_length_gt
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (R : ℕ) :
    ∃ N : ℕ,
      ∀ {i j : ℕ},
        N ≤ i →
        O.FutureMinimumAt i →
        O.NextFutureMinimum i j →
        3 ^ (j - i) <
            2 ^ Word.twoSteps (O.segmentWord i (j - i)) →
        R < j - i := by
  have hDiverges := O.divergesToInfinity_of_infiniteCoefficientSurvivor S
  rcases hDiverges (R * 3 ^ R) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i j hi hMin hNext hContract
  by_contra hNot
  have hLength : j - i ≤ R := by omega
  have hStartBound :=
    O.start_le_bound_mul_threePow_of_contracting_length_le
      S hMin hNext hContract hLength
  have hEscape : R * 3 ^ R < O.value i := hN i hi
  omega

/-- positive Beatty excess の next-future-minimum block lengths も tail で一様に発散する。 -/
theorem exists_tail_positiveExcess_nextFutureMinimum_length_gt
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (R : ℕ) :
    ∃ N : ℕ,
      ∀ {i j : ℕ},
        N ≤ i →
        O.FutureMinimumAt i →
        O.NextFutureMinimum i j →
        0 < O.segmentBeattyExcess i (j - i) →
        R < j - i := by
  rcases O.exists_tail_contracting_nextFutureMinimum_length_gt S R with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i j hi hMin hNext hExcess
  have hContract :
      3 ^ (j - i) <
        2 ^ Word.twoSteps (O.segmentWord i (j - i)) :=
    (O.nextFutureMinimum_segmentBeattyExcess_pos_iff_threePow_lt_twoPow hNext).1
      hExcess
  exact hN hi hMin hNext hContract

/--
特に `(carry, excess) = (1,1)` block の bounded lengths は tail から完全に消える。
carry はこの結論自体には不要だが、三型分類から直接呼べる wrapper として残す。
-/
theorem exists_tail_one_one_nextFutureMinimum_length_gt
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    (R : ℕ) :
    ∃ N : ℕ,
      ∀ {i j : ℕ},
        N ≤ i →
        O.FutureMinimumAt i →
        O.NextFutureMinimum i j →
        (Critical.beattyCarry i (j - i) = 1 ∧
          O.segmentBeattyExcess i (j - i) = 1) →
        R < j - i := by
  rcases O.exists_tail_positiveExcess_nextFutureMinimum_length_gt S R with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro i j hi hMin hNext hOneOne
  have hExcess : 0 < O.segmentBeattyExcess i (j - i) := by
    rw [hOneOne.2]
    omega
  exact hN hi hMin hNext hExcess

end OddOrbit

namespace Bridge

/--
critical margin の Beatty-addition cocycle。

`beattyIndex(a+b) = beattyIndex(a)+beattyIndex(b)+carry(a,b)` を
`μ(n)=beattyIndex(n)+1-n log₂3` に代入した exact identity。
-/
theorem criticalMargin_add_eq
    (a b : ℕ) :
    criticalMargin (a + b) =
      criticalMargin a + criticalMargin b +
        (Critical.beattyCarry a b : ℝ) - 1 := by
  rw [
    criticalMargin_eq_beattyIndex_add_one_sub (a + b),
    criticalMargin_eq_beattyIndex_add_one_sub a,
    criticalMargin_eq_beattyIndex_add_one_sub b,
    Critical.beattyIndex_add_eq
  ]
  push_cast
  ring

/--
Beatty carry `1` は critical margins の和が `1` 以下であることと exact に同値。

carry `0` を仮定すると cocycle により endpoint margin が非正になり、
`criticalMargin_pos` と矛盾する。
-/
theorem beattyCarry_eq_one_iff_criticalMargin_add_le_one
    (a b : ℕ) :
    Critical.beattyCarry a b = 1 ↔
      criticalMargin a + criticalMargin b ≤ 1 := by
  constructor
  · intro hCarry
    have hCocycle := criticalMargin_add_eq a b
    rw [hCarry] at hCocycle
    norm_num at hCocycle
    have hUpper := criticalMargin_le_one (a + b)
    linarith
  · intro hSum
    rcases Critical.beattyCarry_eq_zero_or_one a b with hCarry | hCarry
    · have hCocycle := criticalMargin_add_eq a b
      rw [hCarry] at hCocycle
      norm_num at hCocycle
      have hPos := criticalMargin_pos (a + b)
      linarith
    · exact hCarry

/--
Beatty carry `0` は critical margins の和が `1` を strict に越えることと exact に同値。
-/
theorem beattyCarry_eq_zero_iff_one_lt_criticalMargin_add
    (a b : ℕ) :
    Critical.beattyCarry a b = 0 ↔
      1 < criticalMargin a + criticalMargin b := by
  constructor
  · intro hCarry
    have hCocycle := criticalMargin_add_eq a b
    rw [hCarry] at hCocycle
    norm_num at hCocycle
    have hPos := criticalMargin_pos (a + b)
    linarith
  · intro hSum
    rcases Critical.beattyCarry_eq_zero_or_one a b with hCarry | hCarry
    · exact hCarry
    · have hCocycle := criticalMargin_add_eq a b
      rw [hCarry] at hCocycle
      norm_num at hCocycle
      have hUpper := criticalMargin_le_one (a + b)
      linarith

/-- carry `1` の threshold を local length margin の形で書いた版。 -/
theorem beattyCarry_eq_one_iff_criticalMargin_le_threshold
    (a r : ℕ) :
    Critical.beattyCarry a r = 1 ↔
      criticalMargin r ≤ 1 - criticalMargin a := by
  rw [beattyCarry_eq_one_iff_criticalMargin_add_le_one]
  constructor <;> intro h <;> linarith

/-- carry `0` の threshold を local length margin の形で書いた版。 -/
theorem beattyCarry_eq_zero_iff_threshold_lt_criticalMargin
    (a r : ℕ) :
    Critical.beattyCarry a r = 0 ↔
      1 - criticalMargin a < criticalMargin r := by
  rw [beattyCarry_eq_zero_iff_one_lt_criticalMargin_add]
  constructor <;> intro h <;> linarith


end Bridge

namespace OddOrbit

open Bridge

/--
`(carry, excess) = (1,1)` block は critical-margin threshold の下側にある。

excess `1` は contracting flat 型を指定し、margin inequality 自体は carry `1` の
exact threshold から従う。
-/
theorem nextFutureMinimum_one_one_criticalMargin_le_threshold
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hOneOne :
      Critical.beattyCarry i (j - i) = 1 ∧
        O.segmentBeattyExcess i (j - i) = 1) :
    criticalMargin (j - i) ≤ 1 - criticalMargin i := by
  exact
    (beattyCarry_eq_one_iff_criticalMargin_le_threshold i (j - i)).1
      hOneOne.1

/--
`(carry, excess) = (0,0)` block は同じ critical-margin threshold の strict 上側にある。

したがって `(0,0)` と `(1,1)` は別々の primitive 型ではなく、
`criticalMargin (j-i)` と `1-criticalMargin i` の大小で分離される。
-/
theorem nextFutureMinimum_zero_zero_threshold_lt_criticalMargin
    (O : Collatz3.OddOrbit)
    {i j : ℕ}
    (hZeroZero :
      Critical.beattyCarry i (j - i) = 0 ∧
        O.segmentBeattyExcess i (j - i) = 0) :
    1 - criticalMargin i < criticalMargin (j - i) := by
  exact
    (beattyCarry_eq_zero_iff_threshold_lt_criticalMargin i (j - i)).1
      hZeroZero.1

end OddOrbit
end Collatz3
