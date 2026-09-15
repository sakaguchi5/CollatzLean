import CollatzLean.Collatz3.CSTConditional.ACStructure
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscapeShadow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Collatz3 CSTConditional: A/C future-minimum block 上の normalized escape shadow

`SurvivorNormalizedEscapeShadow` の finite-segment affine equation を、Global CST 下の
next-future-minimum block に特殊化する。

Global CST により block 長 `r = j-i` の total two-depth は exact に

`beattyIndex r`

となる。従って shadow gap `S_m = -Z_m` は

`S_i = affineConst(block) / 3^r
       + (2^(beattyIndex r) / 3^r) * S_j`

という positive affine cocycle を満たす。

さらに `2^(beattyIndex r) < 3^r` なので係数は strict に `(0,1)` に入る。

ここでは A/C symbol を新しく定義しない。既存 next-future-minimum exact depth と
shadow の一般 segment theorem を合成するだけである。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional
open Filter

/--
Global CST 下の next-future-minimum block では shadow の total two-depth を
`beattyIndex (j-i)` に exact に置き換えられる。
-/
theorem nextFutureMinimum_normalizedEscapeShadowValue_eq_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (L : ℝ)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    (2 : ℝ) ^ Critical.beattyIndex (j - i) *
        O.normalizedEscapeShadowValue L j =
      (3 : ℝ) ^ (j - i) * O.normalizedEscapeShadowValue L i +
        (Word.affineConst (O.segmentWord i (j - i)) : ℝ) := by
  have hShadow :=
    O.normalizedEscapeShadowValue_segment L i (j - i)
  have hDepth :=
    O.nextFutureMinimum_segmentTwoSteps_eq_beattyIndex_of_globalCST
      G hStart hNext
  have hij : i < j := hNext.1
  have hIndex : i + (j - i) = j := by
    omega
  rw [hDepth, hIndex] at hShadow
  exact hShadow

/--
shadow gap `S=-Z` を affine recurrence として解いた形。

`r=j-i`, `B=affineConst(block)` とすると

`S_i = B/3^r + (2^(beattyIndex r)/3^r) S_j`。
-/
theorem nextFutureMinimum_normalizedEscapeShadowGap_affine_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    (L : ℝ)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    -O.normalizedEscapeShadowValue L i =
      (Word.affineConst (O.segmentWord i (j - i)) : ℝ) /
          (3 : ℝ) ^ (j - i) +
        ((2 : ℝ) ^ Critical.beattyIndex (j - i) /
            (3 : ℝ) ^ (j - i)) *
          (-O.normalizedEscapeShadowValue L j) := by
  have h :=
    O.nextFutureMinimum_normalizedEscapeShadowValue_eq_of_globalCST
      G L hStart hNext
  have hThree : (0 : ℝ) < (3 : ℝ) ^ (j - i) := by
    positivity
  field_simp [ne_of_gt hThree]
  linarith

/--
next-future-minimum shadow cocycle の linear coefficient は strict に `(0,1)`。

Global CST 下の whole block が coefficient-expanding、すなわち
`2^H < 3^r` であることの実数版。
-/
theorem nextFutureMinimum_shadowContractionCoefficient_mem_Ioo_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    0 <
        (2 : ℝ) ^ Critical.beattyIndex (j - i) /
          (3 : ℝ) ^ (j - i) ∧
      (2 : ℝ) ^ Critical.beattyIndex (j - i) /
          (3 : ℝ) ^ (j - i) < 1 := by
  have hDepth :=
    O.nextFutureMinimum_segmentTwoSteps_eq_beattyIndex_of_globalCST
      G hStart hNext
  have hPowNat :=
    O.nextFutureMinimum_twoPow_lt_threePow_of_globalCST
      G hStart hNext
  rw [hDepth] at hPowNat
  have hPow :
      (2 : ℝ) ^ Critical.beattyIndex (j - i) <
        (3 : ℝ) ^ (j - i) := by
    exact_mod_cast hPowNat
  constructor
  · positivity
  · exact (div_lt_one (by positivity : (0 : ℝ) < (3 : ℝ) ^ (j - i))).2 hPow

/--
`R_m -> L` も仮定すると、同じ next-future-minimum block 上で両端の shadow gap は正で、
affine coefficient は strict contraction になる。

A 型 limit と A/C block geometry の直接の接点。
-/
theorem nextFutureMinimum_positiveShadowGap_affine_of_globalCST
    (O : Collatz3.OddOrbit)
    (G : GlobalCST)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L))
    {i j : ℕ}
    (hStart : O.FutureMinimumAt i)
    (hNext : O.NextFutureMinimum i j) :
    0 < -O.normalizedEscapeShadowValue L i ∧
      0 < -O.normalizedEscapeShadowValue L j ∧
      (-O.normalizedEscapeShadowValue L i =
        (Word.affineConst (O.segmentWord i (j - i)) : ℝ) /
            (3 : ℝ) ^ (j - i) +
          ((2 : ℝ) ^ Critical.beattyIndex (j - i) /
              (3 : ℝ) ^ (j - i)) *
            (-O.normalizedEscapeShadowValue L j)) ∧
      0 <
        (2 : ℝ) ^ Critical.beattyIndex (j - i) /
          (3 : ℝ) ^ (j - i) ∧
      (2 : ℝ) ^ Critical.beattyIndex (j - i) /
          (3 : ℝ) ^ (j - i) < 1 := by
  have hi := O.normalizedEscapeShadowGap_pos_of_tendsto hT i
  have hj := O.normalizedEscapeShadowGap_pos_of_tendsto hT j
  have hAffine :=
    O.nextFutureMinimum_normalizedEscapeShadowGap_affine_of_globalCST
      G L hStart hNext
  have hCoeff :=
    O.nextFutureMinimum_shadowContractionCoefficient_mem_Ioo_of_globalCST
      G hStart hNext
  exact ⟨hi, hj, hAffine, hCoeff.1, hCoeff.2⟩

end OddOrbit
end Collatz3
