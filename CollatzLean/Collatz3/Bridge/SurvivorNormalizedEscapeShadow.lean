import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscape
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Collatz3 Bridge: normalized escape limit から得られる exact shadow 軌道

`SurvivorNormalizedEscape` では actual odd-only orbit から

`R_m = 2^D_m * x_m / 3^m`

を作った。

このファイルでは任意の実数 `L` に対して、同じ exponent stream を使う homogeneous companion

`Y_m(L) = L * 3^m / 2^D_m`

と、その actual orbit との差

`Z_m(L) = x_m - Y_m(L)`

だけを導入する。

新しい orbit structure は作らない。二つとも既存 actual orbit から読む実数値である。

中心となる exact identity は

`2^(e_m) Z_(m+1) = 3 Z_m + 1`

である。したがって normalized escape limit `L` が存在する場合、actual orbit と
同じ exponent stream / affine translation を持つ実数 shadow が自動的に得られる。

また有限 segment `w = segmentWord a r` についても

`2^(twoSteps w) Z_(a+r) = 3^r Z_a + affineConst(w)`

が exact に成立する。

ここでは `L` が存在する条件は仮定しない。A 型からの存在は
`CSTConditional/ANormalizedEscapeShadow` で接続する。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open Filter

/--
normalized escape の候補極限 `L` から作る homogeneous companion value。

`Y_m(L) = L * 3^m / 2^D_m`。
-/
noncomputable def normalizedEscapeCompanionValue
    (O : Collatz3.OddOrbit)
    (L : ℝ)
    (m : ℕ) : ℝ :=
  L * (3 : ℝ) ^ m /
    (2 : ℝ) ^ infinitePrefixDepth O.exponent m

/--
actual value と homogeneous companion の差。

`Z_m(L) = x_m - Y_m(L)`。

limit `L` を使う場合には `Z_m(L) < 0` となる。
-/
noncomputable def normalizedEscapeShadowValue
    (O : Collatz3.OddOrbit)
    (L : ℝ)
    (m : ℕ) : ℝ :=
  (O.value m : ℝ) - O.normalizedEscapeCompanionValue L m

/-- companion を normalized escape 座標へ戻すと常に exactly `L`。 -/
theorem normalizedEscapeCompanionValue_normalizes_to
    (O : Collatz3.OddOrbit)
    (L : ℝ)
    (m : ℕ) :
    ((2 : ℝ) ^ infinitePrefixDepth O.exponent m *
        O.normalizedEscapeCompanionValue L m) /
      (3 : ℝ) ^ m = L := by
  unfold normalizedEscapeCompanionValue
  field_simp

/--
homogeneous companion の一歩 recurrence。

`2^(e_m) Y_(m+1) = 3 Y_m`。
-/
theorem normalizedEscapeCompanionValue_succ
    (O : Collatz3.OddOrbit)
    (L : ℝ)
    (m : ℕ) :
    (2 : ℝ) ^ O.exponent m *
        O.normalizedEscapeCompanionValue L (m + 1) =
      3 * O.normalizedEscapeCompanionValue L m := by
  unfold normalizedEscapeCompanionValue
  rw [infinitePrefixDepth_succ, pow_add, pow_succ]
  field_simp
  ring

/--
任意有限 segment 上の homogeneous companion equation。

`H = twoSteps(segmentWord a r)` とすると

`2^H Y_(a+r) = 3^r Y_a`。
-/
theorem normalizedEscapeCompanionValue_segment
    (O : Collatz3.OddOrbit)
    (L : ℝ)
    (a r : ℕ) :
    (2 : ℝ) ^ Word.twoSteps (O.segmentWord a r) *
        O.normalizedEscapeCompanionValue L (a + r) =
      (3 : ℝ) ^ r * O.normalizedEscapeCompanionValue L a := by
  unfold normalizedEscapeCompanionValue
  rw [O.infinitePrefixDepth_add_eq a r]
  simp only [pow_add]
  field_simp

/--
shadow は actual orbit と同じ `+1` affine recurrence を満たす。

`2^(e_m) Z_(m+1) = 3 Z_m + 1`。
-/
theorem normalizedEscapeShadowValue_succ
    (O : Collatz3.OddOrbit)
    (L : ℝ)
    (m : ℕ) :
    (2 : ℝ) ^ O.exponent m *
        O.normalizedEscapeShadowValue L (m + 1) =
      3 * O.normalizedEscapeShadowValue L m + 1 := by
  have hStepNat := (O.step m).equation
  have hStep :
      (2 : ℝ) ^ O.exponent m * (O.value (m + 1) : ℝ) =
        3 * (O.value m : ℝ) + 1 := by
    exact_mod_cast hStepNat
  have hHom := O.normalizedEscapeCompanionValue_succ L m
  unfold normalizedEscapeShadowValue
  calc
    (2 : ℝ) ^ O.exponent m *
        ((O.value (m + 1) : ℝ) -
          O.normalizedEscapeCompanionValue L (m + 1))
        =
      (2 : ℝ) ^ O.exponent m * (O.value (m + 1) : ℝ) -
        (2 : ℝ) ^ O.exponent m *
          O.normalizedEscapeCompanionValue L (m + 1) := by ring
    _ = (3 * (O.value m : ℝ) + 1) -
          3 * O.normalizedEscapeCompanionValue L m := by
            rw [hStep, hHom]
    _ = 3 *
          ((O.value m : ℝ) - O.normalizedEscapeCompanionValue L m) + 1 := by
            ring

/--
正の gap `-Z_m` で読んだ一歩 recurrence。

`2^(e_m) (-Z_(m+1)) = 3(-Z_m) - 1`。
-/
theorem normalizedEscapeShadowGap_succ
    (O : Collatz3.OddOrbit)
    (L : ℝ)
    (m : ℕ) :
    (2 : ℝ) ^ O.exponent m *
        (-O.normalizedEscapeShadowValue L (m + 1)) =
      3 * (-O.normalizedEscapeShadowValue L m) - 1 := by
  have h := O.normalizedEscapeShadowValue_succ L m
  linarith

/--
shadow は任意有限 segment 上でも actual orbit と同じ affine translation を持つ。

`w = segmentWord a r`, `H = twoSteps w` とすると

`2^H Z_(a+r) = 3^r Z_a + affineConst(w)`。
-/
theorem normalizedEscapeShadowValue_segment
    (O : Collatz3.OddOrbit)
    (L : ℝ)
    (a r : ℕ) :
    (2 : ℝ) ^ Word.twoSteps (O.segmentWord a r) *
        O.normalizedEscapeShadowValue L (a + r) =
      (3 : ℝ) ^ r * O.normalizedEscapeShadowValue L a +
        (Word.affineConst (O.segmentWord a r) : ℝ) := by
  have hRun := O.runsSegment a r
  have hEndpoint :
      (O.segmentWord a r).EndpointEquation
        (O.value a) (O.value (a + r)) := by
    simpa using hRun.endpointEquation
  have hEqNat :=
    (Word.endpointEquation_iff
      (O.segmentWord a r) (O.value a) (O.value (a + r))).1 hEndpoint
  have hOdd := O.segmentWord_oddSteps a r
  rw [hOdd] at hEqNat
  have hEq :
      (2 : ℝ) ^ Word.twoSteps (O.segmentWord a r) *
          (O.value (a + r) : ℝ) =
        (3 : ℝ) ^ r * (O.value a : ℝ) +
          (Word.affineConst (O.segmentWord a r) : ℝ) := by
    exact_mod_cast hEqNat
  have hHom := O.normalizedEscapeCompanionValue_segment L a r
  unfold normalizedEscapeShadowValue
  calc
    (2 : ℝ) ^ Word.twoSteps (O.segmentWord a r) *
        ((O.value (a + r) : ℝ) -
          O.normalizedEscapeCompanionValue L (a + r))
        =
      (2 : ℝ) ^ Word.twoSteps (O.segmentWord a r) *
          (O.value (a + r) : ℝ) -
        (2 : ℝ) ^ Word.twoSteps (O.segmentWord a r) *
          O.normalizedEscapeCompanionValue L (a + r) := by ring
    _ =
      ((3 : ℝ) ^ r * (O.value a : ℝ) +
          (Word.affineConst (O.segmentWord a r) : ℝ)) -
        (3 : ℝ) ^ r * O.normalizedEscapeCompanionValue L a := by
          rw [hEq, hHom]
    _ =
      (3 : ℝ) ^ r *
          ((O.value a : ℝ) - O.normalizedEscapeCompanionValue L a) +
        (Word.affineConst (O.segmentWord a r) : ℝ) := by
          ring

/--
shadow gap `-Z` で読んだ有限 segment affine equation。

`2^H (-Z_end) = 3^r (-Z_start) - affineConst(w)`。
-/
theorem normalizedEscapeShadowGap_segment
    (O : Collatz3.OddOrbit)
    (L : ℝ)
    (a r : ℕ) :
    (2 : ℝ) ^ Word.twoSteps (O.segmentWord a r) *
        (-O.normalizedEscapeShadowValue L (a + r)) =
      (3 : ℝ) ^ r * (-O.normalizedEscapeShadowValue L a) -
        (Word.affineConst (O.segmentWord a r) : ℝ) := by
  have h := O.normalizedEscapeShadowValue_segment L a r
  linarith

/--
shadow gap と normalized escape の limit gap は exact に同じ量を異なる scale で見たもの。

`-Z_m = (L - R_m) * 3^m / 2^D_m`。
-/
theorem neg_normalizedEscapeShadowValue_eq_limitGap_scaled
    (O : Collatz3.OddOrbit)
    (L : ℝ)
    (m : ℕ) :
    -O.normalizedEscapeShadowValue L m =
      (L - O.normalizedEscapeCoordinate m) * (3 : ℝ) ^ m /
        (2 : ℝ) ^ infinitePrefixDepth O.exponent m := by
  unfold normalizedEscapeShadowValue normalizedEscapeCompanionValue
    normalizedEscapeCoordinate
  field_simp
  ring

/--
`R_m -> L` なら strict monotonicity により各有限段階で `R_m < L`。

単なる `R_m ≤ L` より強く、shadow の符号を決めるために使う。
-/
theorem normalizedEscapeCoordinate_lt_limit_of_tendsto
    (O : Collatz3.OddOrbit)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L))
    (m : ℕ) :
    O.normalizedEscapeCoordinate m < L := by
  have hNextLe : O.normalizedEscapeCoordinate (m + 1) ≤ L :=
    O.normalizedEscapeCoordinate_monotone.ge_of_tendsto hT (m + 1)
  have hRise :
      O.normalizedEscapeCoordinate m <
        O.normalizedEscapeCoordinate (m + 1) :=
    O.normalizedEscapeCoordinate_strictMono (by omega)
  exact lt_of_lt_of_le hRise hNextLe

/--
`R_m -> L` なら actual value は homogeneous companion より strict に小さい。

`x_m < L * 3^m / 2^D_m`。
-/
theorem value_lt_normalizedEscapeCompanionValue_of_tendsto
    (O : Collatz3.OddOrbit)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L))
    (m : ℕ) :
    (O.value m : ℝ) < O.normalizedEscapeCompanionValue L m := by
  have hR := O.normalizedEscapeCoordinate_lt_limit_of_tendsto hT m
  unfold normalizedEscapeCoordinate at hR
  unfold normalizedEscapeCompanionValue
  have hTwo :
      (0 : ℝ) < (2 : ℝ) ^ infinitePrefixDepth O.exponent m := by
    positivity
  have hThree : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  apply (lt_div_iff₀ hTwo).2
  have hR' := (div_lt_iff₀ hThree).1 hR
  simpa [mul_comm] using hR'

/--
normalized escape limit から作る shadow は全段階で strict に負。
-/
theorem normalizedEscapeShadowValue_neg_of_tendsto
    (O : Collatz3.OddOrbit)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L))
    (m : ℕ) :
    O.normalizedEscapeShadowValue L m < 0 := by
  unfold normalizedEscapeShadowValue
  have h := O.value_lt_normalizedEscapeCompanionValue_of_tendsto hT m
  linarith

/--
従って shadow gap `-Z_m` は全段階で strict に正。
-/
theorem normalizedEscapeShadowGap_pos_of_tendsto
    (O : Collatz3.OddOrbit)
    {L : ℝ}
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L))
    (m : ℕ) :
    0 < -O.normalizedEscapeShadowValue L m := by
  exact neg_pos.mpr (O.normalizedEscapeShadowValue_neg_of_tendsto hT m)

/--
`L != 0` なら actual / companion 比は normalized escape 比そのもの。

`x_m / Y_m(L) = R_m / L`。
-/
theorem value_div_normalizedEscapeCompanionValue_eq_coordinate_div
    (O : Collatz3.OddOrbit)
    {L : ℝ}
    (hL : L ≠ 0)
    (m : ℕ) :
    (O.value m : ℝ) / O.normalizedEscapeCompanionValue L m =
      O.normalizedEscapeCoordinate m / L := by
  unfold normalizedEscapeCompanionValue normalizedEscapeCoordinate
  field_simp [hL]

/--
`L>0` かつ `R_m -> L` なら actual value と homogeneous companion の比は `1` へ収束する。

従って shadow は絶対値としては非零でも、companion に対する相対誤差は消える。
-/
theorem value_div_normalizedEscapeCompanionValue_tendsto_one
    (O : Collatz3.OddOrbit)
    {L : ℝ}
    (hL : 0 < L)
    (hT : Tendsto O.normalizedEscapeCoordinate atTop (nhds L)) :
    Tendsto
      (fun m : ℕ =>
        (O.value m : ℝ) / O.normalizedEscapeCompanionValue L m)
      atTop
      (nhds 1) := by
  have hRatio :
      Tendsto (fun m : ℕ => O.normalizedEscapeCoordinate m / L)
        atTop (nhds 1) := by
    have h := hT.div_const L
    simpa [hL.ne'] using h
  have hFun :
      (fun m : ℕ =>
        (O.value m : ℝ) / O.normalizedEscapeCompanionValue L m) =
      (fun m : ℕ => O.normalizedEscapeCoordinate m / L) := by
    funext m
    exact O.value_div_normalizedEscapeCompanionValue_eq_coordinate_div hL.ne' m
  rw [hFun]
  exact hRatio

end OddOrbit
end Collatz3
