import CollatzLean.Collatz3.CSTConditional.ANormalizedEscape
import CollatzLean.Collatz3.Bridge.SurvivorNormalizedEscapeShadow

/-!
# Collatz3 CSTConditional: A 型 normalized escape limit と exact shadow

`ANormalizedEscape` では `LinearDefectLowerBound` から有限正の実数極限

`R_m -> L`

を得た。

このファイルではその `L` を `SurvivorNormalizedEscapeShadow` の一般定理へ渡すだけで、
新しい A 型の primitive notion は導入しない。

得られる shadow

`Z_m = x_m - L * 3^m / 2^D_m`

は

* 全段階で `Z_m < 0`,
* actual orbit と同じ exponent stream を使い、
* `2^(e_m) Z_(m+1) = 3 Z_m + 1`,
* actual / homogeneous companion 比は `1` へ収束

を同時に満たす。

従って A 型候補には、正整数 actual orbit と同じ affine itinerary を共有する
negative real shadow が canonical に付随する。
-/

namespace Collatz3
namespace OddOrbit

open Bridge
open CSTConditional
open Filter

/--
linear defect survivor に付随する real escape limit と negative shadow を一つにまとめた derived package。

primitive data を増やさず、既存の limit existence と shadow identities を単に束ねる。
-/
theorem exists_negativeNormalizedEscapeShadow_of_linearDefect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N) :
    ∃ L : ℝ,
      0 < L ∧
      (O.value 0 : ℝ) < L ∧
      Tendsto O.normalizedEscapeCoordinate atTop (nhds L) ∧
      (∀ m : ℕ, O.normalizedEscapeCoordinate m < L) ∧
      (∀ m : ℕ, O.normalizedEscapeShadowValue L m < 0) ∧
      (∀ m : ℕ,
        (2 : ℝ) ^ O.exponent m *
            O.normalizedEscapeShadowValue L (m + 1) =
          3 * O.normalizedEscapeShadowValue L m + 1) ∧
      Tendsto
        (fun m : ℕ =>
          (O.value m : ℝ) / O.normalizedEscapeCompanionValue L m)
        atTop
        (nhds 1) := by
  rcases O.exists_normalizedEscapeLimit_of_linearDefect S hLinear with
    ⟨L, hL, hT, _hUpper⟩
  have hStart := O.normalizedEscapeLimit_start_lt hT
  refine ⟨L, hL, hStart, hT, ?_, ?_, ?_, ?_⟩
  · intro m
    exact O.normalizedEscapeCoordinate_lt_limit_of_tendsto hT m
  · intro m
    exact O.normalizedEscapeShadowValue_neg_of_tendsto hT m
  · intro m
    exact O.normalizedEscapeShadowValue_succ L m
  · exact O.value_div_normalizedEscapeCompanionValue_tendsto_one hL hT

/--
同じ package を正の gap `S_m = -Z_m` で読む。

`S_m > 0` かつ

`2^(e_m) S_(m+1) = 3 S_m - 1`。
-/
theorem exists_positiveNormalizedEscapeShadowGap_of_linearDefect
    (O : Collatz3.OddOrbit)
    (S : O.IsInfiniteCoefficientSurvivor)
    {K N : ℕ}
    (hLinear : O.LinearDefectLowerBound K N) :
    ∃ L : ℝ,
      0 < L ∧
      Tendsto O.normalizedEscapeCoordinate atTop (nhds L) ∧
      (∀ m : ℕ, 0 < -O.normalizedEscapeShadowValue L m) ∧
      (∀ m : ℕ,
        (2 : ℝ) ^ O.exponent m *
            (-O.normalizedEscapeShadowValue L (m + 1)) =
          3 * (-O.normalizedEscapeShadowValue L m) - 1) := by
  rcases O.exists_normalizedEscapeLimit_of_linearDefect S hLinear with
    ⟨L, hL, hT, _hUpper⟩
  refine ⟨L, hL, hT, ?_, ?_⟩
  · intro m
    exact O.normalizedEscapeShadowGap_pos_of_tendsto hT m
  · intro m
    exact O.normalizedEscapeShadowGap_succ L m

end OddOrbit
end Collatz3
