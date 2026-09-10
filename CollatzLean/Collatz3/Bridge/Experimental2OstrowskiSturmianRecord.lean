import CollatzLean.Collatz3.Experimental2.OstrowskiCorridorArithmetic
import CollatzLean.Collatz3.Bridge.Experimental2ConvergentSturmianCompletion

/-!
# Collatz3 Bridge: sharp corridor / Ostrowski / Sturmian / Record 座標

`MechanicalConvergentCorridorSharp` で得た自然 range

* roof residual: `x < Pn`
* inverse residual: `k < Qn`

を `Critical.beattyIndex` / `beattyInverseHeight` に特殊化する。

さらに有限 corridor composition と Ostrowski 型 digit block を接続し、
最小非零 digit の endpoint orientation だけが scalar height の最終補正を決めることを示す。

lower endpoint を最後に持つ場合:

`H(Σ c_n Q_n) = Σ c_n P_n`

upper endpoint を最後に持つ場合:

`H(Σ c_n Q_n) = Σ c_n P_n + 1`

である。

最後に admissible profile / deterministic `initialRecordCuts` へ移し、
RecordFerrers の record cut の縦 Ostrowski 座標から横座標を exact に復元する。
-/

namespace Collatz3
open Experimental2
namespace Bridge

private theorem beattyIndex_mono_for_sharpCorridor :
    Monotone Critical.beattyIndex := by
  intro a b hab
  exact beattyIndex_mono_via_upper hab

/-- Beatty inverse の lower corridor を自然 range `k<Qn` へ強化した形。 -/
theorem beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hkPos : 0 < k)
    (hk : k < Qn) :
    beattyInverseHeight (Q + k) = P + beattyInverseHeight k := by
  simpa [beattyInverseHeight] using
    (IsLowerMechanicalRoof.inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_sharpCorridor
      B hkPos hk)

/-- Beatty inverse の upper corridor も positive residual 全幅 `k<Qn` で exact。 -/
theorem beattyInverseHeight_add_currentQ_eq_add_currentP_of_upperFarey_sharp
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hkPos : 0 < k)
    (hk : k < Qn) :
    beattyInverseHeight (Q + k) = P + beattyInverseHeight k := by
  simpa [beattyInverseHeight] using
    (IsLowerMechanicalRoof.inverse_add_currentQ_eq_add_currentP_of_upperFarey_sharp
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_sharpCorridor
      B hPLt hkPos hk)

/-- lower corridor は residual `0` も含め、自然 range 全体で一つの translation。 -/
theorem beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey_sharp_including_zero
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hk : k < Qn) :
    beattyInverseHeight (Q + k) = P + beattyInverseHeight k := by
  simpa [beattyInverseHeight] using
    (IsLowerMechanicalRoof.inverse_add_currentQ_eq_add_currentP_of_lowerFarey_sharp_including_zero
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_sharpCorridor
      B hPLt hk)

/-- upper corridor は residual `0` だけ `+1` endpoint correction を持つ。 -/
theorem beattyInverseHeight_add_currentQ_eq_of_upperFarey_sharp_piecewise
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hk : k < Qn) :
    beattyInverseHeight (Q + k) =
      if k = 0 then P + 1 else P + beattyInverseHeight k := by
  simpa [beattyInverseHeight] using
    (IsLowerMechanicalRoof.inverse_add_currentQ_eq_of_upperFarey_sharp_piecewise
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_sharpCorridor
      B hPLt hk)

/-- lower sharp corridor の `log₃2` ceiling 表示。 -/
theorem sturmianCeil_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hkPos : 0 < k)
    (hk : k < Qn) :
    ⌈((Q + k : ℕ) : ℝ) * Real.logb 3 2⌉₊ =
      P + ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
  calc
    ⌈((Q + k : ℕ) : ℝ) * Real.logb 3 2⌉₊ = beattyInverseHeight (Q + k) :=
      (beattyInverseHeight_eq_natCeil_mul_logb_three_two (Q + k)).symm
    _ = P + beattyInverseHeight k :=
      beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
        B hkPos hk
    _ = P + ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
      rw [beattyInverseHeight_eq_natCeil_mul_logb_three_two]

/-- upper sharp corridor の `log₃2` ceiling 表示。 -/
theorem sturmianCeil_add_currentQ_eq_add_currentP_of_upperFarey_sharp
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hkPos : 0 < k)
    (hk : k < Qn) :
    ⌈((Q + k : ℕ) : ℝ) * Real.logb 3 2⌉₊ =
      P + ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
  calc
    ⌈((Q + k : ℕ) : ℝ) * Real.logb 3 2⌉₊ = beattyInverseHeight (Q + k) :=
      (beattyInverseHeight_eq_natCeil_mul_logb_three_two (Q + k)).symm
    _ = P + beattyInverseHeight k :=
      beattyInverseHeight_add_currentQ_eq_add_currentP_of_upperFarey_sharp
        B hPLt hkPos hk
    _ = P + ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
      rw [beattyInverseHeight_eq_natCeil_mul_logb_three_two]

/--
Beatty inverse の一歩差分は `log₃2` ceiling mechanical word の差分そのもの。
-/
theorem beattyInverseBit_eq_ceilDiff_logb_three_two
    (k : ℕ) :
    beattyInverseHeight (k + 1) - beattyInverseHeight k =
      ⌈((k + 1 : ℕ) : ℝ) * Real.logb 3 2⌉₊ -
        ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
  rw [beattyInverseHeight_eq_natCeil_mul_logb_three_two,
    beattyInverseHeight_eq_natCeil_mul_logb_three_two]

/-- lower corridor 内部の Sturmian bit block は `k+1<Qn` 全域で exact に反復する。 -/
theorem beattyInverseStep_add_currentQ_eq_of_lowerFarey_sharp
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hkPos : 0 < k)
    (hk : k + 1 < Qn) :
    beattyInverseHeight (Q + k + 1) - beattyInverseHeight (Q + k) =
      beattyInverseHeight (k + 1) - beattyInverseHeight k := by
  simpa [beattyInverseHeight,
    IsLowerMechanicalRoof.inverseStep] using
    (IsLowerMechanicalRoof.inverseStep_add_currentQ_eq_inverseStep_of_lowerFarey_sharp
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_sharpCorridor
      B hkPos hk)

/-- upper corridor 内部も seam より後では同じ Sturmian bit block を反復する。 -/
theorem beattyInverseStep_add_currentQ_eq_of_upperFarey_sharp
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hkPos : 0 < k)
    (hk : k + 1 < Qn) :
    beattyInverseHeight (Q + k + 1) - beattyInverseHeight (Q + k) =
      beattyInverseHeight (k + 1) - beattyInverseHeight k := by
  simpa [beattyInverseHeight,
    IsLowerMechanicalRoof.inverseStep] using
    (IsLowerMechanicalRoof.inverseStep_add_currentQ_eq_inverseStep_of_upperFarey_sharp
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_sharpCorridor
      B hPLt hkPos hk)

/-- lower seam bit は自然条件 `1<Qn` だけで exact に `1`。 -/
theorem beattyInverseStep_currentQ_eq_one_of_lowerFarey_sharp
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hOneLt : 1 < Qn) :
    beattyInverseHeight (Q + 1) - beattyInverseHeight Q = 1 := by
  have hEnd := beattyInverseHeight_currentQ_eq_currentP_of_lowerFarey B hPLt
  have hNext := beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
    B (k := 1) (by omega) hOneLt
  have hOne : beattyInverseHeight 1 = 1 := by
    simp only [beattyInverseHeight, IsLowerMechanicalRoof.inverse_one]
  rw [hEnd, hNext, hOne]
  omega

/-- upper seam bit は自然条件 `1<Qn` だけで exact に `0`。 -/
theorem beattyInverseStep_currentQ_eq_zero_of_upperFarey_sharp
    {P Q Pn Qn : ℕ}
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hOneLt : 1 < Qn) :
    beattyInverseHeight (Q + 1) - beattyInverseHeight Q = 0 := by
  have hEnd := beattyInverseHeight_currentQ_eq_currentP_add_one_of_upperFarey B hPLt
  have hNext := beattyInverseHeight_add_currentQ_eq_add_currentP_of_upperFarey_sharp
    B hPLt (k := 1) (by omega) hOneLt
  have hOne : beattyInverseHeight 1 = 1 := by
    simp only [beattyInverseHeight, IsLowerMechanicalRoof.inverse_one]
  rw [hEnd, hNext, hOne]
  omega


/--
lower sharp corridor 内で prefix depth が `Q+k₀` なら、
first-passage roof 条件は自然 range `k₀<Qn` だけで residual inverse boundary へ還元される。
-/
theorem prefixBoundary_iff_residualInverse_of_lowerFarey_sharp
    (w : Word)
    {cut P Q Pn Qn k₀ : ℕ}
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hk₀Pos : 0 < k₀)
    (hk₀ : k₀ < Qn)
    (hDepth : Word.prefixTwoDepth w cut = Q + k₀) :
    Word.prefixTwoDepth w cut ≤ Critical.beattyIndex cut ↔
      P + beattyInverseHeight k₀ ≤ cut := by
  rw [prefixTwoDepth_le_beatty_iff_inverseBoundary]
  rw [hDepth]
  rw [beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
    B hk₀Pos hk₀]

/-- upper sharp corridor に対する同じ residual boundary reduction。 -/
theorem prefixBoundary_iff_residualInverse_of_upperFarey_sharp
    (w : Word)
    {cut P Q Pn Qn k₀ : ℕ}
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hk₀Pos : 0 < k₀)
    (hk₀ : k₀ < Qn)
    (hDepth : Word.prefixTwoDepth w cut = Q + k₀) :
    Word.prefixTwoDepth w cut ≤ Critical.beattyIndex cut ↔
      P + beattyInverseHeight k₀ ≤ cut := by
  rw [prefixTwoDepth_le_beatty_iff_inverseBoundary]
  rw [hDepth]
  rw [beattyInverseHeight_add_currentQ_eq_add_currentP_of_upperFarey_sharp
    B hPLt hk₀Pos hk₀]

/-- critical first-passage prefix の lower sharp residual bound。 -/
theorem criticalFirstPassage_prefix_residualBoundary_of_lowerFarey_sharp
    {w : Word}
    (F : Word.CriticalFirstPassage w)
    {cut P Q Pn Qn k₀ : ℕ}
    (hCut : cut < Word.oddSteps w)
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hk₀Pos : 0 < k₀)
    (hk₀ : k₀ < Qn)
    (hDepth : Word.prefixTwoDepth w cut = Q + k₀) :
    P + beattyInverseHeight k₀ ≤ cut := by
  exact
    (prefixBoundary_iff_residualInverse_of_lowerFarey_sharp
      w B hk₀Pos hk₀ hDepth).1
      (F.prefixDepth_le_beatty hCut)

/-- critical first-passage prefix の upper sharp residual bound。 -/
theorem criticalFirstPassage_prefix_residualBoundary_of_upperFarey_sharp
    {w : Word}
    (F : Word.CriticalFirstPassage w)
    {cut P Q Pn Qn k₀ : ℕ}
    (hCut : cut < Word.oddSteps w)
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hk₀Pos : 0 < k₀)
    (hk₀ : k₀ < Qn)
    (hDepth : Word.prefixTwoDepth w cut = Q + k₀) :
    P + beattyInverseHeight k₀ ≤ cut := by
  exact
    (prefixBoundary_iff_residualInverse_of_upperFarey_sharp
      w B hPLt hk₀Pos hk₀ hDepth).1
      (F.prefixDepth_le_beatty hCut)

/-! ## finite corridor chain を Beatty/Ostrowski 座標へ接続 -/

/-- lower sharp corridor を finite exact chain の head に追加する。 -/
theorem beattyExactInverseCorridorChain_cons_lower
    {xs : List (ℕ × ℕ)}
    {k P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hResidualPos : 0 < corridorQSum xs + k)
    (hResidualRange : corridorQSum xs + k < Qn)
    (C : ExactInverseCorridorChain beattyInverseHeight xs k) :
    ExactInverseCorridorChain beattyInverseHeight ((P, Q) :: xs) k := by
  apply exactInverseCorridorChain_cons
  · exact beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey_sharp
      B hResidualPos hResidualRange
  · exact C

/-- upper sharp corridor も positive residual なら finite chain の head に追加できる。 -/
theorem beattyExactInverseCorridorChain_cons_upper
    {xs : List (ℕ × ℕ)}
    {k P Q Pn Qn : ℕ}
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hResidualPos : 0 < corridorQSum xs + k)
    (hResidualRange : corridorQSum xs + k < Qn)
    (C : ExactInverseCorridorChain beattyInverseHeight xs k) :
    ExactInverseCorridorChain beattyInverseHeight ((P, Q) :: xs) k := by
  apply exactInverseCorridorChain_cons
  · exact beattyInverseHeight_add_currentQ_eq_add_currentP_of_upperFarey_sharp
      B hPLt hResidualPos hResidualRange
  · exact C

/--
最小非零 Ostrowski digit が lower convergent にある場合の exact scalar-height 公式。
-/
theorem beattyFiniteOstrowski_height_formula_lower
    (higher : List OstrowskiCorridorDigit)
    {P Q Pn Qn d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain beattyInverseHeight
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn) :
    beattyInverseHeight (ostrowskiQSum higher + d * Q) =
      ostrowskiPSum higher + d * P := by
  exact finiteOstrowskiCorridor_height_formula_lower
    (H := beattyInverseHeight) higher hd C
    (beattyInverseHeight_currentQ_eq_currentP_of_lowerFarey B hPLt)

/--
最小非零 Ostrowski digit が upper convergent にある場合は補正が exact に `+1`。
-/
theorem beattyFiniteOstrowski_height_formula_upper
    (higher : List OstrowskiCorridorDigit)
    {P Q Pn Qn d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain beattyInverseHeight
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn) :
    beattyInverseHeight (ostrowskiQSum higher + d * Q) =
      ostrowskiPSum higher + d * P + 1 := by
  exact finiteOstrowskiCorridor_height_formula_upper
    (H := beattyInverseHeight) higher hd C
    (beattyInverseHeight_currentQ_eq_currentP_add_one_of_upperFarey B hPLt)

/-- lower 最小 digit の公式を `ceil(N log₃2)` だけで書いた形。 -/
theorem sturmianFiniteOstrowski_ceiling_formula_lower
    (higher : List OstrowskiCorridorDigit)
    {P Q Pn Qn d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain beattyInverseHeight
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn) :
    ⌈((ostrowskiQSum higher + d * Q : ℕ) : ℝ) * Real.logb 3 2⌉₊ =
      ostrowskiPSum higher + d * P := by
  calc
    ⌈((ostrowskiQSum higher + d * Q : ℕ) : ℝ) * Real.logb 3 2⌉₊ =
        beattyInverseHeight (ostrowskiQSum higher + d * Q) :=
      (beattyInverseHeight_eq_natCeil_mul_logb_three_two _).symm
    _ = ostrowskiPSum higher + d * P :=
      beattyFiniteOstrowski_height_formula_lower higher hd C B hPLt

/-- upper 最小 digit の ceiling 公式。 -/
theorem sturmianFiniteOstrowski_ceiling_formula_upper
    (higher : List OstrowskiCorridorDigit)
    {P Q Pn Qn d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain beattyInverseHeight
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn) :
    ⌈((ostrowskiQSum higher + d * Q : ℕ) : ℝ) * Real.logb 3 2⌉₊ =
      ostrowskiPSum higher + d * P + 1 := by
  calc
    ⌈((ostrowskiQSum higher + d * Q : ℕ) : ℝ) * Real.logb 3 2⌉₊ =
        beattyInverseHeight (ostrowskiQSum higher + d * Q) :=
      (beattyInverseHeight_eq_natCeil_mul_logb_three_two _).symm
    _ = ostrowskiPSum higher + d * P + 1 :=
      beattyFiniteOstrowski_height_formula_upper higher hd C B hPLt

/-! ## admissible profile / RecordFerrers への exact 座標移送 -/

/--
admissible strict record cut の高さが lower-endpoint Ostrowski 住所なら、横座標は weighted `P` sum。
-/
theorem admissibleRecordCut_coordinate_eq_ostrowski_lower
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a : ℕ}
    (R : Ferrers.IsRecordCutAfter h Critical.initialRoofAnchor a)
    (higher : List OstrowskiCorridorDigit)
    {P Q Pn Qn d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain beattyInverseHeight
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hHeight : Critical.profileHeight h a = ostrowskiQSum higher + d * Q) :
    a = ostrowskiPSum higher + d * P := by
  have hContact := admissibleRecordCut_eq_exactInverseBoundary A R
  rw [hHeight] at hContact
  have hFormula := beattyFiniteOstrowski_height_formula_lower higher hd C B hPLt
  omega

/-- upper-endpoint Ostrowski 住所では record cut 横座標に exact `+1` が残る。 -/
theorem admissibleRecordCut_coordinate_eq_ostrowski_upper
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a : ℕ}
    (R : Ferrers.IsRecordCutAfter h Critical.initialRoofAnchor a)
    (higher : List OstrowskiCorridorDigit)
    {P Q Pn Qn d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain beattyInverseHeight
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hHeight : Critical.profileHeight h a = ostrowskiQSum higher + d * Q) :
    a = ostrowskiPSum higher + d * P + 1 := by
  have hContact := admissibleRecordCut_eq_exactInverseBoundary A R
  rw [hHeight] at hContact
  have hFormula := beattyFiniteOstrowski_height_formula_upper higher hd C B hPLt
  omega

/-- deterministic `initialRecordCuts` に対する lower Ostrowski 座標公式。 -/
theorem admissibleInitialRecordCut_coordinate_eq_ostrowski_lower
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a : ℕ}
    (ha : a ∈ Ferrers.initialRecordCuts h)
    (higher : List OstrowskiCorridorDigit)
    {P Q Pn Qn d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain beattyInverseHeight
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hHeight : Critical.profileHeight h a = ostrowskiQSum higher + d * Q) :
    a = ostrowskiPSum higher + d * P := by
  have hContact := admissibleInitialRecordCut_eq_exactInverseBoundary A ha
  rw [hHeight] at hContact
  have hFormula := beattyFiniteOstrowski_height_formula_lower higher hd C B hPLt
  omega

/-- deterministic `initialRecordCuts` に対する upper Ostrowski 座標公式。 -/
theorem admissibleInitialRecordCut_coordinate_eq_ostrowski_upper
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a : ℕ}
    (ha : a ∈ Ferrers.initialRecordCuts h)
    (higher : List OstrowskiCorridorDigit)
    {P Q Pn Qn d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain beattyInverseHeight
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hHeight : Critical.profileHeight h a = ostrowskiQSum higher + d * Q) :
    a = ostrowskiPSum higher + d * P + 1 := by
  have hContact := admissibleInitialRecordCut_eq_exactInverseBoundary A ha
  rw [hHeight] at hContact
  have hFormula := beattyFiniteOstrowski_height_formula_upper higher hd C B hPLt
  omega

/-- RecordFerrers 版 lower は admissible initial-record theorem の薄い wrapper。 -/
theorem recordFerrers_initialRecordCut_coordinate_eq_ostrowski_lower
    {m : ℕ}
    (RF : Ferrers.RecordFerrers m)
    {a : ℕ}
    (ha : a ∈ Ferrers.initialRecordCuts RF.profile.1)
    (higher : List OstrowskiCorridorDigit)
    {P Q Pn Qn d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain beattyInverseHeight
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (B : IsLowerFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hHeight : Critical.profileHeight RF.profile.1 a =
      ostrowskiQSum higher + d * Q) :
    a = ostrowskiPSum higher + d * P :=
  admissibleInitialRecordCut_coordinate_eq_ostrowski_lower
    RF.profile.2 ha higher hd C B hPLt hHeight

/-- RecordFerrers 版 upper も薄い wrapper。 -/
theorem recordFerrers_initialRecordCut_coordinate_eq_ostrowski_upper
    {m : ℕ}
    (RF : Ferrers.RecordFerrers m)
    {a : ℕ}
    (ha : a ∈ Ferrers.initialRecordCuts RF.profile.1)
    (higher : List OstrowskiCorridorDigit)
    {P Q Pn Qn d : ℕ}
    (hd : 0 < d)
    (C : ExactInverseCorridorChain beattyInverseHeight
      (expandOstrowskiCorridorDigits higher ++
        List.replicate (d - 1) (P, Q)) Q)
    (B : IsUpperFareyBracket (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn)
    (hHeight : Critical.profileHeight RF.profile.1 a =
      ostrowskiQSum higher + d * Q) :
    a = ostrowskiPSum higher + d * P + 1 :=
  admissibleInitialRecordCut_coordinate_eq_ostrowski_upper
    RF.profile.2 ha higher hd C B hPLt hHeight

end Bridge
end Collatz3
