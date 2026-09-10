import CollatzLean.Collatz3.Experimental2.MechanicalInverseCorridorEndpoint
import CollatzLean.Collatz3.Bridge.Experimental2ConvergentSturmian

/-!
# Collatz3 Bridge: convergent/Sturmian/Record bridge の endpoint 完成と profile 一般化

`Experimental2ConvergentSturmian` に残っていた二点を閉じる。

1. residual `k₀ = 0` の corridor endpoint を lower / upper orientation ごとに exact に記述する。
2. inverse-boundary / record-cut theorem を `RecordFerrers` より下の
   `Profile` / `Admissible` 層へ降ろす。

lower endpoint は

`beattyInverseHeight Q = P`

upper endpoint は

`beattyInverseHeight Q = P + 1`

であり、upper 側の一段差は current roof endpoint が `Q-1` にあることに対応する。

また proper profile cut の inverse-boundary bound は carry law を使わず、
strict record cut の exact contact も `Admissible + IsRecordCutAfter` だけで成立する。
従って今後の continued-fraction 階層分解は full `RecordFerrers` を仮定せずに進められる。
-/

namespace Collatz3
open Experimental2
namespace Bridge

private theorem beattyIndex_mono_for_inverseCorridor :
    Monotone Critical.beattyIndex := by
  intro a b hab
  exact beattyIndex_mono_via_upper hab

/-- lower convergent corridor の `k₀ = 0` endpoint。 -/
theorem beattyInverseHeight_currentQ_eq_currentP_of_lowerFarey
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn) :
    beattyInverseHeight Q = P := by
  simpa [beattyInverseHeight] using
    (IsLowerMechanicalRoof.inverse_currentQ_eq_currentP_of_lowerFarey
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three B hPLt)

/-- upper convergent corridor の `k₀ = 0` endpoint。 -/
theorem beattyInverseHeight_currentQ_eq_currentP_add_one_of_upperFarey
    {P Q Pn Qn : ℕ}
    (B : IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hPLt : P < Pn) :
    beattyInverseHeight Q = P + 1 := by
  simpa [beattyInverseHeight] using
    (IsLowerMechanicalRoof.inverse_currentQ_eq_currentP_add_one_of_upperFarey
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_inverseCorridor B hPLt)

/--
lower corridor の inverse translation は `k = 0` を含めて一つの式になる。
-/
theorem beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey_including_zero
    {P Q Pn Qn k : ℕ}
    (B : IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hRange : P + beattyInverseHeight k < Pn) :
    beattyInverseHeight (Q + k) = P + beattyInverseHeight k := by
  simpa [beattyInverseHeight] using
    (IsLowerMechanicalRoof.inverse_add_currentQ_eq_add_currentP_of_lowerFarey_including_zero
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_inverseCorridor B hRange)

/--
upper corridor は seam だけ一段補正を持つ。

`k=0` では `P+1`、`k>0` では `P+beattyInverseHeight(k)`。
-/
theorem beattyInverseHeight_add_currentQ_eq_of_upperFarey_piecewise
    {P Q Pn Qn k : ℕ}
    (B : IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hRange : P + beattyInverseHeight k < Pn) :
    beattyInverseHeight (Q + k) =
      if k = 0 then P + 1 else P + beattyInverseHeight k := by
  simpa [beattyInverseHeight] using
    (IsLowerMechanicalRoof.inverse_add_currentQ_eq_of_upperFarey_piecewise
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_inverseCorridor B hRange)

/-- lower corridor の Sturmian seam bit は exact に `1`。 -/
theorem beattyInverseStep_currentQ_eq_one_of_lowerFarey
    {P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hRange : P + 1 < Pn) :
    beattyInverseHeight (Q + 1) - beattyInverseHeight Q = 1 := by
  simpa [beattyInverseHeight,
    IsLowerMechanicalRoof.inverseStep] using
    (IsLowerMechanicalRoof.inverseStep_currentQ_eq_one_of_lowerFarey
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_inverseCorridor B hRange)

/-- upper corridor の seam bit は exact に `0`。 -/
theorem beattyInverseStep_currentQ_eq_zero_of_upperFarey
    {P Q Pn Qn : ℕ}
    (B : IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hRange : P + 1 < Pn) :
    beattyInverseHeight (Q + 1) - beattyInverseHeight Q = 0 := by
  simpa [beattyInverseHeight,
    IsLowerMechanicalRoof.inverseStep] using
    (IsLowerMechanicalRoof.inverseStep_currentQ_eq_zero_of_upperFarey
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      beattyIndex_mono_for_inverseCorridor B hRange)

/--
residual `k₀=0` の lower first-passage boundary。

prefix two-depth が current numerator `Q` に一致するなら、roof 条件は exact に
`P ≤ cut` へ還元される。
-/
theorem prefixBoundary_iff_currentP_le_of_lowerFarey
    (w : Word)
    {cut P Q Pn Qn : ℕ}
    (B : IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hDepth : Word.prefixTwoDepth w cut = Q)
    (hPLt : P < Pn) :
    Word.prefixTwoDepth w cut ≤ Critical.beattyIndex cut ↔
      P ≤ cut := by
  rw [prefixTwoDepth_le_beatty_iff_inverseBoundary]
  rw [hDepth]
  rw [beattyInverseHeight_currentQ_eq_currentP_of_lowerFarey B hPLt]

/--
residual `k₀=0` の upper first-passage boundary。

upper seam の一段補正により exact 条件は `P+1 ≤ cut` になる。
-/
theorem prefixBoundary_iff_currentP_add_one_le_of_upperFarey
    (w : Word)
    {cut P Q Pn Qn : ℕ}
    (B : IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hDepth : Word.prefixTwoDepth w cut = Q)
    (hPLt : P < Pn) :
    Word.prefixTwoDepth w cut ≤ Critical.beattyIndex cut ↔
      P + 1 ≤ cut := by
  rw [prefixTwoDepth_le_beatty_iff_inverseBoundary]
  rw [hDepth]
  rw [beattyInverseHeight_currentQ_eq_currentP_add_one_of_upperFarey B hPLt]

/-- lower endpoint にある first-passage prefix は `P` 以降にしか現れない。 -/
theorem criticalFirstPassage_prefix_currentP_le_of_lowerFarey
    {w : Word}
    (F : Word.CriticalFirstPassage w)
    {cut P Q Pn Qn : ℕ}
    (hCut : cut < Word.oddSteps w)
    (B : IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hDepth : Word.prefixTwoDepth w cut = Q)
    (hPLt : P < Pn) :
    P ≤ cut := by
  exact
    (prefixBoundary_iff_currentP_le_of_lowerFarey
      w B hDepth hPLt).1
      (F.prefixDepth_le_beatty hCut)

/-- upper endpoint にある first-passage prefix は `P+1` 以降にしか現れない。 -/
theorem criticalFirstPassage_prefix_currentP_add_one_le_of_upperFarey
    {w : Word}
    (F : Word.CriticalFirstPassage w)
    {cut P Q Pn Qn : ℕ}
    (hCut : cut < Word.oddSteps w)
    (B : IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hDepth : Word.prefixTwoDepth w cut = Q)
    (hPLt : P < Pn) :
    P + 1 ≤ cut := by
  exact
    (prefixBoundary_iff_currentP_add_one_le_of_upperFarey
      w B hDepth hPLt).1
      (F.prefixDepth_le_beatty hCut)

/-! ## RecordFerrers より下へ降ろした canonical profile API -/

/--
任意の proper profile cut は inverse Sturmian boundary の上側にある。

`RecordFerrers` の carry compatibility は不要で、profile の定義的 Beatty bound だけで成立する。
今後はこちらを正本とし、RecordFerrers 版は compatibility wrapper として読める。
-/
theorem profile_above_inverseBoundary
    {m : ℕ}
    (h : Critical.Profile m)
    {k : ℕ}
    (hk : k < m) :
    beattyInverseHeight (Critical.profileHeight h k) ≤ k := by
  exact
    (le_beattyIndex_iff_beattyInverseHeight_le).1
      (Ferrers.profileHeight_le_beatty (h := h) hk)

/--
`Admissible + strict record cut` だけで exact inverse-boundary contact が得られる。

full `RecordFerrers` の canonical carry law は不要。
-/
theorem admissibleRecordCut_eq_exactInverseBoundary
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a : ℕ}
    (C : Ferrers.IsRecordCutAfter
      h Critical.initialRoofAnchor a) :
    beattyInverseHeight (Critical.profileHeight h a) = a := by
  apply roofCut_profileHeight_eq_exactInverseBoundary
  exact Ferrers.isRoofCut_of_isRecordCutAfter A C

/--
任意の admissible profile の deterministic `initialRecordCuts` endpoint は
exact inverse-boundary contact である。
-/
theorem admissibleInitialRecordCut_eq_exactInverseBoundary
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a : ℕ}
    (ha : a ∈ Ferrers.initialRecordCuts h) :
    beattyInverseHeight (Critical.profileHeight h a) = a := by
  have C : Ferrers.IsRecordCutAfter
      h Critical.initialRoofAnchor a := by
    change a ∈ Ferrers.recordCutsAfter h Critical.initialRoofAnchor at ha
    exact ((Ferrers.mem_recordCutsAfter_iff).1 ha).2
  exact admissibleRecordCut_eq_exactInverseBoundary A C

/--
lower endpoint `Q` にある admissible record cut の odd coordinate は exact に `P`。

これは `RecordFerrers` より弱い仮定だけで成立する endpoint glue。
-/
theorem admissibleRecordCut_coordinate_eq_currentP_of_lowerFarey
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a P Q Pn Qn : ℕ}
    (C : Ferrers.IsRecordCutAfter
      h Critical.initialRoofAnchor a)
    (B : IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hHeight : Critical.profileHeight h a = Q)
    (hPLt : P < Pn) :
    a = P := by
  have hContact := admissibleRecordCut_eq_exactInverseBoundary A C
  rw [hHeight] at hContact
  rw [beattyInverseHeight_currentQ_eq_currentP_of_lowerFarey B hPLt] at hContact
  exact hContact.symm

/--
upper endpoint `Q` にある admissible record cut は seam correction により `P+1`。
-/
theorem admissibleRecordCut_coordinate_eq_currentP_add_one_of_upperFarey
    {m : ℕ}
    {h : Critical.Profile m}
    (A : Critical.Admissible h)
    {a P Q Pn Qn : ℕ}
    (C : Ferrers.IsRecordCutAfter
      h Critical.initialRoofAnchor a)
    (B : IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hHeight : Critical.profileHeight h a = Q)
    (hPLt : P < Pn) :
    a = P + 1 := by
  have hContact := admissibleRecordCut_eq_exactInverseBoundary A C
  rw [hHeight] at hContact
  rw [beattyInverseHeight_currentQ_eq_currentP_add_one_of_upperFarey B hPLt] at hContact
  exact hContact.symm

/-- RecordFerrers 版 lower endpoint は generic admissible-profile theorem の wrapper。 -/
theorem recordFerrers_recordCut_coordinate_eq_currentP_of_lowerFarey
    {m : ℕ}
    (R : Ferrers.RecordFerrers m)
    {a P Q Pn Qn : ℕ}
    (C : Ferrers.IsRecordCutAfter
      R.profile.1 Critical.initialRoofAnchor a)
    (B : IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hHeight : Critical.profileHeight R.profile.1 a = Q)
    (hPLt : P < Pn) :
    a = P :=
  admissibleRecordCut_coordinate_eq_currentP_of_lowerFarey
    R.profile.2 C B hHeight hPLt

/-- RecordFerrers 版 upper endpoint も generic theorem の wrapper。 -/
theorem recordFerrers_recordCut_coordinate_eq_currentP_add_one_of_upperFarey
    {m : ℕ}
    (R : Ferrers.RecordFerrers m)
    {a P Q Pn Qn : ℕ}
    (C : Ferrers.IsRecordCutAfter
      R.profile.1 Critical.initialRoofAnchor a)
    (B : IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hHeight : Critical.profileHeight R.profile.1 a = Q)
    (hPLt : P < Pn) :
    a = P + 1 :=
  admissibleRecordCut_coordinate_eq_currentP_add_one_of_upperFarey
    R.profile.2 C B hHeight hPLt

end Bridge
end Collatz3
