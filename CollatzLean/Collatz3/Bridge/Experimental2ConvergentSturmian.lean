import CollatzLean.Collatz3.Experimental2.MechanicalInverseCorridor
import CollatzLean.Collatz3.Bridge.Experimental2SturmianBoundary
import CollatzLean.Collatz3.Ferrers.RecordFerrers

/-!
# Collatz3 Bridge: convergent corridor から Sturmian boundary / FirstPassage / RecordFerrers へ

`MechanicalConvergentCorridor` と `MechanicalInverse` を合成すると、
Beatty roof の convergent corridor

`beattyIndex(P+x) = Q + beattyIndex(x)`

は、その離散逆側で

`beattyInverseHeight(Q+k) = P + beattyInverseHeight(k)`

へ exact に転置される。

ここで `beattyInverseHeight(k) = ceil(k * log₃ 2)` なので、
これは `log₃ 2` 側 Sturmian boundary の exact finite block structure そのものである。

さらに現在の `CriticalFirstPassage` は inverse boundary 条件と exact に同値であり、
RecordFerrers の strict record cut は critical roof cut なので、同じ境界 translation を
FirstPassage と RecordFerrers の両方へ運べる。

このファイルで接続する流れは

consecutive Farey / convergent bracket
  → Beatty roof corridor
  → inverse Sturmian corridor
  → FirstPassage prefix boundary
  → RecordFerrers roof contacts

である。

continued fraction の convergent 列そのものを新しい data として保存せず、
既存 `IsLowerFareyBracket` / `IsUpperFareyBracket` certificate を入口に使う。
-/

namespace Collatz3
namespace Bridge

/--
Beatty roof を一度上がってから離散逆で戻ると元の odd coordinate に exact に戻る。

`beattyIndex` は strict に増えるため、一般の monotone roof にあり得る plateau はない。
これにより roof cut は転置 Sturmian 座標でも exact boundary contact になる。
-/
theorem beattyInverseHeight_beattyIndex
    (m : ℕ) :
    beattyInverseHeight (Critical.beattyIndex m) = m := by
  have hUpper :
      beattyInverseHeight (Critical.beattyIndex m) ≤ m :=
    beattyInverseHeight_le_of_reaches (by exact le_rfl)
  have hLower :
      m ≤ beattyInverseHeight (Critical.beattyIndex m) := by
    by_contra hNot
    have hInvLt :
        beattyInverseHeight (Critical.beattyIndex m) < m := by omega
    have hSuccLe :
        beattyInverseHeight (Critical.beattyIndex m) + 1 ≤ m := by omega
    have hStep :=
      Critical.beattyIndex_lt_succ
        (beattyInverseHeight (Critical.beattyIndex m))
    have hTailMono :=
      beattyIndex_mono_via_upper hSuccLe
    have hStrict :
        Critical.beattyIndex (beattyInverseHeight (Critical.beattyIndex m)) <
          Critical.beattyIndex m :=
      lt_of_lt_of_le hStep hTailMono
    have hSpec :=
      beattyInverseHeight_spec (Critical.beattyIndex m)
    omega
  exact Nat.le_antisymm hUpper hLower

/--
lower convergent corridor の exact inverse translation を Beatty roof に特殊化する。
-/
theorem beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey
    {P Q Pn Qn k : ℕ}
    (B : Experimental2.IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk : 0 < k)
    (hRange : P + beattyInverseHeight k < Pn) :
    beattyInverseHeight (Q + k) = P + beattyInverseHeight k := by
  have hMono : Monotone Critical.beattyIndex := by
    intro a b hab
    exact beattyIndex_mono_via_upper hab
  simpa [beattyInverseHeight] using
    (Experimental2.IsLowerMechanicalRoof.inverse_add_currentQ_eq_add_currentP_of_lowerFarey
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      hMono
      B hk hRange)

/-- upper convergent corridor の exact inverse translation。 -/
theorem beattyInverseHeight_add_currentQ_eq_add_currentP_of_upperFarey
    {P Q Pn Qn k : ℕ}
    (B : Experimental2.IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk : 0 < k)
    (hRange : P + beattyInverseHeight k < Pn) :
    beattyInverseHeight (Q + k) = P + beattyInverseHeight k := by
  have hMono : Monotone Critical.beattyIndex := by
    intro a b hab
    exact beattyIndex_mono_via_upper hab
  simpa [beattyInverseHeight] using
    (Experimental2.IsLowerMechanicalRoof.inverse_add_currentQ_eq_add_currentP_of_upperFarey
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      hMono
      B hk hRange)
/--
lower corridor を `log₃ 2` の ceiling 境界だけで書いた形。

`Q` だけ vertical threshold を進めると、boundary height は exact に `P` 増える。
-/
theorem sturmianCeil_add_currentQ_eq_add_currentP_of_lowerFarey
    {P Q Pn Qn k : ℕ}
    (B : Experimental2.IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk : 0 < k)
    (hRange : P + beattyInverseHeight k < Pn) :
    ⌈((Q + k : ℕ) : ℝ) * Real.logb 3 2⌉₊ =
      P + ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
  calc
    ⌈((Q + k : ℕ) : ℝ) * Real.logb 3 2⌉₊ =
        beattyInverseHeight (Q + k) :=
      (beattyInverseHeight_eq_natCeil_mul_logb_three_two (Q + k)).symm
    _ = P + beattyInverseHeight k :=
      beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey
        B hk hRange
    _ = P + ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
      rw [beattyInverseHeight_eq_natCeil_mul_logb_three_two]

/-- upper corridor の `log₃ 2` ceiling 表示。 -/
theorem sturmianCeil_add_currentQ_eq_add_currentP_of_upperFarey
    {P Q Pn Qn k : ℕ}
    (B : Experimental2.IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk : 0 < k)
    (hRange : P + beattyInverseHeight k < Pn) :
    ⌈((Q + k : ℕ) : ℝ) * Real.logb 3 2⌉₊ =
      P + ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
  calc
    ⌈((Q + k : ℕ) : ℝ) * Real.logb 3 2⌉₊ =
        beattyInverseHeight (Q + k) :=
      (beattyInverseHeight_eq_natCeil_mul_logb_three_two (Q + k)).symm
    _ = P + beattyInverseHeight k :=
      beattyInverseHeight_add_currentQ_eq_add_currentP_of_upperFarey
        B hk hRange
    _ = P + ⌈(k : ℝ) * Real.logb 3 2⌉₊ := by
      rw [beattyInverseHeight_eq_natCeil_mul_logb_three_two]

/--
lower corridor では inverse Sturmian boundary の一歩差分が `Q` shift で exact に反復する。

したがって corridor 内の finite bit block は、height 方向に `Q` ずらしても同一。
-/
theorem beattyInverseStep_add_currentQ_eq_of_lowerFarey
    {P Q Pn Qn k : ℕ}
    (B : Experimental2.IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk : 0 < k)
    (hRange : P + beattyInverseHeight (k + 1) < Pn) :
    beattyInverseHeight (Q + k + 1) - beattyInverseHeight (Q + k) =
      beattyInverseHeight (k + 1) - beattyInverseHeight k := by
  have hMono : Monotone Critical.beattyIndex := by
    intro a b hab
    exact beattyIndex_mono_via_upper hab
  simpa [beattyInverseHeight,
    Experimental2.IsLowerMechanicalRoof.inverseStep] using
    (Experimental2.IsLowerMechanicalRoof.inverseStep_add_currentQ_eq_inverseStep_of_lowerFarey
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      hMono
      B hk hRange)

/-- upper corridor でも positive domain では同じ inverse bit が `Q` shift で反復する。 -/
theorem beattyInverseStep_add_currentQ_eq_of_upperFarey
    {P Q Pn Qn k : ℕ}
    (B : Experimental2.IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk : 0 < k)
    (hRange : P + beattyInverseHeight (k + 1) < Pn) :
    beattyInverseHeight (Q + k + 1) - beattyInverseHeight (Q + k) =
      beattyInverseHeight (k + 1) - beattyInverseHeight k := by
  have hMono : Monotone Critical.beattyIndex := by
    intro a b hab
    exact beattyIndex_mono_via_upper hab
  simpa [beattyInverseHeight,
    Experimental2.IsLowerMechanicalRoof.inverseStep] using
    (Experimental2.IsLowerMechanicalRoof.inverseStep_add_currentQ_eq_inverseStep_of_upperFarey
      beattyIndex_isLowerMechanical_logb_two_three
      one_le_logb_two_three
      hMono
      B hk hRange)

/--
lower convergent corridor 内で、prefix depth が `Q+k₀` の形なら
first-passage roof 条件は residual inverse boundary へ exact に還元される。
-/
theorem prefixBoundary_iff_residualInverse_of_lowerFarey
    (w : Word)
    {cut P Q Pn Qn k₀ : ℕ}
    (B : Experimental2.IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk₀ : 0 < k₀)
    (hDepth : Word.prefixTwoDepth w cut = Q + k₀)
    (hRange : P + beattyInverseHeight k₀ < Pn) :
    Word.prefixTwoDepth w cut ≤ Critical.beattyIndex cut ↔
      P + beattyInverseHeight k₀ ≤ cut := by
  rw [prefixTwoDepth_le_beatty_iff_inverseBoundary]
  rw [hDepth]
  rw [beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey
    B hk₀ hRange]

/-- upper convergent corridor に対する同じ residual boundary reduction。 -/
theorem prefixBoundary_iff_residualInverse_of_upperFarey
    (w : Word)
    {cut P Q Pn Qn k₀ : ℕ}
    (B : Experimental2.IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk₀ : 0 < k₀)
    (hDepth : Word.prefixTwoDepth w cut = Q + k₀)
    (hRange : P + beattyInverseHeight k₀ < Pn) :
    Word.prefixTwoDepth w cut ≤ Critical.beattyIndex cut ↔
      P + beattyInverseHeight k₀ ≤ cut := by
  rw [prefixTwoDepth_le_beatty_iff_inverseBoundary]
  rw [hDepth]
  rw [beattyInverseHeight_add_currentQ_eq_add_currentP_of_upperFarey
    B hk₀ hRange]

/--
critical first-passage prefix を lower convergent corridor で residualize する。

prefix two-depth が `Q+k₀` なら、その odd cut は
`P + beattyInverseHeight(k₀)` 以上でなければならない。
-/
theorem criticalFirstPassage_prefix_residualBoundary_of_lowerFarey
    {w : Word}
    (F : Word.CriticalFirstPassage w)
    {cut P Q Pn Qn k₀ : ℕ}
    (hCut : cut < Word.oddSteps w)
    (B : Experimental2.IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk₀ : 0 < k₀)
    (hDepth : Word.prefixTwoDepth w cut = Q + k₀)
    (hRange : P + beattyInverseHeight k₀ < Pn) :
    P + beattyInverseHeight k₀ ≤ cut := by
  exact
    (prefixBoundary_iff_residualInverse_of_lowerFarey
      w B hk₀ hDepth hRange).1
      (F.prefixDepth_le_beatty hCut)

/-- upper convergent corridor に対する first-passage residual boundary。 -/
theorem criticalFirstPassage_prefix_residualBoundary_of_upperFarey
    {w : Word}
    (F : Word.CriticalFirstPassage w)
    {cut P Q Pn Qn k₀ : ℕ}
    (hCut : cut < Word.oddSteps w)
    (B : Experimental2.IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk₀ : 0 < k₀)
    (hDepth : Word.prefixTwoDepth w cut = Q + k₀)
    (hRange : P + beattyInverseHeight k₀ < Pn) :
    P + beattyInverseHeight k₀ ≤ cut := by
  exact
    (prefixBoundary_iff_residualInverse_of_upperFarey
      w B hk₀ hDepth hRange).1
      (F.prefixDepth_le_beatty hCut)

/--
任意の proper profile cut は転置 Sturmian boundary の上側にある。

RecordFerrers 固有の carry law は不要で、profile の Beatty roof bound だけから従う。
-/
theorem recordFerrers_profile_above_inverseBoundary
    {m : ℕ}
    (R : Ferrers.RecordFerrers m)
    {k : ℕ}
    (hk : k < m) :
    beattyInverseHeight (Critical.profileHeight R.profile.1 k) ≤ k := by
  exact
    (le_beattyIndex_iff_beattyInverseHeight_le).1
      (Ferrers.profileHeight_le_beatty (h := R.profile.1) hk)

/--
critical roof cut は転置座標でも exact boundary contact。

profile height が `beattyIndex(a)` に一致することと
`beattyInverseHeight(profileHeight)=a` が同じ格子点を表す。
-/
theorem roofCut_profileHeight_eq_exactInverseBoundary
    {m : ℕ}
    {h : Critical.Profile m}
    {a : ℕ}
    (A : Critical.IsRoofCut h a) :
    beattyInverseHeight (Critical.profileHeight h a) = a := by
  rw [Critical.IsRoofCut.height_eq A]
  exact beattyInverseHeight_beattyIndex a

/--
RecordFerrers の strict record cut は必ず exact inverse-boundary contact になる。

これが Record 幾何と Sturmian inverse boundary の直接 bridge。
-/
theorem recordFerrers_recordCut_eq_exactInverseBoundary
    {m : ℕ}
    (R : Ferrers.RecordFerrers m)
    {a : ℕ}
    (C : Ferrers.IsRecordCutAfter
      R.profile.1 Critical.initialRoofAnchor a) :
    beattyInverseHeight (Critical.profileHeight R.profile.1 a) = a := by
  apply roofCut_profileHeight_eq_exactInverseBoundary
  exact Ferrers.isRoofCut_of_isRecordCutAfter R.profile.2 C


/--
`initialRecordCuts` に実際に現れる canonical cut はすべて exact inverse-boundary contact。

これにより deterministic record partition の endpoint 列を Sturmian boundary 上の格子点として読める。
-/
theorem recordFerrers_initialRecordCut_eq_exactInverseBoundary
    {m : ℕ}
    (R : Ferrers.RecordFerrers m)
    {a : ℕ}
    (ha : a ∈ Ferrers.initialRecordCuts R.profile.1) :
    beattyInverseHeight (Critical.profileHeight R.profile.1 a) = a := by
  have C : Ferrers.IsRecordCutAfter
      R.profile.1 Critical.initialRoofAnchor a := by
    change a ∈ Ferrers.recordCutsAfter
      R.profile.1 Critical.initialRoofAnchor at ha
    have hSpec := (Ferrers.mem_recordCutsAfter_iff).1 ha
    exact hSpec.2
  exact recordFerrers_recordCut_eq_exactInverseBoundary R C

/--
lower convergent corridor 内の RecordFerrers record cut の座標分解。

record cut の profile height が `Q+k₀` なら、その odd coordinate は exact に

`P + beattyInverseHeight(k₀)`

へ分解される。
-/
theorem recordFerrers_recordCut_coordinate_eq_add_currentP_of_lowerFarey
    {m : ℕ}
    (R : Ferrers.RecordFerrers m)
    {a P Q Pn Qn k₀ : ℕ}
    (C : Ferrers.IsRecordCutAfter
      R.profile.1 Critical.initialRoofAnchor a)
    (B : Experimental2.IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk₀ : 0 < k₀)
    (hHeight : Critical.profileHeight R.profile.1 a = Q + k₀)
    (hRange : P + beattyInverseHeight k₀ < Pn) :
    a = P + beattyInverseHeight k₀ := by
  have hContact := recordFerrers_recordCut_eq_exactInverseBoundary R C
  rw [hHeight] at hContact
  rw [beattyInverseHeight_add_currentQ_eq_add_currentP_of_lowerFarey
    B hk₀ hRange] at hContact
  exact hContact.symm

/-- upper convergent corridor に対する RecordFerrers record-cut 座標分解。 -/
theorem recordFerrers_recordCut_coordinate_eq_add_currentP_of_upperFarey
    {m : ℕ}
    (R : Ferrers.RecordFerrers m)
    {a P Q Pn Qn k₀ : ℕ}
    (C : Ferrers.IsRecordCutAfter
      R.profile.1 Critical.initialRoofAnchor a)
    (B : Experimental2.IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk₀ : 0 < k₀)
    (hHeight : Critical.profileHeight R.profile.1 a = Q + k₀)
    (hRange : P + beattyInverseHeight k₀ < Pn) :
    a = P + beattyInverseHeight k₀ := by
  have hContact := recordFerrers_recordCut_eq_exactInverseBoundary R C
  rw [hHeight] at hContact
  rw [beattyInverseHeight_add_currentQ_eq_add_currentP_of_upperFarey
    B hk₀ hRange] at hContact
  exact hContact.symm

/-- lower corridor の record-cut 座標を `log₃ 2` ceiling だけで表示する。 -/
theorem recordFerrers_recordCut_coordinate_eq_sturmianCeil_of_lowerFarey
    {m : ℕ}
    (R : Ferrers.RecordFerrers m)
    {a P Q Pn Qn k₀ : ℕ}
    (C : Ferrers.IsRecordCutAfter
      R.profile.1 Critical.initialRoofAnchor a)
    (B : Experimental2.IsLowerFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk₀ : 0 < k₀)
    (hHeight : Critical.profileHeight R.profile.1 a = Q + k₀)
    (hRange : P + beattyInverseHeight k₀ < Pn) :
    a = P + ⌈(k₀ : ℝ) * Real.logb 3 2⌉₊ := by
  calc
    a = P + beattyInverseHeight k₀ :=
      recordFerrers_recordCut_coordinate_eq_add_currentP_of_lowerFarey
        R C B hk₀ hHeight hRange
    _ = P + ⌈(k₀ : ℝ) * Real.logb 3 2⌉₊ := by
      rw [beattyInverseHeight_eq_natCeil_mul_logb_three_two]

/-- upper corridor の record-cut 座標を `log₃ 2` ceiling だけで表示する。 -/
theorem recordFerrers_recordCut_coordinate_eq_sturmianCeil_of_upperFarey
    {m : ℕ}
    (R : Ferrers.RecordFerrers m)
    {a P Q Pn Qn k₀ : ℕ}
    (C : Ferrers.IsRecordCutAfter
      R.profile.1 Critical.initialRoofAnchor a)
    (B : Experimental2.IsUpperFareyBracket
      (Real.logb 2 3) P Q Pn Qn)
    (hk₀ : 0 < k₀)
    (hHeight : Critical.profileHeight R.profile.1 a = Q + k₀)
    (hRange : P + beattyInverseHeight k₀ < Pn) :
    a = P + ⌈(k₀ : ℝ) * Real.logb 3 2⌉₊ := by
  calc
    a = P + beattyInverseHeight k₀ :=
      recordFerrers_recordCut_coordinate_eq_add_currentP_of_upperFarey
        R C B hk₀ hHeight hRange
    _ = P + ⌈(k₀ : ℝ) * Real.logb 3 2⌉₊ := by
      rw [beattyInverseHeight_eq_natCeil_mul_logb_three_two]

end Bridge
end Collatz3
