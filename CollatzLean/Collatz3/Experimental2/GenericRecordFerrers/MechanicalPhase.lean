import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordFerrers
import CollatzLean.Collatz3.Experimental2.MechanicalCharacterization
import CollatzLean.Collatz3.Experimental2.RotationPhase
import Mathlib.Tactic.Linarith

/-!
# Collatz3 Experimental2: 一般 RecordFerrers の mechanical phase 表現

第1--9段階で、一般 unit-carry roof 上の deterministic record geometry と
canonical carry law を構成し、Collatz の `Ferrers.RecordFerrers` がその
Beatty/profile-height 特殊化であることまで閉じた。

このファイルでは、その exact carry law を lower mechanical roof の回転 phase へ移す。

中心は既存の一般定理

`roofCarry β a r = 1 ↔ 1 ≤ roofPhase β σ a + roofPhase β σ r`

である。これを canonical block chain 全体へ持ち上げることで、

* premature carry-1 roof return 禁止 ↔ premature phase-wrap roof return 禁止、
* terminal carry `0` ↔ terminal phase sum `< 1`、
* canonical carry compatibility ↔ canonical phase threshold compatibility

を exact に示す。

ここでは lower mechanical convention だけを扱う。
irrational roof slope は既存の `HasUnitCarry.lowerMechanical_of_irrational_roofSlope` により
lower mechanical になるため、次の任意無理回転層へそのまま接続できる。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

/--
lower mechanical roof では carry `0` と phase 和の strict non-wrap `< 1` が exact に同値。

carry が `0` または `1` の二値であることと、既存の carry-one/wrap 同値だけから導く。
-/
theorem roofCarry_eq_zero_iff_lowerPhase_nonwrap
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    (a b : ℕ) :
    roofCarry β a b = 0 ↔
      roofPhase β σ a + roofPhase β σ b < 1 := by
  constructor
  · intro hZero
    have hNotOne : roofCarry β a b ≠ 1 := by
      omega
    by_contra hNotLt
    have hWrap :
        1 ≤ roofPhase β σ a + roofPhase β σ b :=
      le_of_not_gt hNotLt
    exact hNotOne ((carry_eq_one_iff_lowerPhase_wrap U M a b).2 hWrap)
  · intro hNonwrap
    rcases U.carry_eq_zero_or_one a b with hZero | hOne
    · exact hZero
    · have hWrap :=
        (carry_eq_one_iff_lowerPhase_wrap U M a b).1 hOne
      linarith

/--
proper local prefix で禁止する phase 版 event。

途中で再び roof に乗り、その block phase が threshold `1` を wrap することを排除する。
`NoPrematureCarryOneRoofReturn` の lower mechanical 表現である。
-/
def NoPrematurePhaseWrapRoofReturn
    (β : ℕ → ℕ)
    (σ : ℝ)
    (m : ℕ)
    (height : ℕ → ℕ)
    (a r : ℕ) : Prop :=
  ∀ j : ℕ,
    0 < j →
    j < r →
    ¬ (IsProperRoofCut β m height (a + j) ∧
      1 ≤ roofPhase β σ a + roofPhase β σ j)

/--
premature carry-1 roof return 禁止と premature phase-wrap roof return 禁止は exact に同値。
-/
theorem noPrematureCarryOneRoofReturn_iff_phaseWrap
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {m : ℕ}
    {height : ℕ → ℕ}
    (a r : ℕ) :
    NoPrematureCarryOneRoofReturn β m height a r ↔
      NoPrematurePhaseWrapRoofReturn β σ m height a r := by
  constructor
  · intro C j hjPos hjLt hBad
    apply C j hjPos hjLt
    exact
      ⟨hBad.1,
        (carry_eq_one_iff_lowerPhase_wrap U M a j).2 hBad.2⟩
  · intro P j hjPos hjLt hBad
    apply P j hjPos hjLt
    exact
      ⟨hBad.1,
        (carry_eq_one_iff_lowerPhase_wrap U M a j).1 hBad.2⟩

/--
lower mechanical phase で書いた contextual compatibility。

interior boundary carry `1` は canonical record geometry から自動導出されるため、
carry 版と同様にここでも保存しない。

* 各 block の proper prefix で phase-wrap roof return を禁止する。
* 最終 block の phase 和だけ strict non-wrap `< 1` を要求する。
-/
def PhaseThresholdCompatibleFrom
    (β : ℕ → ℕ)
    (σ : ℝ)
    (m : ℕ)
    (height : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] =>
      NoPrematurePhaseWrapRoofReturn β σ m height a r ∧
        roofPhase β σ a + roofPhase β σ r < 1
  | a, r :: s :: rs =>
      NoPrematurePhaseWrapRoofReturn β σ m height a r ∧
        PhaseThresholdCompatibleFrom β σ m height (a + r) (s :: rs)

/--
任意 block length 列上で contextual carry compatibility と lower mechanical phase threshold
compatibility は exact に同値。
-/
theorem contextualCarryCompatibleFrom_iff_phaseThresholdCompatibleFrom
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {m : ℕ}
    {height : ℕ → ℕ} :
    ∀ (a : ℕ) (rs : List ℕ),
      ContextualCarryCompatibleFrom β m height a rs ↔
        PhaseThresholdCompatibleFrom β σ m height a rs
  | _a, [] => by
      simp [ContextualCarryCompatibleFrom, PhaseThresholdCompatibleFrom]
  | a, [r] => by
      simp only [ContextualCarryCompatibleFrom, PhaseThresholdCompatibleFrom]
      exact and_congr
        (noPrematureCarryOneRoofReturn_iff_phaseWrap U M a r)
        (roofCarry_eq_zero_iff_lowerPhase_nonwrap U M a r)
  | a, r :: s :: rs => by
      simp only [ContextualCarryCompatibleFrom, PhaseThresholdCompatibleFrom]
      exact and_congr
        (noPrematureCarryOneRoofReturn_iff_phaseWrap U M a r)
        (contextualCarryCompatibleFrom_iff_phaseThresholdCompatibleFrom
          U M (a + r) (s :: rs))

/--
deterministic canonical record partition 上の lower mechanical phase threshold law。
-/
def CanonicalPhaseThresholdCompatible
    (β : ℕ → ℕ)
    (σ : ℝ)
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  PhaseThresholdCompatibleFrom
    β σ m height canonicalAnchor (canonicalRecordLengths β m height)

/-- canonical phase threshold compatibility の定義展開用 theorem。 -/
theorem canonicalPhaseThresholdCompatible_iff
    {β : ℕ → ℕ}
    {σ : ℝ}
    {m : ℕ}
    {height : ℕ → ℕ} :
    CanonicalPhaseThresholdCompatible β σ m height ↔
      PhaseThresholdCompatibleFrom
        β σ m height canonicalAnchor (canonicalRecordLengths β m height) := by
  rfl

/--
canonical carry compatibility と canonical lower mechanical phase threshold law は exact に同値。

この定理が一般 RecordFerrers の carry 語彙と回転 phase 語彙を直接接着する。
-/
theorem canonicalCarryCompatible_iff_phaseThresholdCompatible
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {m : ℕ}
    {height : ℕ → ℕ} :
    CanonicalCarryCompatible β m height ↔
      CanonicalPhaseThresholdCompatible β σ m height := by
  unfold CanonicalCarryCompatible CanonicalPhaseThresholdCompatible
  exact
    contextualCarryCompatibleFrom_iff_phaseThresholdCompatibleFrom
      U M canonicalAnchor (canonicalRecordLengths β m height)

/--
canonical phase threshold law と canonical 全 block の local criticality も exact に同値。

carry を中間語彙として使うが、結論は phase と局所幾何だけで書かれる。
-/
theorem canonicalPhaseThresholdCompatible_iff_localRoofCriticalBlocks
    {β : ℕ → ℕ}
    (U : HasUnitCarry β)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m) :
    CanonicalPhaseThresholdCompatible β σ m height ↔
      LocalRoofCriticalBlocksFrom
        β m height canonicalAnchor (canonicalRecordLengths β m height) := by
  constructor
  · intro P
    have C : CanonicalCarryCompatible β m height :=
      (canonicalCarryCompatible_iff_phaseThresholdCompatible U M).2 P
    exact
      (canonicalCarryCompatible_iff_localRoofCriticalBlocks
        U A hβ1 hm).1 C
  · intro L
    have C : CanonicalCarryCompatible β m height :=
      (canonicalCarryCompatible_iff_localRoofCriticalBlocks
        U A hβ1 hm).2 L
    exact
      (canonicalCarryCompatible_iff_phaseThresholdCompatible U M).1 C

/--
lower mechanical roof を固定すると、本質的 canonical record law は

* `1 < m`,
* canonical phase threshold compatibility

だけで特徴付けられる。unit-carry 性は mechanical roof から導出される。
-/
theorem hasCanonicalRecordLaw_iff_phaseThresholdCompatible
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {m : ℕ}
    {height : ℕ → ℕ} :
    HasCanonicalRecordLaw β m height ↔
      1 < m ∧ CanonicalPhaseThresholdCompatible β σ m height := by
  constructor
  · rintro ⟨U, hm, C⟩
    exact
      ⟨hm,
        (canonicalCarryCompatible_iff_phaseThresholdCompatible U M).1 C⟩
  · rintro ⟨hm, P⟩
    have U : HasUnitCarry β := M.hasUnitCarry
    exact
      ⟨U, hm,
        (canonicalCarryCompatible_iff_phaseThresholdCompatible U M).2 P⟩

/--
lower mechanical roof 上では完成 RecordFerrers path を phase threshold 語彙だけで特徴付けられる。

`β 1 = 1` と admissibility は path 側の条件として残り、
record/carry law の部分だけが rotation threshold へ置き換わる。
-/
theorem isRecordFerrersPath_iff_phaseThresholdCompatible
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {m : ℕ}
    {height : ℕ → ℕ} :
    IsRecordFerrersPath β m height ↔
      β 1 = 1 ∧
        IsAdmissibleRoofPath β m height ∧
          1 < m ∧ CanonicalPhaseThresholdCompatible β σ m height := by
  constructor
  · rintro ⟨hβ1, A, H⟩
    have hPhase :=
      (hasCanonicalRecordLaw_iff_phaseThresholdCompatible M).1 H
    exact ⟨hβ1, A, hPhase.1, hPhase.2⟩
  · rintro ⟨hβ1, A, hm, P⟩
    exact
      ⟨hβ1, A,
        (hasCanonicalRecordLaw_iff_phaseThresholdCompatible M).2 ⟨hm, P⟩⟩

namespace RecordFerrers

/--
完成 RecordFerrers は、任意に与えた lower mechanical slope に対して
canonical phase threshold compatibility を満たす。
-/
theorem phaseThresholdCompatible
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ) :
    CanonicalPhaseThresholdCompatible β σ m R.height :=
  (canonicalCarryCompatible_iff_phaseThresholdCompatible
    R.unitCarry M).1 R.carryCompatible

/--
lower mechanical roof、admissible path、標準 gauge、幅、canonical phase threshold law から
直接 RecordFerrers を構成する。
-/
def ofCanonicalPhase
    {β : ℕ → ℕ}
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ)
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath β m height)
    (hβ1 : β 1 = 1)
    (hm : 1 < m)
    (P : CanonicalPhaseThresholdCompatible β σ m height) :
    RecordFerrers β m := by
  have U : HasUnitCarry β := M.hasUnitCarry
  exact
    ofCanonicalCarry U A hβ1 hm
      ((canonicalCarryCompatible_iff_phaseThresholdCompatible U M).2 P)

/--
完成 RecordFerrers の canonical local critical geometry は、
その lower mechanical phase threshold law からも exact に回収できる。
-/
theorem localCriticalBlocks_of_phase
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    {σ : ℝ}
    (M : IsLowerMechanicalRoof β σ) :
    LocalRoofCriticalBlocksFrom
      β m R.height canonicalAnchor (canonicalRecordLengths β m R.height) := by
  exact
    (canonicalPhaseThresholdCompatible_iff_localRoofCriticalBlocks
      R.unitCarry M R.admissible R.roof_one R.one_lt_width).1
      (R.phaseThresholdCompatible M)

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
