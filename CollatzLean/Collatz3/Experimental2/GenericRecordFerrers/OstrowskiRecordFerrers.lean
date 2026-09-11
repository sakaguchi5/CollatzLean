import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RotationOstrowskiSystem

/-!
# Collatz3 Experimental2: 任意無理回転の Ostrowski / RecordFerrers exact bridge

第10段階では一般 RecordFerrers の canonical carry law を lower mechanical phase threshold へ移し、
第12段階では任意の無理回転 `α ∈ (0,1)` から canonical lifted roof

`β_α(n) = n + floor(n α)`

を構成した。第13段階では、同じ回転の canonical horizontal Ostrowski digits から

`N α = integer(N) + error(N)`

を exact に復元し、lifted roof の phase が `fract(error(N))` に一致することまで示した。

このファイルでは両者を接着する。
新しい RecordFerrers 条件は導入せず、既存の phase threshold law を
canonical Ostrowski error の fractional partで読み替えるだけである。

中心結果は

`CanonicalCarryCompatible`
`↔ CanonicalPhaseThresholdCompatible`
`↔ CanonicalOstrowskiThresholdCompatible`
`↔ LocalRoofCriticalBlocksFrom`

である。

したがって任意の無理回転 roof 上では RecordFerrers 性を
canonical Ostrowski error の threshold 条件だけで特徴付けられる。
-/

namespace Collatz3
namespace Experimental2
namespace GenericRecordFerrers

namespace RotationOstrowskiSystem

/--
canonical horizontal Ostrowski decomposition から得る回転 phase。

整数部分は fractional part で消えるため、必要なのは composite error の fractional part だけである。
-/
noncomputable def ostrowskiPhase
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) : ℝ :=
  Int.fract (D.rotationBlockError N)

/--
Ostrowski phase は pure rotation `N α` の fractional part と exact に一致する。
-/
theorem ostrowskiPhase_eq_fract_mul_rotation
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (N : ℕ) :
    D.ostrowskiPhase N = Int.fract ((N : ℝ) * α) := by
  unfold ostrowskiPhase
  exact (D.fract_mul_rotation_eq_fract_blockError N).symm

/--
任意の無理回転 lifted roof の mechanical phase は canonical Ostrowski phase そのもの。
-/
theorem irrationalRotationRoof_phase_eq_ostrowskiPhase
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    (N : ℕ) :
    roofPhase (irrationalRotationRoof α) (1 + α) N =
      D.ostrowskiPhase N := by
  unfold ostrowskiPhase
  exact D.irrationalRotationRoof_phase_eq_fract_rotationBlockError Arot N

/--
proper local prefix で禁止する canonical Ostrowski wrap event。

途中で再び roof に乗り、start と prefix-length の Ostrowski phase 和が threshold `1` を
wrap することを排除する。
-/
def NoPrematureOstrowskiWrapRoofReturn
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m : ℕ)
    (height : ℕ → ℕ)
    (a r : ℕ) : Prop :=
  ∀ j : ℕ,
    0 < j →
    j < r →
    ¬ (IsProperRoofCut (irrationalRotationRoof α) m height (a + j) ∧
      1 ≤ D.ostrowskiPhase a + D.ostrowskiPhase j)

/--
第10段階の premature phase-wrap 禁止条件は、任意無理回転では canonical Ostrowski wrap 禁止と exact に同値。
-/
theorem noPrematurePhaseWrapRoofReturn_iff_ostrowski
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ}
    (a r : ℕ) :
    NoPrematurePhaseWrapRoofReturn
        (irrationalRotationRoof α) (1 + α) m height a r ↔
      D.NoPrematureOstrowskiWrapRoofReturn m height a r := by
  constructor
  · intro P j hjPos hjLt hBad
    apply P j hjPos hjLt
    refine ⟨hBad.1, ?_⟩
    rw [D.irrationalRotationRoof_phase_eq_ostrowskiPhase Arot a]
    rw [D.irrationalRotationRoof_phase_eq_ostrowskiPhase Arot j]
    exact hBad.2
  · intro O j hjPos hjLt hBad
    apply O j hjPos hjLt
    refine ⟨hBad.1, ?_⟩
    rw [← D.irrationalRotationRoof_phase_eq_ostrowskiPhase Arot a]
    rw [← D.irrationalRotationRoof_phase_eq_ostrowskiPhase Arot j]
    exact hBad.2

/--
canonical Ostrowski error だけで書いた contextual threshold compatibility。

* 各 block の proper prefix で Ostrowski wrap roof return を禁止する。
* 最終 block の Ostrowski phase 和だけ strict non-wrap `< 1` を要求する。

interior boundary wrap は canonical record geometry から自動導出されるため保存しない。
-/
def OstrowskiThresholdCompatibleFrom
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m : ℕ)
    (height : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _a, [] => False
  | a, [r] =>
      D.NoPrematureOstrowskiWrapRoofReturn m height a r ∧
        D.ostrowskiPhase a + D.ostrowskiPhase r < 1
  | a, r :: s :: rs =>
      D.NoPrematureOstrowskiWrapRoofReturn m height a r ∧
        D.OstrowskiThresholdCompatibleFrom m height (a + r) (s :: rs)

/--
任意 block length 列上で mechanical phase threshold と canonical Ostrowski threshold は exact に同値。
-/
theorem phaseThresholdCompatibleFrom_iff_ostrowski
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    ∀ (a : ℕ) (rs : List ℕ),
      PhaseThresholdCompatibleFrom
          (irrationalRotationRoof α) (1 + α) m height a rs ↔
        D.OstrowskiThresholdCompatibleFrom m height a rs
  | _a, [] => by
      simp [PhaseThresholdCompatibleFrom, OstrowskiThresholdCompatibleFrom]
  | a, [r] => by
      simp only [PhaseThresholdCompatibleFrom, OstrowskiThresholdCompatibleFrom]
      rw [D.noPrematurePhaseWrapRoofReturn_iff_ostrowski Arot a r]
      rw [D.irrationalRotationRoof_phase_eq_ostrowskiPhase Arot a]
      rw [D.irrationalRotationRoof_phase_eq_ostrowskiPhase Arot r]
  | a, r :: s :: rs => by
      simp only [PhaseThresholdCompatibleFrom, OstrowskiThresholdCompatibleFrom]
      exact and_congr
        (D.noPrematurePhaseWrapRoofReturn_iff_ostrowski Arot a r)
        (D.phaseThresholdCompatibleFrom_iff_ostrowski
          Arot (a + r) (s :: rs))

/--
deterministic canonical record partition 上の Ostrowski threshold law。
-/
def CanonicalOstrowskiThresholdCompatible
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (m : ℕ)
    (height : ℕ → ℕ) : Prop :=
  D.OstrowskiThresholdCompatibleFrom
    m height canonicalAnchor
      (canonicalRecordLengths (irrationalRotationRoof α) m height)

/-- canonical Ostrowski threshold law の定義展開。 -/
theorem canonicalOstrowskiThresholdCompatible_iff
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    D.CanonicalOstrowskiThresholdCompatible m height ↔
      D.OstrowskiThresholdCompatibleFrom
        m height canonicalAnchor
          (canonicalRecordLengths (irrationalRotationRoof α) m height) := by
  rfl

/--
canonical mechanical phase threshold law と canonical Ostrowski threshold law は exact に同値。
-/
theorem canonicalPhaseThresholdCompatible_iff_ostrowski
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    CanonicalPhaseThresholdCompatible
        (irrationalRotationRoof α) (1 + α) m height ↔
      D.CanonicalOstrowskiThresholdCompatible m height := by
  unfold CanonicalPhaseThresholdCompatible CanonicalOstrowskiThresholdCompatible
  exact
    D.phaseThresholdCompatibleFrom_iff_ostrowski
      Arot canonicalAnchor
      (canonicalRecordLengths (irrationalRotationRoof α) m height)

/--
canonical carry law と canonical Ostrowski threshold law は任意無理回転 roof 上で exact に同値。
-/
theorem canonicalCarryCompatible_iff_ostrowski
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    CanonicalCarryCompatible (irrationalRotationRoof α) m height ↔
      D.CanonicalOstrowskiThresholdCompatible m height := by
  have U : HasUnitCarry (irrationalRotationRoof α) :=
    irrationalRotationRoof_hasUnitCarry Arot.nonneg
  have M : IsLowerMechanicalRoof
      (irrationalRotationRoof α) (1 + α) :=
    irrationalRotationRoof_isLowerMechanical Arot.nonneg
  exact
    (canonicalCarryCompatible_iff_phaseThresholdCompatible U M).trans
      (D.canonicalPhaseThresholdCompatible_iff_ostrowski Arot)

/--
canonical Ostrowski threshold law は、admissible path 上で canonical 全 block の
local critical geometry と exact に同値。
-/
theorem canonicalOstrowskiThresholdCompatible_iff_localRoofCriticalBlocks
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath (irrationalRotationRoof α) m height)
    (hm : 1 < m) :
    D.CanonicalOstrowskiThresholdCompatible m height ↔
      LocalRoofCriticalBlocksFrom
        (irrationalRotationRoof α) m height canonicalAnchor
        (canonicalRecordLengths (irrationalRotationRoof α) m height) := by
  have U : HasUnitCarry (irrationalRotationRoof α) :=
    irrationalRotationRoof_hasUnitCarry Arot.nonneg
  have M : IsLowerMechanicalRoof
      (irrationalRotationRoof α) (1 + α) :=
    irrationalRotationRoof_isLowerMechanical Arot.nonneg
  have hOne : irrationalRotationRoof α 1 = 1 :=
    irrationalRotationRoof_one Arot.lt_one
  exact
    (D.canonicalPhaseThresholdCompatible_iff_ostrowski Arot).symm.trans
      (canonicalPhaseThresholdCompatible_iff_localRoofCriticalBlocks
        U M A hOne hm)

/--
任意無理回転 roof 上の完成 RecordFerrers path を、canonical Ostrowski threshold だけで特徴付ける。

ambient roof の標準 gauge・unit-carry・lower mechanical 性は `Arot` から自動で供給される。
残る条件は

* admissible path,
* `1 < m`,
* canonical Ostrowski threshold law

だけである。
-/
theorem isRecordFerrersPath_iff_ostrowski
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ} :
    IsRecordFerrersPath (irrationalRotationRoof α) m height ↔
      IsAdmissibleRoofPath (irrationalRotationRoof α) m height ∧
        1 < m ∧
          D.CanonicalOstrowskiThresholdCompatible m height := by
  have hRF :=
    isRecordFerrersPath_irrationalRotationRoof_iff
      (α := α) Arot (m := m) (height := height)
  constructor
  · intro R
    have h := hRF.1 R
    exact
      ⟨h.1, h.2.1,
        (D.canonicalPhaseThresholdCompatible_iff_ostrowski Arot).1 h.2.2⟩
  · rintro ⟨A, hm, O⟩
    apply hRF.2
    exact
      ⟨A, hm,
        (D.canonicalPhaseThresholdCompatible_iff_ostrowski Arot).2 O⟩

/--
RecordFerrers を canonical Ostrowski threshold data から直接構成する。

これは arbitrary irrational rotation の全 admissible path が RecordFerrers になるという主張ではない。
Ostrowski threshold law を満たす path だけを構成する。
-/
noncomputable def recordFerrersOfOstrowskiThreshold
    {α : ℝ}
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α)
    {m : ℕ}
    {height : ℕ → ℕ}
    (A : IsAdmissibleRoofPath (irrationalRotationRoof α) m height)
    (hm : 1 < m)
    (O : D.CanonicalOstrowskiThresholdCompatible m height) :
    RecordFerrers (irrationalRotationRoof α) m :=
  recordFerrersOfIrrationalRotation
    Arot A hm
    ((D.canonicalPhaseThresholdCompatible_iff_ostrowski Arot).2 O)

end RotationOstrowskiSystem

namespace RecordFerrers

/--
任意無理回転 roof 上の完成 RecordFerrers は、対応する canonical Ostrowski threshold law を満たす。
-/
theorem ostrowskiThresholdCompatible
    {α : ℝ}
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m)
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α) :
    D.CanonicalOstrowskiThresholdCompatible m R.height := by
  exact
    (D.canonicalCarryCompatible_iff_ostrowski Arot).1
      R.carryCompatible

/--
完成 RecordFerrers の canonical local critical geometry を Ostrowski threshold law から回収する。
-/
theorem localCriticalBlocks_of_ostrowski
    {α : ℝ}
    {m : ℕ}
    (R : RecordFerrers (irrationalRotationRoof α) m)
    (D : RotationOstrowskiSystem α)
    (Arot : IsIrrationalUnitRotation α) :
    LocalRoofCriticalBlocksFrom
      (irrationalRotationRoof α) m R.height canonicalAnchor
      (canonicalRecordLengths (irrationalRotationRoof α) m R.height) := by
  exact
    (D.canonicalOstrowskiThresholdCompatible_iff_localRoofCriticalBlocks
      Arot R.admissible R.one_lt_width).1
      (R.ostrowskiThresholdCompatible D Arot)

end RecordFerrers

end GenericRecordFerrers
end Experimental2
end Collatz3
