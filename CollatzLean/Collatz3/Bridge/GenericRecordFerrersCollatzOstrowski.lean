import CollatzLean.Collatz3.Bridge.GenericRecordFerrersBeatty
import CollatzLean.Collatz3.Bridge.CollatzOstrowskiRecordStability
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.OstrowskiRecordFerrers

/-!
# Collatz3 Bridge: generic irrational-Ostrowski RecordFerrers の Collatz 特殊化

第9段階では、既存 `Ferrers.RecordFerrers` が一般 RecordFerrers の
`Critical.beattyIndex` / `Critical.profileHeight` 特殊化と exact に一致することを示した。
第10--14段階では一般理論を

* lower mechanical phase,
* fractional gauge,
* 任意無理回転 `α ∈ (0,1)`,
* canonical Ostrowski error,
* canonical Ostrowski threshold law

へ拡張した。

このファイルでは、その一般理論を

`α = collatzLogRotation = log₂(3/2)`

へ戻す。

中心は次の二つの exact identification である。

1. `irrationalRotationRoof collatzLogRotation = Critical.beattyIndex`。
2. 既存 `BeattyRegularOstrowskiSystem` を generic `RotationOstrowskiSystem` として読むと、
   generic Ostrowski phase は既存 horizontal block error の fractional part と一致する。

これにより、第14段階だけから Collatz の `IsRecordFerrersProfile` を
canonical generic Ostrowski threshold で特徴付けられる。
最後に既存 `CollatzOstrowskiRecordStability` の threshold predicate と比較し、
旧 Collatz 専用 theorem と新 generic theorem が同じ law を表すことを確認する。

actual Collatz correction / `Runs` の層には触れない。
それらは引き続き Collatz 専用 Bridge に残す。
-/

namespace Collatz3
open Experimental2
open Experimental2.GenericRecordFerrers
namespace Bridge

/--
Collatz の正規化回転角を lifted slope に戻すと `log₂ 3` になる。
-/
theorem one_add_collatzLogRotation_eq_logb_two_three :
    (1 : ℝ) + collatzLogRotation = Real.logb 2 3 := by
  rw [collatzLogRotation_eq_logb_three_sub_one]
  ring

/--
`collatzLogRotation = log₂(3/2)` は generic theory が要求する
irrational open-unit rotation である。

open interval は Beatty roof の irrational slope を fractional gauge へ移した
第11段階の一般定理から得る。
-/
theorem collatzLogRotation_isIrrationalUnitRotation :
    IsIrrationalUnitRotation collatzLogRotation := by
  have hIrr : Irrational collatzLogRotation := by
    simpa [collatzLogRotation] using irrational_logb_two_three_halves
  have hRange :=
    fractionalRoofSlope_mem_openUnitInterval_of_irrational
      beattyIndex_isLowerMechanical_logb_two_three.isRoofSlope
      irrational_logb_two_three
  have hFrac :
      fractionalRoofSlope Critical.beattyIndex (Real.logb 2 3) =
        collatzLogRotation := by
    unfold fractionalRoofSlope
    rw [Critical.beattyIndex_one]
    simpa using collatzLogRotation_eq_logb_three_sub_one.symm
  rw [hFrac] at hRange
  exact ⟨hIrr, hRange.1, hRange.2⟩

/--
任意無理回転から第12段階で作った canonical lifted roof は、
Collatz 回転角では `Critical.beattyIndex` そのものになる。

従って generic theory と Collatz theory の ambient roof は単なる同型ではなく
関数として exact に一致する。
-/
theorem irrationalRotationRoof_collatzLogRotation_eq_beattyIndex :
    irrationalRotationRoof collatzLogRotation = Critical.beattyIndex := by
  funext n
  calc
    irrationalRotationRoof collatzLogRotation n =
        n + ⌊(n : ℝ) * collatzLogRotation⌋₊ := by
      exact irrationalRotationRoof_eq collatzLogRotation n
    _ = n + normalizeRoof Critical.beattyIndex n := by
      simp only [normalizeBeatty_eq_natFloor_logb_three_halves,
        collatzLogRotation]
    _ = Critical.beattyIndex n := by
      have h := beattyIndex_hasUnitCarry.eq_linear_add_normalizeRoof n
      rw [Critical.beattyIndex_one] at h
      simpa using h.symm

namespace BeattyRegularOstrowskiSystem

/--
既存 Collatz `BeattyRegularOstrowskiSystem` を、第13段階の
任意回転 `RotationOstrowskiSystem` として忘却する canonical map。

continued-fraction lattice 自体は同じ `conv` を使う。
必要なのは direct slope

`1 + collatzLogRotation = log₂ 3`

の書き換えだけである。
-/
noncomputable def toGenericRotationOstrowskiSystem
    (D : BeattyRegularOstrowskiSystem) :
    RotationOstrowskiSystem collatzLogRotation where
  conv := D.conv
  lowerBracket := by
    intro n hn
    rw [one_add_collatzLogRotation_eq_logb_two_three]
    exact D.lowerBracket n hn
  upperBracket := by
    intro n hn
    rw [one_add_collatzLogRotation_eq_logb_two_three]
    exact D.upperBracket n hn

/--
Collatz system を generic system として読んだ canonical Ostrowski phase は、
既存 horizontal canonical block error の fractional part と exact に一致する。

二つの実装の内部 digit normalization を直接比較する必要はない。
両者が同じ pure rotation `N * collatzLogRotation` の fractional part を表すことから従う。
-/
theorem genericOstrowskiPhase_eq_horizontalOstrowskiBlockErrorPhase
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ) :
    (D.toGenericRotationOstrowskiSystem).ostrowskiPhase N =
      Int.fract (D.horizontalOstrowskiBlockError N) := by
  calc
    (D.toGenericRotationOstrowskiSystem).ostrowskiPhase N =
        Int.fract ((N : ℝ) * collatzLogRotation) :=
      (D.toGenericRotationOstrowskiSystem).ostrowskiPhase_eq_fract_mul_rotation N
    _ = Int.fract (D.horizontalOstrowskiBlockError N) :=
      D.fract_mul_rotation_eq_fract_blockError N

/--
既存の normalized Beatty mechanical phase と、第14段階の generic Ostrowski phase も
exact に同じ座標である。
-/
theorem normalizedBeattyMechanicalPhase_eq_genericOstrowskiPhase
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ) :
    roofPhase (normalizeRoof Critical.beattyIndex)
        collatzLogRotation N =
      (D.toGenericRotationOstrowskiSystem).ostrowskiPhase N := by
  calc
    roofPhase (normalizeRoof Critical.beattyIndex)
        collatzLogRotation N =
      Int.fract (D.horizontalOstrowskiBlockError N) :=
        D.normalizedBeattyMechanicalPhase_eq_fract_horizontalOstrowskiBlockError N
    _ = (D.toGenericRotationOstrowskiSystem).ostrowskiPhase N :=
      (D.genericOstrowskiPhase_eq_horizontalOstrowskiBlockErrorPhase N).symm

/--
第9段階の Beatty specialization と第14段階の arbitrary-rotation theorem だけから、
Collatz `IsRecordFerrersProfile` を generic canonical Ostrowski threshold で特徴付ける。

この theorem の証明では既存 Collatz 専用
`isRecordFerrersProfile_iff_canonicalOstrowskiThresholdCompatible` を使わない。
従って generic theory から Collatz law を本当に再回収した形になっている。
-/
theorem isRecordFerrersProfile_iff_genericCollatzOstrowskiThreshold
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (H : Critical.AdmissibleProfile m) :
    Ferrers.IsRecordFerrersProfile H ↔
      1 < m ∧
        (D.toGenericRotationOstrowskiSystem).CanonicalOstrowskiThresholdCompatible
            m (Critical.profileHeight H.1) := by
  let DG : RotationOstrowskiSystem collatzLogRotation :=
    D.toGenericRotationOstrowskiSystem
  have Arot : IsIrrationalUnitRotation collatzLogRotation :=
    collatzLogRotation_isIrrationalUnitRotation
  have hBeatty :=
    isRecordFerrersProfile_iff_genericBeattyRecordFerrersPath H
  have hOst :=
    DG.isRecordFerrersPath_iff_ostrowski
      Arot (m := m) (height := Critical.profileHeight H.1)
  constructor
  · intro RF
    have RBeatty :
        IsRecordFerrersPath
          Critical.beattyIndex m (Critical.profileHeight H.1) :=
      hBeatty.1 RF
    have RRotation :
        IsRecordFerrersPath
          (irrationalRotationRoof collatzLogRotation)
          m (Critical.profileHeight H.1) := by
      rw [irrationalRotationRoof_collatzLogRotation_eq_beattyIndex]
      exact RBeatty
    have h := hOst.1 RRotation
    exact ⟨h.2.1, h.2.2⟩
  · rintro ⟨hm, O⟩
    have ABeatty :
        IsAdmissibleRoofPath
          Critical.beattyIndex m (Critical.profileHeight H.1) :=
      admissibleProfile_isExperimental2RoofPath H.2
    have ARotation :
        IsAdmissibleRoofPath
          (irrationalRotationRoof collatzLogRotation)
          m (Critical.profileHeight H.1) := by
      rw [irrationalRotationRoof_collatzLogRotation_eq_beattyIndex]
      exact ABeatty
    have RRotation :
        IsRecordFerrersPath
          (irrationalRotationRoof collatzLogRotation)
          m (Critical.profileHeight H.1) :=
      hOst.2 ⟨ARotation, hm, O⟩
    have RBeatty :
        IsRecordFerrersPath
          Critical.beattyIndex m (Critical.profileHeight H.1) := by
      rw [← irrationalRotationRoof_collatzLogRotation_eq_beattyIndex]
      exact RRotation
    exact hBeatty.2 RBeatty

/--
幅 `1 < m` を固定すると、既存 Collatz 専用 threshold predicate と
第14段階の generic canonical Ostrowski threshold predicate は exact に同値。

これにより旧実装と新 generic 実装が同じ RecordFerrers local law を読んでいることが確定する。
-/
theorem canonicalOstrowskiThresholdCompatible_legacy_iff_generic
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (H : Critical.AdmissibleProfile m)
    (hm : 1 < m) :
    CanonicalOstrowskiThresholdCompatibleFrom
        D H.1 Critical.initialRoofAnchor (Ferrers.initialRecordCuts H.1) ↔
      (D.toGenericRotationOstrowskiSystem).CanonicalOstrowskiThresholdCompatible
          m (Critical.profileHeight H.1) := by
  constructor
  · intro L
    have RF : Ferrers.IsRecordFerrersProfile H :=
      (D.isRecordFerrersProfile_iff_canonicalOstrowskiThresholdCompatible H).2
        ⟨hm, L⟩
    exact
      ((D.isRecordFerrersProfile_iff_genericCollatzOstrowskiThreshold H).1 RF).2
  · intro G
    have RF : Ferrers.IsRecordFerrersProfile H :=
      (D.isRecordFerrersProfile_iff_genericCollatzOstrowskiThreshold H).2
        ⟨hm, G⟩
    exact
      ((D.isRecordFerrersProfile_iff_canonicalOstrowskiThresholdCompatible H).1 RF).2

/--
完成 Collatz `RecordFerrers` は、第14段階の generic canonical Ostrowski threshold law を満たす。

これは stage 15 の実用 wrapper。以後 generic obstruction theorem を Collatz RecordFerrers へ
適用するとき、旧 threshold structure を経由する必要がない。
-/
theorem recordFerrers_genericCollatzOstrowskiThreshold
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    (D.toGenericRotationOstrowskiSystem).CanonicalOstrowskiThresholdCompatible
        m (Critical.profileHeight R.profile.1) := by
  exact
    ((D.isRecordFerrersProfile_iff_genericCollatzOstrowskiThreshold R.profile).1 R.2).2

/--
逆に admissible Collatz profile が generic Collatz-Ostrowski threshold を満たせば、
既存 `Ferrers.RecordFerrers` を直接構成できる。
-/
def recordFerrersOfGenericCollatzOstrowskiThreshold
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (H : Critical.AdmissibleProfile m)
    (hm : 1 < m)
    (O :
      (D.toGenericRotationOstrowskiSystem).CanonicalOstrowskiThresholdCompatible
          m (Critical.profileHeight H.1)) :
    Ferrers.RecordFerrers m :=
  ⟨H,
    (D.isRecordFerrersProfile_iff_genericCollatzOstrowskiThreshold H).2
      ⟨hm, O⟩⟩

end BeattyRegularOstrowskiSystem

end Bridge
end Collatz3
