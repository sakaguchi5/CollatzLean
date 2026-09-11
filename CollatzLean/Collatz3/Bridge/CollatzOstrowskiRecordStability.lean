import CollatzLean.Collatz3.Bridge.CollatzLogPhaseMechanical
import CollatzLean.Collatz3.Bridge.CollatzOstrowskiBlockStability
import CollatzLean.Collatz3.Ferrers.RecordFerrers

import Mathlib.Tactic.Linarith

/-!
# Collatz3 Bridge: Ostrowski block stability と RecordFerrers の exact 接続

このファイルでは、horizontal canonical Ostrowski block の log-phase 理論を
RecordFerrers の exact carry law へ接続する。

層は意図的に四つへ分ける。

1. Ostrowski block error と normalized Beatty mechanical phase の exact 同定。
2. mechanical threshold と `beattyCarry` の exact 同値。
3. canonical RecordFerrers carry law を Ostrowski threshold 語彙へ exact に翻訳。
4. actual Collatz correction を加えても threshold の側が保存される条件。

重要な分離として、actual log phase と pure mechanical phase は同一視しない。
actual 側では既証明の corrected mechanical phase law を用い、
RecordFerrers 側では pure mechanical carry threshold だけを読む。
-/

namespace Collatz3
open Experimental2
namespace Bridge

/-! ## 第1層: Ostrowski block error = normalized mechanical phase -/

namespace BeattyRegularOstrowskiSystem

/--
任意 block length `r` の normalized Beatty mechanical phase は、
horizontal canonical Ostrowski composite error の fractional part そのもの。

`r * log₂(3/2)` の整数部分は canonical Ostrowski decomposition に吸収される。
-/
theorem normalizedBeattyMechanicalPhase_eq_fract_horizontalOstrowskiBlockError
    (D : BeattyRegularOstrowskiSystem)
    (r : ℕ) :
    Experimental2.roofPhase
        (Experimental2.normalizeRoof Critical.beattyIndex)
        collatzLogRotation r =
      Int.fract (D.horizontalOstrowskiBlockError r) := by
  rw [normalizedBeattyLogPhase_eq_fract_rotation]
  exact D.fract_mul_rotation_eq_fract_blockError r

/--
正規化 Beatty roof は `collatzLogRotation = log₂(3/2)` の lower mechanical roof。
後続の carry threshold で毎回 slope の書き換えをしないための公開 wrapper。
-/
theorem normalizeBeatty_isLowerMechanical_collatzLogRotation :
    Experimental2.IsLowerMechanicalRoof
      (Experimental2.normalizeRoof Critical.beattyIndex)
      collatzLogRotation := by
  simpa [collatzLogRotation] using
    normalizeBeatty_isLowerMechanical_logb_three_halves

/-! ## 第2層: Ostrowski threshold = Beatty carry -/

/--
Beatty carry `1` は、二つの canonical Ostrowski block phase の和が
lower mechanical threshold `1` に到達することと exact に同値。

anchor `a` 自体も一つの block length と見て canonical horizontal Ostrowski 展開するため、
式は完全に Ostrowski error の fractional part だけで書ける。
-/
theorem beattyCarry_eq_one_iff_horizontalOstrowski_wrap
    (D : BeattyRegularOstrowskiSystem)
    (a r : ℕ) :
    Critical.beattyCarry a r = 1 ↔
      1 ≤
        Int.fract (D.horizontalOstrowskiBlockError a) +
          Int.fract (D.horizontalOstrowskiBlockError r) := by
  have U :
      Experimental2.HasUnitCarry
        (Experimental2.normalizeRoof Critical.beattyIndex) :=
    beattyIndex_hasUnitCarry.normalizeRoof_hasUnitCarry
  have h :=
    Experimental2.carry_eq_one_iff_lowerPhase_wrap
      U normalizeBeatty_isLowerMechanical_collatzLogRotation a r
  have hCarryEq :
      Experimental2.roofCarry
          (Experimental2.normalizeRoof Critical.beattyIndex) a r =
        Critical.beattyCarry a r := by
    calc
      Experimental2.roofCarry
          (Experimental2.normalizeRoof Critical.beattyIndex) a r =
          Experimental2.roofCarry Critical.beattyIndex a r :=
        beattyIndex_hasUnitCarry.roofCarry_normalizeRoof_eq a r
      _ = Critical.beattyCarry a r :=
        experimental2_roofCarry_beattyIndex_eq a r
  rw [hCarryEq] at h
  rw [
    normalizedBeattyMechanicalPhase_eq_fract_horizontalOstrowskiBlockError D a,
    normalizedBeattyMechanicalPhase_eq_fract_horizontalOstrowskiBlockError D r
  ] at h
  exact h

/--
Beatty carry `0` は、二つの canonical Ostrowski block phase の和が
strict non-wrap 側にあることと exact に同値。

carry が `0` または `1` の二値であることと前 theorem だけから導く。
-/
theorem beattyCarry_eq_zero_iff_horizontalOstrowski_nonwrap
    (D : BeattyRegularOstrowskiSystem)
    (a r : ℕ) :
    Critical.beattyCarry a r = 0 ↔
      Int.fract (D.horizontalOstrowskiBlockError a) +
          Int.fract (D.horizontalOstrowskiBlockError r) < 1 := by
  constructor
  · intro hZero
    have hNotOne : Critical.beattyCarry a r ≠ 1 := by omega
    have hNotWrap :
        ¬ 1 ≤
          Int.fract (D.horizontalOstrowskiBlockError a) +
            Int.fract (D.horizontalOstrowskiBlockError r) := by
      intro hWrap
      apply hNotOne
      exact (D.beattyCarry_eq_one_iff_horizontalOstrowski_wrap a r).2 hWrap
    exact lt_of_not_ge hNotWrap
  · intro hNonwrap
    rcases Critical.beattyCarry_eq_zero_or_one a r with hZero | hOne
    · exact hZero
    · have hWrap :=
        (D.beattyCarry_eq_one_iff_horizontalOstrowski_wrap a r).1 hOne
      linarith

/--
Record local geometry で禁止される
`premature roof return + carry 1` を、Ostrowski threshold だけで書いた薄い predicate。

新しい carry を定義しているのではなく、既存 `beattyCarry` の exact threshold 表現である。
-/
def NoPrematureOstrowskiWrapRoofReturn
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (h : Critical.Profile m)
    (a r : ℕ) : Prop :=
  ∀ j : ℕ,
    0 < j →
    j < r →
    ¬ (Critical.IsRoofCut h (a + j) ∧
      1 ≤
        Int.fract (D.horizontalOstrowskiBlockError a) +
          Int.fract (D.horizontalOstrowskiBlockError j))

/--
既存の `NoPrematureCarryOneRoofReturn` と Ostrowski threshold 版は exact に同値。
-/
theorem noPrematureCarryOneRoofReturn_iff_noPrematureOstrowskiWrapRoofReturn
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    {h : Critical.Profile m}
    (a r : ℕ) :
    Critical.NoPrematureCarryOneRoofReturn h a r ↔
      NoPrematureOstrowskiWrapRoofReturn D h a r := by
  constructor
  · intro C j hjPos hjLt hBad
    apply C j hjPos hjLt
    exact
      ⟨hBad.1,
        (D.beattyCarry_eq_one_iff_horizontalOstrowski_wrap a j).2 hBad.2⟩
  · intro C j hjPos hjLt hBad
    apply C j hjPos hjLt
    exact
      ⟨hBad.1,
        (D.beattyCarry_eq_one_iff_horizontalOstrowski_wrap a j).1 hBad.2⟩

/-! ## 第3層: canonical RecordFerrers carry law の Ostrowski 化 -/

/--
canonical record cut chain に沿う exact threshold compatibility。

`Ferrers.CanonicalCarryCompatibleFrom` の carry 語彙を一切保存せず、

* 各 block interior では premature Ostrowski wrap + roof return を禁止、
* terminal block では Ostrowski phase sum を strict non-wrap に置く

という pure threshold 条件だけを再帰的に読む。
-/
def CanonicalOstrowskiThresholdCompatibleFrom
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (h : Critical.Profile m) : ℕ → List ℕ → Prop
  | a, [] =>
      NoPrematureOstrowskiWrapRoofReturn D h a (m - a) ∧
        Int.fract (D.horizontalOstrowskiBlockError a) +
            Int.fract (D.horizontalOstrowskiBlockError (m - a)) < 1
  | a, k :: ks =>
      NoPrematureOstrowskiWrapRoofReturn D h a (k - a) ∧
        CanonicalOstrowskiThresholdCompatibleFrom D h k ks

/--
canonical carry compatibility と canonical Ostrowski threshold compatibility は exact に同値。

この theorem が RecordFerrers の定義層と Ostrowski phase 層を直接接着する。
-/
theorem canonicalCarryCompatibleFrom_iff_canonicalOstrowskiThresholdCompatibleFrom
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    {h : Critical.Profile m} :
    ∀ (a : ℕ) (cuts : List ℕ),
      Ferrers.CanonicalCarryCompatibleFrom h a cuts ↔
        CanonicalOstrowskiThresholdCompatibleFrom D h a cuts
  | a, [] => by
      simp only [
        Ferrers.CanonicalCarryCompatibleFrom,
        CanonicalOstrowskiThresholdCompatibleFrom
      ]
      constructor
      · rintro ⟨hNo, hZero⟩
        exact
          ⟨(D.noPrematureCarryOneRoofReturn_iff_noPrematureOstrowskiWrapRoofReturn
              a (m - a)).1 hNo,
            (D.beattyCarry_eq_zero_iff_horizontalOstrowski_nonwrap
              a (m - a)).1 hZero⟩
      · rintro ⟨hNo, hNonwrap⟩
        exact
          ⟨(D.noPrematureCarryOneRoofReturn_iff_noPrematureOstrowskiWrapRoofReturn
              a (m - a)).2 hNo,
            (D.beattyCarry_eq_zero_iff_horizontalOstrowski_nonwrap
              a (m - a)).2 hNonwrap⟩
  | a, k :: ks => by
      simp only [
        Ferrers.CanonicalCarryCompatibleFrom,
        CanonicalOstrowskiThresholdCompatibleFrom
      ]
      have hTail :=
        canonicalCarryCompatibleFrom_iff_canonicalOstrowskiThresholdCompatibleFrom
          D (m := m) (h := h) k ks
      constructor
      · rintro ⟨hNo, hRest⟩
        exact
          ⟨(D.noPrematureCarryOneRoofReturn_iff_noPrematureOstrowskiWrapRoofReturn
              a (k - a)).1 hNo,
            hTail.1 hRest⟩
      · rintro ⟨hNo, hRest⟩
        exact
          ⟨(D.noPrematureCarryOneRoofReturn_iff_noPrematureOstrowskiWrapRoofReturn
              a (k - a)).2 hNo,
            hTail.2 hRest⟩

/--
真の `RecordFerrers` は、その deterministic `initialRecordCuts` 上で
canonical Ostrowski threshold compatibility を自動的に満たす。
-/
theorem recordFerrers_canonicalOstrowskiThresholdCompatible
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    CanonicalOstrowskiThresholdCompatibleFrom
      D R.profile.1 Critical.initialRoofAnchor
        (Ferrers.initialRecordCuts R.profile.1) := by
  exact
    (D.canonicalCarryCompatibleFrom_iff_canonicalOstrowskiThresholdCompatibleFrom
      Critical.initialRoofAnchor
      (Ferrers.initialRecordCuts R.profile.1)).1
      R.carryCompatible

/--
`IsRecordFerrersProfile` 自体を Ostrowski threshold 語彙へ exact に書き換える。

従って RecordFerrers の local law は、admissibility と `1 < m` を固定すれば
canonical Ostrowski threshold compatibility と同値である。
-/
theorem isRecordFerrersProfile_iff_canonicalOstrowskiThresholdCompatible
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (H : Critical.AdmissibleProfile m) :
    Ferrers.IsRecordFerrersProfile H ↔
      1 < m ∧
        CanonicalOstrowskiThresholdCompatibleFrom
          D H.1 Critical.initialRoofAnchor
            (Ferrers.initialRecordCuts H.1) := by
  change
    (1 < m ∧
      Ferrers.CanonicalCarryCompatibleFrom
        H.1 Critical.initialRoofAnchor (Ferrers.initialRecordCuts H.1)) ↔ _
  constructor
  · rintro ⟨hm, hCarry⟩
    exact
      ⟨hm,
        (D.canonicalCarryCompatibleFrom_iff_canonicalOstrowskiThresholdCompatibleFrom
          Critical.initialRoofAnchor (Ferrers.initialRecordCuts H.1)).1 hCarry⟩
  · rintro ⟨hm, hThreshold⟩
    exact
      ⟨hm,
        (D.canonicalCarryCompatibleFrom_iff_canonicalOstrowskiThresholdCompatibleFrom
          Critical.initialRoofAnchor (Ferrers.initialRecordCuts H.1)).2 hThreshold⟩

/--
Admissible profile と canonical Ostrowski threshold compatibility から
直接 `RecordFerrers` を構成する逆向き wrapper。
-/
def recordFerrersOfCanonicalOstrowskiThresholdCompatible
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (H : Critical.AdmissibleProfile m)
    (hm : 1 < m)
    (C : CanonicalOstrowskiThresholdCompatibleFrom
      D H.1 Critical.initialRoofAnchor (Ferrers.initialRecordCuts H.1)) :
    Ferrers.RecordFerrers m :=
  Ferrers.RecordFerrers.ofCanonicalCarry H hm
    ((D.canonicalCarryCompatibleFrom_iff_canonicalOstrowskiThresholdCompatibleFrom
      Critical.initialRoofAnchor (Ferrers.initialRecordCuts H.1)).2 C)

end BeattyRegularOstrowskiSystem

end Bridge

/-! ## 第4層: actual Collatz correction を加えた threshold-side stability -/

namespace Runs

/--
`r` odd steps の actual run は、pure mechanical block phase を
canonical Ostrowski composite error の fractional part で exact に書ける。

これは actual phase と pure mechanical phaseを同一視せず、
initial actual phase と correction sum を明示的に残した式である。
-/
theorem actualLogPhase_eq_horizontalOstrowskiMechanicalBlock
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (r : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r) :
    Bridge.collatzLogPhase y =
      Int.fract
        (Bridge.collatzLogPhase x +
          Int.fract (D.horizontalOstrowskiBlockError r) +
          h.logCorrectionSum) := by
  have hMechanical :=
    Bridge.actualLogPhase_eq_correctedMechanicalPhase h
  rw [hSteps] at hMechanical
  rw [
    D.normalizedBeattyMechanicalPhase_eq_fract_horizontalOstrowskiBlockError r
  ] at hMechanical
  exact hMechanical

/--
Record-side pure threshold が carry `1` 側なら、
非負の initial actual phase と Collatz correction を加えても wrap 側は保存される。

同時に actual endpoint phase の exact corrected-mechanical 表示も返す。
-/
theorem beattyCarryOne_actualOstrowskiBlock_stable
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (a r : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r)
    (hCarry : Critical.beattyCarry a r = 1) :
    1 ≤
        Int.fract (D.horizontalOstrowskiBlockError a) +
          Int.fract (D.horizontalOstrowskiBlockError r) +
          Bridge.collatzLogPhase x + h.logCorrectionSum ∧
      Bridge.collatzLogPhase y =
        Int.fract
          (Bridge.collatzLogPhase x +
            Int.fract (D.horizontalOstrowskiBlockError r) +
            h.logCorrectionSum) := by
  constructor
  · have hPure :=
      (D.beattyCarry_eq_one_iff_horizontalOstrowski_wrap a r).1 hCarry
    have hPhaseNonneg := (Bridge.collatzLogPhase_mem_Ico x).1
    have hCorrectionNonneg := h.logCorrectionSum_nonneg
    linarith
  · exact h.actualLogPhase_eq_horizontalOstrowskiMechanicalBlock D r hSteps

/--
Record-side carry `0` の block について、initial actual phase と correction の総和が
pure non-wrap margin より小さければ、actual perturbation 後も threshold `1` を越えない。

actual endpoint phase の exact corrected-mechanical 表示も同時に返す。
-/
theorem beattyCarryZero_actualOstrowskiBlock_stable
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (a r : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r)
    (hCarry : Critical.beattyCarry a r = 0)
    (hMargin :
      Bridge.collatzLogPhase x + h.logCorrectionSum <
        1 -
          (Int.fract (D.horizontalOstrowskiBlockError a) +
            Int.fract (D.horizontalOstrowskiBlockError r))) :
    Int.fract (D.horizontalOstrowskiBlockError a) +
          Int.fract (D.horizontalOstrowskiBlockError r) +
          Bridge.collatzLogPhase x + h.logCorrectionSum < 1 ∧
      Bridge.collatzLogPhase y =
        Int.fract
          (Bridge.collatzLogPhase x +
            Int.fract (D.horizontalOstrowskiBlockError r) +
            h.logCorrectionSum) := by
  have hPure :=
    (D.beattyCarry_eq_zero_iff_horizontalOstrowski_nonwrap a r).1 hCarry
  constructor
  · linarith
  · exact h.actualLogPhase_eq_horizontalOstrowskiMechanicalBlock D r hSteps

/--
high orbit 上では actual correction sum を `r * correctionCap X` で置き換えて、
Record-side carry `0` の non-wrap stability を一様に判定できる。
-/
theorem beattyCarryZero_actualOstrowskiBlock_stable_of_cap
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (a r X : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r)
    (hCarry : Critical.beattyCarry a r = 0)
    (hX : 0 < X)
    (hAbove : AllStartsAtLeast X w x)
    (hMargin :
      Bridge.collatzLogPhase x +
          (r : ℝ) * Bridge.collatzLogCorrectionCap X <
        1 -
          (Int.fract (D.horizontalOstrowskiBlockError a) +
            Int.fract (D.horizontalOstrowskiBlockError r))) :
    Int.fract (D.horizontalOstrowskiBlockError a) +
          Int.fract (D.horizontalOstrowskiBlockError r) +
          Bridge.collatzLogPhase x + h.logCorrectionSum < 1 ∧
      Bridge.collatzLogPhase y =
        Int.fract
          (Bridge.collatzLogPhase x +
            Int.fract (D.horizontalOstrowskiBlockError r) +
            h.logCorrectionSum) := by
  have hCorrection :=
    h.logCorrectionSum_le_steps_mul_cap hX hAbove
  rw [hSteps] at hCorrection
  have hStrict :
      Bridge.collatzLogPhase x + h.logCorrectionSum <
        1 -
          (Int.fract (D.horizontalOstrowskiBlockError a) +
            Int.fract (D.horizontalOstrowskiBlockError r)) := by
    linarith
  exact
    h.beattyCarryZero_actualOstrowskiBlock_stable
      D a r hSteps hCarry hStrict

end Runs
end Collatz3
