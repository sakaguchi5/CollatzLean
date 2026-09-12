import CollatzLean.Collatz3.Bridge.GenericRecordFerrersCollatzOstrowski
import CollatzLean.Collatz3.Bridge.CollatzOstrowskiRecordStability
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.SturmianGraphThresholdBridge
set_option linter.style.longLine false
/-!
# Collatz3 Bridge: actual Sturmian path code と Collatz correction の exact 接続

S6 では arbitrary irrational rotation の RecordFerrers threshold law を
actual Sturmian graph path の `edgeCount` code へ移した。

本ファイルでは `α = collatzLogRotation = log₂(3/2)` に特殊化し、既存の
actual Collatz correction theory と接着する。

重要な分離は維持する。

* pure mechanical / RecordFerrers 側は Sturmian path code の phase threshold、
* actual Collatz 側は initial log phase と正の `+1` correction sum

として扱い、両者を同一視しない。

中心結果は次の二層である。

1. Collatz `RecordFerrers` の canonical threshold lawを generic Sturmian path code だけで特徴付ける。
2. actual finite run の corrected mechanical phase と carry `0/1` stability を
   同じ canonical Sturmian path phase で書く。
-/

namespace Collatz3
open Experimental2
open Experimental2.GenericRecordFerrers
namespace Bridge

namespace BeattyRegularOstrowskiSystem

/--
Collatz regular-Ostrowski system を generic system として読んだ weight-`N` Sturmian path phase は、
既存 horizontal Ostrowski block error の fractional part と exact に一致する。
-/
theorem genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase
    (D : BeattyRegularOstrowskiSystem)
    (N : ℕ) :
    (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
        ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight N) =
      Int.fract (D.horizontalOstrowskiBlockError N) := by
  rw [(D.toGenericRotationOstrowskiSystem).sturmianPathPhase_code N]
  exact D.genericOstrowskiPhase_eq_horizontalOstrowskiBlockErrorPhase N

/--
Collatz `IsRecordFerrersProfile` を、generic actual Sturmian path-code threshold で exact に特徴付ける。

既存 generic Ostrowski threshold theorem と S6 の exact bridge の合成であり、
新しい RecordFerrers 条件は導入しない。
-/
theorem isRecordFerrersProfile_iff_genericCollatzSturmianPathThreshold
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (H : Critical.AdmissibleProfile m) :
    Ferrers.IsRecordFerrersProfile H ↔
      1 < m ∧
        (D.toGenericRotationOstrowskiSystem).CanonicalSturmianPathThresholdCompatible
          m (Critical.profileHeight H.1) := by
  have hOst := D.isRecordFerrersProfile_iff_genericCollatzOstrowskiThreshold H
  have hPath :=
    (D.toGenericRotationOstrowskiSystem).canonicalOstrowskiThresholdCompatible_iff_sturmianPath
      (m := m) (height := Critical.profileHeight H.1)
  constructor
  · intro R
    have h := hOst.1 R
    exact ⟨h.1, hPath.1 h.2⟩
  · rintro ⟨hm, P⟩
    exact hOst.2 ⟨hm, hPath.2 P⟩

/--
完成 Collatz `RecordFerrers` は canonical generic Sturmian path threshold law を満たす。
-/
theorem recordFerrers_genericCollatzSturmianPathThreshold
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    (D.toGenericRotationOstrowskiSystem).CanonicalSturmianPathThresholdCompatible
      m (Critical.profileHeight R.profile.1) := by
  exact
    (D.toGenericRotationOstrowskiSystem).canonicalOstrowskiThresholdCompatible_iff_sturmianPath.1
      (D.recordFerrers_genericCollatzOstrowskiThreshold R)

/--
逆に admissible Collatz profile が generic Sturmian path threshold を満たせば、
既存 `Ferrers.RecordFerrers` を直接構成できる。
-/
def recordFerrersOfGenericCollatzSturmianPathThreshold
    (D : BeattyRegularOstrowskiSystem)
    {m : ℕ}
    (H : Critical.AdmissibleProfile m)
    (hm : 1 < m)
    (P :
      (D.toGenericRotationOstrowskiSystem).CanonicalSturmianPathThresholdCompatible
        m (Critical.profileHeight H.1)) :
    Ferrers.RecordFerrers m :=
  D.recordFerrersOfGenericCollatzOstrowskiThreshold
    H hm
    ((D.toGenericRotationOstrowskiSystem).canonicalOstrowskiThresholdCompatible_iff_sturmianPath.2 P)

end BeattyRegularOstrowskiSystem

end Bridge

namespace Runs

/--
`r` odd steps の actual run を、weight-`r` actual Sturmian path code の mechanical phase と
Collatz correction sum に exact 分解する。
-/
theorem actualLogPhase_eq_sturmianPathMechanicalBlock
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (r : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r) :
    Bridge.collatzLogPhase y =
      Int.fract
        (Bridge.collatzLogPhase x +
          (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
            ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight r) +
          h.logCorrectionSum) := by
  have hOld := h.actualLogPhase_eq_horizontalOstrowskiMechanicalBlock D r hSteps
  rw [D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase r]
  exact hOld

/--
Record-side carry `1` の block は、Sturmian path phase で読んでも、
非負の initial actual phase と correction を加えた後に wrap 側へ留まる。
-/
theorem beattyCarryOne_actualSturmianPathBlock_stable
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (a r : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r)
    (hCarry : Critical.beattyCarry a r = 1) :
    1 ≤
        (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
            ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight a) +
          (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
            ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight r) +
          Bridge.collatzLogPhase x + h.logCorrectionSum ∧
      Bridge.collatzLogPhase y =
        Int.fract
          (Bridge.collatzLogPhase x +
            (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
              ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight r) +
            h.logCorrectionSum) := by
  have hOld :=
    h.beattyCarryOne_actualOstrowskiBlock_stable D a r hSteps hCarry
  simpa only [
    D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase a,
    D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase r
  ] using hOld

/--
Record-side carry `0` block では、actual perturbation が pure non-wrap margin 未満なら、
Sturmian path phase で見ても threshold `1` を越えない。
-/
theorem beattyCarryZero_actualSturmianPathBlock_stable
    (D : Bridge.BeattyRegularOstrowskiSystem)
    (a r : ℕ)
    {w : Word} {x y : ℕ}
    (h : Runs w x y)
    (hSteps : Word.oddSteps w = r)
    (hCarry : Critical.beattyCarry a r = 0)
    (hMargin :
      Bridge.collatzLogPhase x + h.logCorrectionSum <
        1 -
          ((D.toGenericRotationOstrowskiSystem).sturmianPathPhase
              ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight a) +
            (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
              ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight r))) :
    (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
          ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight a) +
        (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
          ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight r) +
        Bridge.collatzLogPhase x + h.logCorrectionSum < 1 ∧
      Bridge.collatzLogPhase y =
        Int.fract
          (Bridge.collatzLogPhase x +
            (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
              ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight r) +
            h.logCorrectionSum) := by
  have hMarginOld :
      Bridge.collatzLogPhase x + h.logCorrectionSum <
        1 -
          (Int.fract (D.horizontalOstrowskiBlockError a) +
            Int.fract (D.horizontalOstrowskiBlockError r)) := by
    simpa only [
      D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase a,
      D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase r
    ] using hMargin
  have hOld :=
    h.beattyCarryZero_actualOstrowskiBlock_stable
      D a r hSteps hCarry hMarginOld
  simpa only [
    D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase a,
    D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase r
  ] using hOld

/--
high orbit 上では correction sum を `r * correctionCap X` で上から押さえ、
Sturmian path phase 側で carry `0` の non-wrap stability を一様判定できる。
-/
theorem beattyCarryZero_actualSturmianPathBlock_stable_of_cap
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
          ((D.toGenericRotationOstrowskiSystem).sturmianPathPhase
              ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight a) +
            (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
              ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight r))) :
    (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
          ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight a) +
        (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
          ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight r) +
        Bridge.collatzLogPhase x + h.logCorrectionSum < 1 ∧
      Bridge.collatzLogPhase y =
        Int.fract
          (Bridge.collatzLogPhase x +
            (D.toGenericRotationOstrowskiSystem).sturmianPathPhase
              ((D.toGenericRotationOstrowskiSystem).sturmianPathCodeOfWeight r) +
            h.logCorrectionSum) := by
  have hMarginOld :
      Bridge.collatzLogPhase x +
          (r : ℝ) * Bridge.collatzLogCorrectionCap X <
        1 -
          (Int.fract (D.horizontalOstrowskiBlockError a) +
            Int.fract (D.horizontalOstrowskiBlockError r)) := by
    simpa only [
      D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase a,
      D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase r
    ] using hMargin
  have hOld :=
    h.beattyCarryZero_actualOstrowskiBlock_stable_of_cap
      D a r X hSteps hCarry hX hAbove hMarginOld
  simpa only [
    D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase a,
    D.genericSturmianPathPhase_eq_horizontalOstrowskiBlockErrorPhase r
  ] using hOld

end Runs
end Collatz3
