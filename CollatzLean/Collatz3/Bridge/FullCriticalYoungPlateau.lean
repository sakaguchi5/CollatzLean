import CollatzLean.Collatz3.Bridge.FullCriticalYoung
import CollatzLean.Collatz3.Bridge.GenericRecordFerrersBeatty
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.RecordFerrersPlateau

/-!
# Collatz3 Bridge: FullCriticalYoung から RecordFerrers plateau への coarse-graining

full critical Young object は finite admissible profile を完全に保持する。
一方、RecordFerrers の `plateauWidthDropCode` は

* deterministic canonical record lengths,
* 各 canonical block の rank drop

だけを保存する coarse な Young/Frobenius code である。

本ファイルではこの忘却写像を明示する。

`FullCriticalYoung`
  -> `canonicalRecordLengths`
  -> `(width, rankDrop)` plateau code

という合成を primitive とし、RecordFerrers 条件を満たす場合には
既存 generic Beatty specialization の `plateauWidthDropCode` と exact に一致することを示す。

これにより、95 / 175 型の

* full Young 座標では異なる、
* canonical record lengths が同じなら coarse plateau code では同じ、

という現象を一般 theorem として切り分ける。
-/

namespace Collatz3
namespace Bridge

open Experimental2

namespace FullCriticalYoung

/--
full critical Young object から deterministic canonical record lengths だけを読む。
ここが最初の情報忘却段階。
-/
def coarseLengths
    {m : ℕ}
    (Y : FullCriticalYoung m) : List ℕ :=
  Ferrers.canonicalRecordLengths Y.1

/--
full critical Young object から得る coarse `(plateau width, rank drop)` code。
RecordFerrers law 自体は定義には埋め込まない。

後段で RecordFerrers を仮定したとき、既存 `plateauWidthDropCode` と一致する。
-/
def coarseWidthDropCode
    {m : ℕ}
    (Y : FullCriticalYoung m) :
    Experimental2.YoungFerrersRestricted.WidthDropCode :=
  Experimental2.YoungFerrersRestricted.widthDropCodeFromLengths
    Critical.beattyIndex m (coarseLengths Y)

/-- coarse code の width 列は canonical record lengths そのもの。 -/
@[simp] theorem coarseWidthDropCode_widths
    {m : ℕ}
    (Y : FullCriticalYoung m) :
    Experimental2.YoungFerrersRestricted.widthsOfCode
        (coarseWidthDropCode Y) =
      coarseLengths Y := by
  simp [coarseWidthDropCode]

/-- coarse code の drop 列は各 canonical width の Beatty rank drop。 -/
@[simp] theorem coarseWidthDropCode_drops
    {m : ℕ}
    (Y : FullCriticalYoung m) :
    Experimental2.YoungFerrersRestricted.dropsOfCode
        (coarseWidthDropCode Y) =
      (coarseLengths Y).map
        (Experimental2.GenericRecordFerrers.rankDropNat
          Critical.beattyIndex m) := by
  simp [coarseWidthDropCode]

/-- RecordFerrers から underlying full critical Young object を忘却する。 -/
def ofRecordFerrers
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) : FullCriticalYoung m :=
  R.profile

/--
coarse map は既存 generic Beatty RecordFerrers の `plateauWidthDropCode` と exact に一致する。
これが今回の coarse-graining bridge の中心定理。
-/
theorem coarseWidthDropCode_ofRecordFerrers_eq_plateauWidthDropCode
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    coarseWidthDropCode (ofRecordFerrers R) =
      (recordFerrersToGenericBeatty R).plateauWidthDropCode := by
  change
    Experimental2.YoungFerrersRestricted.widthDropCodeFromLengths
        Critical.beattyIndex m
        (Ferrers.canonicalRecordLengths R.profile.1) =
      Experimental2.YoungFerrersRestricted.widthDropCodeFromLengths
        Critical.beattyIndex m
        (Experimental2.GenericRecordFerrers.canonicalRecordLengths
          Critical.beattyIndex m
          (Critical.profileHeight R.profile.1))
  rw [genericCanonicalRecordLengths_beatty_eq]

/--
RecordFerrers 上では coarse code の総横幅は `m-1`。
既存 plateau theorem を bridge 経由で輸送する。
-/
theorem coarseWidthDropCode_width_ofRecordFerrers
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    Experimental2.YoungFerrersRestricted.codeWidth
        (coarseWidthDropCode (ofRecordFerrers R)) =
      m - 1 := by
  rw [coarseWidthDropCode_ofRecordFerrers_eq_plateauWidthDropCode]
  exact
    Experimental2.GenericRecordFerrers.RecordFerrers.plateauCode_width
      (recordFerrersToGenericBeatty R)

/--
canonical record lengths が同じ full critical Young object は、
coarse plateau code では必ず同一視される。

これは 95 / 175 で観察した情報損失を一般化した theorem。
-/
theorem coarseWidthDropCode_eq_of_coarseLengths_eq
    {m : ℕ}
    {Y Z : FullCriticalYoung m}
    (h : coarseLengths Y = coarseLengths Z) :
    coarseWidthDropCode Y = coarseWidthDropCode Z := by
  unfold coarseWidthDropCode
  rw [h]

/--
同じ canonical record lengths を持つ二つの RecordFerrers は、
generic Beatty 側の `plateauWidthDropCode` でも一致する。
full profile の相違はこの coarse code からは復元できない。
-/
theorem plateauWidthDropCode_eq_of_canonicalRecordLengths_eq
    {m : ℕ}
    {R S : Ferrers.RecordFerrers m}
    (h :
      Ferrers.canonicalRecordLengths R.profile.1 =
        Ferrers.canonicalRecordLengths S.profile.1) :
    (recordFerrersToGenericBeatty R).plateauWidthDropCode =
      (recordFerrersToGenericBeatty S).plateauWidthDropCode := by
  rw [
    ← coarseWidthDropCode_ofRecordFerrers_eq_plateauWidthDropCode R,
    ← coarseWidthDropCode_ofRecordFerrers_eq_plateauWidthDropCode S
  ]
  apply coarseWidthDropCode_eq_of_coarseLengths_eq
  exact h

end FullCriticalYoung
end Bridge
end Collatz3
