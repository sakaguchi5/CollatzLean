import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.RecordFerrersPlateau

/-!
# Collatz3 Experimental2: plateau 座標における Young 共役

Ferrers/Young 図形を plateau の

`(横幅 r_i, successive drop d_i)`

で読むと、図形の転置では

* 新しい横幅 = 旧 successive drop、
* 新しい successive drop = 旧横幅、
* block の順序は反転

となる。

このファイルではこの座標変換を `conjugateWidthDropCode` として切り出し、
二回適用すると元へ戻る involution と、幅/高さの交換を exact に証明する。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- `(width, drop)` を交換し、block 順序を反転する Young 共役座標。 -/
def conjugateWidthDropCode (c : WidthDropCode) : WidthDropCode :=
  (c.map (fun p => (p.2, p.1))).reverse

/-- 共役後の plateau widths は元の drop 列の逆順。 -/
theorem widthsOfCode_conjugate
    (c : WidthDropCode) :
    widthsOfCode (conjugateWidthDropCode c) =
      (dropsOfCode c).reverse := by
  simp [conjugateWidthDropCode, widthsOfCode, dropsOfCode,
    List.map_reverse, List.map_map, Function.comp_def]

/-- 共役後の successive drops は元の width 列の逆順。 -/
theorem dropsOfCode_conjugate
    (c : WidthDropCode) :
    dropsOfCode (conjugateWidthDropCode c) =
      (widthsOfCode c).reverse := by
  simp [conjugateWidthDropCode, widthsOfCode, dropsOfCode,
    List.map_reverse, List.map_map, Function.comp_def]

/-- 共役は横幅と全縦高を交換する。 -/
theorem codeWidth_conjugate
    (c : WidthDropCode) :
    codeWidth (conjugateWidthDropCode c) = codeDropSum c := by
  simp [codeWidth, codeDropSum, widthsOfCode_conjugate,
    List.sum_reverse]

/-- 共役後の全 drop は元の横幅に等しい。 -/
theorem codeDropSum_conjugate
    (c : WidthDropCode) :
    codeDropSum (conjugateWidthDropCode c) = codeWidth c := by
  simp [codeWidth, codeDropSum, dropsOfCode_conjugate,
    List.sum_reverse]

/-- plateau 座標での Young 共役は involution。 -/
@[simp] theorem conjugateWidthDropCode_involutive
    (c : WidthDropCode) :
    conjugateWidthDropCode (conjugateWidthDropCode c) = c := by
  simp [conjugateWidthDropCode, List.map_reverse, List.map_map,
    Function.comp_def]

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- RecordFerrers rank-envelope の plateau code を Young 共役座標へ移す。 -/
def conjugatePlateauCode
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) : WidthDropCode :=
  conjugateWidthDropCode R.plateauWidthDropCode

/--
共役側の plateau widths は、元 RecordFerrers の rank-drop 列の逆順。
-/
theorem conjugatePlateauWidths_eq_reverse_rankDrops
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    widthsOfCode R.conjugatePlateauCode =
      ((canonicalRecordLengths β m R.height).map (rankDropNat β m)).reverse := by
  rw [conjugatePlateauCode, widthsOfCode_conjugate]
  simp

/--
共役側の successive drops は、元 canonical record lengths の逆順。
-/
theorem conjugatePlateauDrops_eq_reverse_recordLengths
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    dropsOfCode R.conjugatePlateauCode =
      (canonicalRecordLengths β m R.height).reverse := by
  rw [conjugatePlateauCode, dropsOfCode_conjugate]
  simp

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
