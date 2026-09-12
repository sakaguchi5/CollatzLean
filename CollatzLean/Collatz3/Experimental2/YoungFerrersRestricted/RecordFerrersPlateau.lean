import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.PlateauDecomposition
import CollatzLean.Collatz3.Experimental2.GenericRecordFerrers.RecordRankFerrersShape

/-!
# Collatz3 Experimental2: RecordFerrers の特殊 plateau class

一般 Young/Ferrers 図形では plateau の横幅と縦落差は独立に選べる。
RecordFerrers の rank-envelope shape ではそうではない。

canonical block 長 `r` に対応する縦落差は

`rankDropNat β m r`

に強制される。
このファイルでは

* plateau width = `canonicalRecordLengths`、
* successive drop = `rankDropNat β m r`、
* その width-drop code から読む列高 = `rankFerrersShape` の列高

を exact に固定する。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

open GenericRecordFerrers

/-- 任意 length code を RecordFerrers 型の `(width, rank-drop)` code へ写す。 -/
def widthDropCodeFromLengths
    (β : ℕ → ℕ)
    (m : ℕ)
    (rs : List ℕ) : WidthDropCode :=
  rs.map (fun r => (r, rankDropNat β m r))

@[simp] theorem widthsOfCode_widthDropCodeFromLengths
    (β : ℕ → ℕ)
    (m : ℕ)
    (rs : List ℕ) :
    widthsOfCode (widthDropCodeFromLengths β m rs) = rs := by
  simp [widthDropCodeFromLengths, widthsOfCode, Function.comp_def]

@[simp] theorem dropsOfCode_widthDropCodeFromLengths
    (β : ℕ → ℕ)
    (m : ℕ)
    (rs : List ℕ) :
    dropsOfCode (widthDropCodeFromLengths β m rs) =
      rs.map (rankDropNat β m) := by
  simp [widthDropCodeFromLengths, dropsOfCode, Function.comp_def]

@[simp] theorem codeWidth_widthDropCodeFromLengths
    (β : ℕ → ℕ)
    (m : ℕ)
    (rs : List ℕ) :
    codeWidth (widthDropCodeFromLengths β m rs) = rs.sum := by
  simp [codeWidth]

/-- rank-drop code の drop sum は既存 `rankDropNatSum` と exact に一致する。 -/
theorem codeDropSum_widthDropCodeFromLengths
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∀ rs : List ℕ,
      codeDropSum (widthDropCodeFromLengths β m rs) =
        rankDropNatSum β m rs
  | [] => by
      rfl
  | r :: rs => by
      change
        rankDropNat β m r +
            codeDropSum (widthDropCodeFromLengths β m rs) =
          rankDropNat β m r + rankDropNatSum β m rs
      rw [codeDropSum_widthDropCodeFromLengths β m rs]

/--
width-drop code から読む列高は、既存 rank-envelope 列高と一点ごとに一致する。
-/
theorem columnHeight_widthDropCodeFromLengths_eq_rank
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∀ (rs : List ℕ) (k : ℕ),
      columnHeightFromWidthDropCode
          (widthDropCodeFromLengths β m rs) k =
        rankFerrersColumnHeightFromLengths β m rs k
  | [], k => by
      rfl
  | r :: rs, k => by
      by_cases hk : k < r
      · simp only [
          widthDropCodeFromLengths,
          List.map_cons,
          columnHeightFromWidthDropCode,
          rankFerrersColumnHeightFromLengths,
          hk,
          ↓reduceIte
        ]
        change
          rankDropNat β m r +
              codeDropSum (widthDropCodeFromLengths β m rs) =
            rankDropNat β m r + rankDropNatSum β m rs
        rw [codeDropSum_widthDropCodeFromLengths β m rs]
      · simp only [
          widthDropCodeFromLengths,
          List.map_cons,
          columnHeightFromWidthDropCode,
          rankFerrersColumnHeightFromLengths,
          hk,
          ↓reduceIte
        ]
        exact
          columnHeight_widthDropCodeFromLengths_eq_rank
            β m rs (k - r)

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- 完成 RecordFerrers の canonical `(plateau width, rank drop)` code。 -/
def plateauWidthDropCode
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) : WidthDropCode :=
  widthDropCodeFromLengths β m
    (canonicalRecordLengths β m R.height)

/-- plateau widths は canonical record lengths そのもの。 -/
@[simp] theorem plateauWidths_eq_canonicalRecordLengths
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    widthsOfCode R.plateauWidthDropCode =
      canonicalRecordLengths β m R.height := by
  simp [plateauWidthDropCode]

/-- successive drops は各 canonical block の `rankDropNat` そのもの。 -/
@[simp] theorem plateauDrops_eq_rankDrops
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    dropsOfCode R.plateauWidthDropCode =
      (canonicalRecordLengths β m R.height).map (rankDropNat β m) := by
  simp [plateauWidthDropCode]

/-- RecordFerrers plateau code の総横幅は exact に `m-1`。 -/
@[simp] theorem plateauCode_width
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    codeWidth R.plateauWidthDropCode = m - 1 := by
  rw [plateauWidthDropCode, codeWidth_widthDropCodeFromLengths]
  exact R.canonicalRecordLengths_sum_width

/--
同じ幅 `m-1` 上で、plateau code から作る Ferrers shape。
`codeWidth` への cast を primitive data に持ち込まないための RecordFerrers 専用 wrapper。
-/
def plateauFerrersShape
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    Combinatorics.FerrersShape (m - 1) :=
  ⟨fun k => columnHeightFromWidthDropCode R.plateauWidthDropCode k.1,
    by
      intro i j hij
      exact columnHeightFromWidthDropCode_antitone R.plateauWidthDropCode hij⟩

/--
RecordFerrers plateau code が作る shape は既存 `rankFerrersShape` と exact に同じ。
これで一般 Young plateau 座標と RecordFerrers rank-envelope が接続される。
-/
theorem plateauFerrersShape_eq_rankFerrersShape
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    R.plateauFerrersShape = R.rankFerrersShape := by
  apply Subtype.ext
  funext k
  change
    columnHeightFromWidthDropCode
        (widthDropCodeFromLengths β m
          (canonicalRecordLengths β m R.height)) k.1 =
      rankFerrersColumnHeightFromLengths β m
        (canonicalRecordLengths β m R.height) k.1
  exact
    columnHeight_widthDropCodeFromLengths_eq_rank
      β m (canonicalRecordLengths β m R.height) k.1

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
