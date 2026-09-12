import CollatzLean.Collatz3.Combinatorics.YoungFerrers

/-!
# Collatz3 Experimental2: Young/Ferrers plateau の一般座標

このファイルは Collatz 固有の算術を使わない。
有限 Ferrers/Young 図形の列高を、

* plateau の横幅、
* plateau の高さ、
* 高さの successive drop

へ分解するための最小 API を置く。

まず任意の自然数列に対する canonical run-length encoding を作る。
Ferrers shape の列高は antitone なので、この run-length code はそのまま
plateau 分解になる。

後段では RecordFerrers の特殊な Young 図形を、より直接的な
`(width, drop)` code で扱う。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- 同じ自然数を `n` 回並べる。proof を局所化するための薄い補助定義。 -/
def repeatValue : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, x => x :: repeatValue n x

@[simp] theorem repeatValue_zero (x : ℕ) :
    repeatValue 0 x = [] := rfl

@[simp] theorem repeatValue_succ (n x : ℕ) :
    repeatValue (n + 1) x = x :: repeatValue n x := rfl

/-- 末尾側から一個増やした形。plateau run の伸長に使う。 -/
theorem repeatValue_succ_right (n x : ℕ) :
    repeatValue (n + 1) x = repeatValue n x ++ [x] := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [repeatValue_succ, List.cons_append]
      exact congrArg (fun xs => x :: xs) ih

@[simp] theorem repeatValue_length (n x : ℕ) :
    (repeatValue n x).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [repeatValue, ih]

@[simp] theorem repeatValue_sum (n x : ℕ) :
    (repeatValue n x).sum = n * x := by
  induction n with
  | zero => simp [repeatValue]
  | succ n ih =>
      simp [repeatValue, ih, Nat.succ_mul, Nat.add_comm]

/-- `(width, height)` の canonical plateau code。 -/
abbrev PlateauHeightCode := List (ℕ × ℕ)

/-- plateau code を列高列へ戻す。 -/
def decodeHeightCode : PlateauHeightCode → List ℕ
  | [] => []
  | (w, h) :: cs => repeatValue w h ++ decodeHeightCode cs

/-- 一つの run を保持しながら左から列高列を読む。 -/
def encodeHeightAux : ℕ → ℕ → List ℕ → PlateauHeightCode
  | h, w, [] => [(w, h)]
  | h, w, x :: xs =>
      if x = h then
        encodeHeightAux h (w + 1) xs
      else
        (w, h) :: encodeHeightAux x 1 xs

/-- 任意の有限列高列の canonical plateau encoding。 -/
def encodeHeightCode : List ℕ → PlateauHeightCode
  | [] => []
  | h :: hs => encodeHeightAux h 1 hs

/-- run を保持した encoding は exact に元の prefix と tail を復元する。 -/
theorem decodeHeightCode_encodeHeightAux
    (h w : ℕ) :
    ∀ xs : List ℕ,
      decodeHeightCode (encodeHeightAux h w xs) =
        repeatValue w h ++ xs := by
  intro xs
  induction xs generalizing h w with
  | nil =>
      simp [encodeHeightAux, decodeHeightCode]
  | cons x xs ih =>
      by_cases hx : x = h
      · subst x
        simp only [encodeHeightAux]
        calc
          decodeHeightCode (encodeHeightAux h (w + 1) xs)
              = repeatValue (w + 1) h ++ xs :=
                ih (h := h) (w := w + 1)
          _ = (repeatValue w h ++ [h]) ++ xs := by
                rw [repeatValue_succ_right]
          _ = repeatValue w h ++ (h :: xs) := by
                simp [List.append_assoc]
      · simp only [encodeHeightAux, ite_eq_right hx, decodeHeightCode]
        calc
          repeatValue w h ++ decodeHeightCode (encodeHeightAux x 1 xs)
              = repeatValue w h ++ (repeatValue 1 x ++ xs) := by
                rw [ih (h := x) (w := 1)]
          _ = repeatValue w h ++ (x :: xs) := by
                simp [repeatValue]

/-- canonical plateau encoding を decode すると元の列高列へ戻る。 -/
@[simp] theorem decodeHeightCode_encodeHeightCode
    (xs : List ℕ) :
    decodeHeightCode (encodeHeightCode xs) = xs := by
  cases xs with
  | nil => rfl
  | cons h hs =>
      simpa [encodeHeightCode, repeatValue] using
        (decodeHeightCode_encodeHeightAux h 1 hs)

/-- canonical plateau encoding は injective。 -/
theorem encodeHeightCode_injective :
    Function.Injective encodeHeightCode := by
  intro xs ys h
  have hd := congrArg decodeHeightCode h
  simpa using hd

/-- plateau code の横幅列。 -/
def plateauWidths (c : PlateauHeightCode) : List ℕ :=
  c.map Prod.fst

/-- plateau code の高さ列。 -/
def plateauHeights (c : PlateauHeightCode) : List ℕ :=
  c.map Prod.snd

/--
高さ列から successive drop を読む。
最後の高さも `0` までの terminal drop として保存する。
-/
def successiveDropsFromHeights : List ℕ → List ℕ
  | [] => []
  | [h] => [h]
  | h :: k :: hs => (h - k) :: successiveDropsFromHeights (k :: hs)

/-- plateau code の successive drop 列。 -/
def plateauSuccessiveDrops (c : PlateauHeightCode) : List ℕ :=
  successiveDropsFromHeights (plateauHeights c)

/--
後段で使う `(plateau width, successive drop)` code。
一般 Young 図形では plateau encoding から derived data として得る。
RecordFerrers ではこの code が算術式から直接構成される。
-/
abbrev WidthDropCode := List (ℕ × ℕ)

/-- width-drop code の横幅列。 -/
def widthsOfCode (c : WidthDropCode) : List ℕ :=
  c.map Prod.fst

/-- width-drop code の落差列。 -/
def dropsOfCode (c : WidthDropCode) : List ℕ :=
  c.map Prod.snd

/-- code 全体の横幅。 -/
def codeWidth (c : WidthDropCode) : ℕ :=
  (widthsOfCode c).sum

/-- code 全体の縦落差。左端列の高さに対応する。 -/
def codeDropSum (c : WidthDropCode) : ℕ :=
  (dropsOfCode c).sum

/--
width-drop code が定める列高。
先頭 block `(r,d)` の `r` 列では全 suffix drop の和を高さにする。
-/
def columnHeightFromWidthDropCode : WidthDropCode → ℕ → ℕ
  | [], _ => 0
  | (r, d) :: cs, k =>
      if k < r then
        d + codeDropSum cs
      else
        columnHeightFromWidthDropCode cs (k - r)

/-- 任意の列高は code 全体の drop sum 以下。 -/
theorem columnHeightFromWidthDropCode_le_dropSum :
    ∀ (c : WidthDropCode) (k : ℕ),
      columnHeightFromWidthDropCode c k ≤ codeDropSum c
  | [], k => by
      simp [columnHeightFromWidthDropCode, codeDropSum, dropsOfCode]
  | (r, d) :: cs, k => by
      by_cases hk : k < r
      · simp [columnHeightFromWidthDropCode, codeDropSum, dropsOfCode, hk]
      · have hTail :=
          columnHeightFromWidthDropCode_le_dropSum cs (k - r)
        have hTail' :
            columnHeightFromWidthDropCode cs (k - r) ≤
              (List.map Prod.snd cs).sum := by
          simpa [codeDropSum, dropsOfCode] using hTail
        simp only [columnHeightFromWidthDropCode, hk, ↓reduceIte]
        simp [codeDropSum, dropsOfCode]
        omega

/-- width-drop code の列高は右へ進むほど増えない。 -/
theorem columnHeightFromWidthDropCode_antitone
    (c : WidthDropCode) :
    Antitone (columnHeightFromWidthDropCode c) := by
  induction c with
  | nil =>
      intro a b hab
      simp [columnHeightFromWidthDropCode]
  | cons p cs ih =>
      rcases p with ⟨r, d⟩
      intro a b hab
      by_cases hb : b < r
      · have ha : a < r := lt_of_le_of_lt hab hb
        simp [columnHeightFromWidthDropCode, ha, hb]
      · by_cases ha : a < r
        · have hTail := columnHeightFromWidthDropCode_le_dropSum cs (b - r)
          simp only [columnHeightFromWidthDropCode, ha, hb, ↓reduceIte]
          omega
        · have hSub : a - r ≤ b - r := Nat.sub_le_sub_right hab r
          simpa [columnHeightFromWidthDropCode, ha, hb] using ih hSub

/-- 任意 width-drop code から作る古典 Ferrers shape。 -/
def ferrersShapeOfWidthDropCode
    (c : WidthDropCode) :
    Combinatorics.FerrersShape (codeWidth c) :=
  ⟨fun k => columnHeightFromWidthDropCode c k.1,
    by
      intro i j hij
      exact columnHeightFromWidthDropCode_antitone c hij⟩

/-- Ferrers shape の underlying column list。 -/
def ferrersColumnList
    {m : ℕ}
    (F : Combinatorics.FerrersShape m) : List ℕ :=
  List.ofFn F.1

/-- 一般 Ferrers shape の canonical plateau code。 -/
def ferrersPlateauHeightCode
    {m : ℕ}
    (F : Combinatorics.FerrersShape m) : PlateauHeightCode :=
  encodeHeightCode (ferrersColumnList F)

/-- 一般 Ferrers shape の canonical plateau widths。 -/
def ferrersPlateauWidths
    {m : ℕ}
    (F : Combinatorics.FerrersShape m) : List ℕ :=
  plateauWidths (ferrersPlateauHeightCode F)

/-- 一般 Ferrers shape の canonical successive drops。 -/
def ferrersPlateauDrops
    {m : ℕ}
    (F : Combinatorics.FerrersShape m) : List ℕ :=
  plateauSuccessiveDrops (ferrersPlateauHeightCode F)

/-- 一般 Ferrers shape の plateau code は列高列を lossless に復元する。 -/
@[simp] theorem decode_ferrersPlateauHeightCode
    {m : ℕ}
    (F : Combinatorics.FerrersShape m) :
    decodeHeightCode (ferrersPlateauHeightCode F) = ferrersColumnList F := by
  simp [ferrersPlateauHeightCode]

/--
一般 Ferrers shape の canonical plateau decomposition は列高列の意味で一意。
従って plateau widths / heights / successive drops はすべて shape から決定的に定まる。
-/
theorem ferrersPlateauHeightCode_unique
    {m : ℕ}
    (F G : Combinatorics.FerrersShape m)
    (hCode : ferrersPlateauHeightCode F = ferrersPlateauHeightCode G) :
    ferrersColumnList F = ferrersColumnList G := by
  have h := congrArg decodeHeightCode hCode
  simpa using h

/--
canonical plateau code は Ferrers shape 自体を一意に決める。
したがって plateau widths と successive drops は任意選択ではなく、shape の完全な derived 座標である。
-/
theorem ferrersPlateauHeightCode_injective
    {m : ℕ} :
    Function.Injective
      (ferrersPlateauHeightCode :
        Combinatorics.FerrersShape m → PlateauHeightCode) := by
  intro F G hCode
  have hList := ferrersPlateauHeightCode_unique F G hCode
  have hFun : F.1 = G.1 := by
    exact List.ofFn_injective hList
  exact Subtype.ext hFun

end YoungFerrersRestricted
end Experimental2
end Collatz3
