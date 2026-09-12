import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Conjugate



/-!
# Collatz3 Experimental2: plateau 共役と genuine Young 共役の一致

前段 `Conjugate` では width-drop code

  [(r₀,d₀),...,(rₛ,dₛ)]

に対し、swap して reverse する座標変換を Young 共役として導入した。
本ファイルではそれが単なる記号操作ではなく、cell の転置

  (i,j) が元図形の cell
    ↔
  (j,i) が共役図形の cell

を満たす genuine Young conjugation であることを証明する。

証明の核は、元図形の高さ `j` の横幅を直接数える
`genuineConjugateColumnHeight` と、座標共役 code の列高が exact に一致すること。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

@[simp] theorem codeWidth_cons
    (r d : ℕ) (cs : WidthDropCode) :
    codeWidth ((r, d) :: cs) = r + codeWidth cs := by
  simp [codeWidth, widthsOfCode]

@[simp] theorem codeDropSum_cons
    (r d : ℕ) (cs : WidthDropCode) :
    codeDropSum ((r, d) :: cs) = d + codeDropSum cs := by
  simp [codeDropSum, dropsOfCode]

@[simp] theorem conjugateWidthDropCode_cons
    (r d : ℕ) (cs : WidthDropCode) :
    conjugateWidthDropCode ((r, d) :: cs) =
      conjugateWidthDropCode cs ++ [(d, r)] := by
  simp [conjugateWidthDropCode]

@[simp] theorem codeDropSum_append_singleton
    (d r : ℕ) :
    ∀ cs : WidthDropCode,
      codeDropSum (cs ++ [(d, r)]) =
        codeDropSum cs + r
  | [] => by
      simp [codeDropSum, dropsOfCode]
  | (w, e) :: cs => by
      simp [
        codeDropSum,
        dropsOfCode,
        Nat.add_assoc
      ]

/--
width-drop code の末尾に一 block `(d,r)` を付けると、
既存部分の全列高は `r` だけ上がり、その右に高さ `r` の列が `d` 本増える。
-/
theorem columnHeight_append_singleton
    (d r : ℕ) :
    ∀ (cs : WidthDropCode) (k : ℕ),
      columnHeightFromWidthDropCode (cs ++ [(d, r)]) k =
        if k < codeWidth cs then
          columnHeightFromWidthDropCode cs k + r
        else if k < codeWidth cs + d then
          r
        else
          0
  | [], k => by
      simp [
        columnHeightFromWidthDropCode,
        codeWidth,
        widthsOfCode,
        codeDropSum,
        dropsOfCode
      ]
  | (w, e) :: cs, k => by
      by_cases hk0 : k < w
      · have hkAll :
            k < codeWidth ((w, e) :: cs) := by
          rw [codeWidth_cons]
          omega
        simp only [
          List.cons_append,
          columnHeightFromWidthDropCode,
          hk0,
          ↓reduceIte,
          hkAll
        ]
        rw [codeDropSum_append_singleton]
        omega
      · have hwk : w ≤ k := le_of_not_gt hk0
        have hWidth :
            (k - w < codeWidth cs) ↔
              (k < w + codeWidth cs) := by
          omega
        have hWidthD :
            (k - w < codeWidth cs + d) ↔
              (k < w + codeWidth cs + d) := by
          omega
        simp only [
          List.cons_append,
          columnHeightFromWidthDropCode,
          hk0,
          ↓reduceIte,
          codeWidth_cons
        ]
        rw [columnHeight_append_singleton d r cs (k - w)]
        by_cases hk1 : k < w + codeWidth cs
        · have hsub :
              k - w < codeWidth cs :=
            hWidth.mpr hk1
          simp [hk1, hsub]
        · have hsub :
              ¬ k - w < codeWidth cs := by
            intro h
            exact hk1 (hWidth.mp h)
          by_cases hk2 :
              k < w + codeWidth cs + d
          · have hsubD :
                k - w < codeWidth cs + d :=
              hWidthD.mpr hk2
            simp [hk1, hk2, hsub, hsubD]
          · have hsubD :
                ¬ k - w < codeWidth cs + d := by
              intro h
              exact hk2 (hWidthD.mp h)
            simp [hk1, hk2, hsub, hsubD]

/--
元図形の高さ `j` に存在する cell の横幅。

先頭 block の高さは `d + suffixHeight`。
`j` が tail の高さより下なら先頭 `r` 列と tail の両方が残り、
tail より上で先頭 block 内なら `r` 列だけが残る。
-/
def genuineConjugateColumnHeight : WidthDropCode → ℕ → ℕ
  | [], _ => 0
  | (r, d) :: cs, j =>
      if j < codeDropSum cs then
        r + genuineConjugateColumnHeight cs j
      else if j < d + codeDropSum cs then
        r
      else
        0

/--
cell を直接数えた genuine 共役列高は、swap-reverse 座標共役の列高と exact に一致する。
-/
theorem genuineConjugateColumnHeight_eq_coordinate :
    ∀ (c : WidthDropCode) (j : ℕ),
      genuineConjugateColumnHeight c j =
        columnHeightFromWidthDropCode (conjugateWidthDropCode c) j
  | [], j => by
      rfl
  | (r, d) :: cs, j => by
      rw [conjugateWidthDropCode_cons]
      rw [columnHeight_append_singleton d r (conjugateWidthDropCode cs) j]
      rw [codeWidth_conjugate]
      simp only [genuineConjugateColumnHeight]
      rw [genuineConjugateColumnHeight_eq_coordinate cs j]
      by_cases h0 : j < codeDropSum cs
      · simp [h0, Nat.add_comm]
      · by_cases h1 : j < d + codeDropSum cs
        · have h1' : j < codeDropSum cs + d := by omega
          simp [h0, h1, h1']
        · have h1' : ¬ j < codeDropSum cs + d := by omega
          simp [h0, h1, h1']

/--
cell-wise transpose の核心。

`i` が元 code の横幅内、`j` が全縦高内なら、
共役側の第 `j` 列に高さ `i+1` の cell があることと、
元側の第 `i` 列に高さ `j+1` の cell があることは同値。
-/
theorem lt_genuineConjugateColumnHeight_iff :
    ∀ (c : WidthDropCode) (i j : ℕ),
      i < codeWidth c →
      j < codeDropSum c →
      (i < genuineConjugateColumnHeight c j ↔
        j < columnHeightFromWidthDropCode c i)
  | [], i, j, hi, _hj => by
      simp [codeWidth, widthsOfCode] at hi
  | (r, d) :: cs, i, j, hi, hj => by
      simp only [codeWidth_cons, codeDropSum_cons] at hi hj
      by_cases hi0 : i < r
      · by_cases hj0 : j < codeDropSum cs
        · simp [
            genuineConjugateColumnHeight,
            columnHeightFromWidthDropCode,
            hi0,
            hj0
          ]
          omega
        · have hj1 : j < d + codeDropSum cs := by omega
          simp [
            genuineConjugateColumnHeight,
            columnHeightFromWidthDropCode,
            hi0,
            hj0,
            hj1
          ]
      · have hri : r ≤ i := le_of_not_gt hi0
        have hiTail : i - r < codeWidth cs := by omega
        by_cases hj0 : j < codeDropSum cs
        · have hIH :=
            lt_genuineConjugateColumnHeight_iff
              cs (i - r) j hiTail hj0
          simp only [
            genuineConjugateColumnHeight,
            columnHeightFromWidthDropCode,
            hi0,
            hj0,
            ↓reduceIte
          ]
          constructor
          · intro h
            apply hIH.1
            omega
          · intro h
            have h' := hIH.2 h
            omega
        · have hTailLe :=
            columnHeightFromWidthDropCode_le_dropSum cs (i - r)
          by_cases hj1 : j < d + codeDropSum cs
          · simp only [
              genuineConjugateColumnHeight,
              columnHeightFromWidthDropCode,
              hi0,
              hj0,
              hj1,
              ↓reduceIte
            ]
            constructor
            · intro hFalse
              exact False.elim hFalse
            · intro h
              exact hj0 (lt_of_lt_of_le h hTailLe)
          · simp only [
              genuineConjugateColumnHeight,
              columnHeightFromWidthDropCode,
              hi0,
              hj0,
              hj1,
              ↓reduceIte
            ]
            omega

/-- cell を直接数える genuine 共役 shape。 -/
def genuineConjugateShape
    (c : WidthDropCode) :
    Combinatorics.FerrersShape (codeDropSum c) :=
  ⟨fun j => genuineConjugateColumnHeight c j.1,
    by
      intro i j hij
      change
        genuineConjugateColumnHeight c j.1 ≤
          genuineConjugateColumnHeight c i.1
      rw [
        genuineConjugateColumnHeight_eq_coordinate c j.1,
        genuineConjugateColumnHeight_eq_coordinate c i.1
      ]
      exact
        columnHeightFromWidthDropCode_antitone
          (conjugateWidthDropCode c) hij⟩

/-- swap-reverse 座標共役を、元図形の全縦高を幅として読む shape。 -/
def coordinateConjugateShape
    (c : WidthDropCode) :
    Combinatorics.FerrersShape (codeDropSum c) :=
  ⟨fun j =>
      columnHeightFromWidthDropCode (conjugateWidthDropCode c) j.1,
    by
      intro i j hij
      exact
        columnHeightFromWidthDropCode_antitone
          (conjugateWidthDropCode c) hij⟩

/-- A: coordinate conjugate = genuine Young conjugate。 -/
theorem coordinateConjugateShape_eq_genuineConjugateShape
    (c : WidthDropCode) :
    coordinateConjugateShape c = genuineConjugateShape c := by
  apply Subtype.ext
  funext j
  exact
    (genuineConjugateColumnHeight_eq_coordinate c j.1).symm

/--
座標共役 shape は genuine cell transpose を満たす。
これが「swap-reverse が本物の Young 共役である」ことの cell-level 仕様。
-/
theorem coordinateConjugate_hasCell_iff
    (c : WidthDropCode)
    (i : Fin (codeWidth c))
    (j : Fin (codeDropSum c)) :
    Combinatorics.HasCell (coordinateConjugateShape c).1 j i.1 ↔
      Combinatorics.HasCell (ferrersShapeOfWidthDropCode c).1 i j.1 := by
  unfold Combinatorics.HasCell
  change
    i.1 < columnHeightFromWidthDropCode (conjugateWidthDropCode c) j.1 ↔
      j.1 < columnHeightFromWidthDropCode c i.1
  rw [← genuineConjugateColumnHeight_eq_coordinate c j.1]
  exact
    lt_genuineConjugateColumnHeight_iff
      c i.1 j.1 i.2 j.2

end YoungFerrersRestricted
end Experimental2
end Collatz3
