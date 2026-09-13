import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.BasisCharacterization

/-!
# Collatz3 Experimental2: Frobenius diagonal corner と RecordFerrers plateau boundary

F7 では basis equality を

  `NoSimultaneousDiagonalCorner`

という Frobenius arm / successive-rank 座標上の条件で特徴付けた。
本ファイルではそれを `(width, drop)` plateau 座標へ exact に戻す。

RecordFerrers では

* plateau width = `canonicalRecordLengths`、
* plateau drop = `rankDropNat β m r`

なので、対角線上の internal step `t` における simultaneous corner は

* `t` が canonical width の累積境界であり、同時に
* `t` が reverse rank-drop の累積境界、すなわち suffix rank-drop height でもある

ことに一致する。

terminal step では従来の Frobenius terminal tightness
`arm = 0 ∨ arm = rank` をそのまま保持する。
したがって F7 は

  internal canonical-boundary collision の禁止
  + terminal Durfee tightness

へ翻訳される。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/--
正の幅列 `r₀,r₁,...` の累積 endpoint に `t` が一致すること。
再帰的に prefix sum を剥がすため、巨大な累積和 list を primitive data に持たない。
-/
def BoundaryAtWidths : List ℕ → ℕ → Prop
  | [], _ => False
  | r :: rs, t =>
      t = r ∨ (r < t ∧ BoundaryAtWidths rs (t - r))

/-- width-drop code の horizontal plateau endpoint。 -/
def WidthBoundaryAt
    (c : WidthDropCode)
    (t : ℕ) : Prop :=
  BoundaryAtWidths (widthsOfCode c) t

/--
元図形の vertical plateau endpoint。
Young 共役では widths が元 drop 列の逆順になるので、これは
reverse successive-drop の累積 endpoint、すなわち suffix-height boundary である。
-/
def DropHeightBoundaryAt
    (c : WidthDropCode)
    (t : ℕ) : Prop :=
  BoundaryAtWidths (dropsOfCode c).reverse t

/-- width と drop がすべて正の genuine plateau code。 -/
def PositiveWidthDropCode : WidthDropCode → Prop
  | [] => True
  | (r, d) :: cs =>
      0 < r ∧ 0 < d ∧ PositiveWidthDropCode cs

@[simp] theorem codeWidth_pair_cons
    (r d : ℕ)
    (cs : WidthDropCode) :
    codeWidth ((r, d) :: cs) = r + codeWidth cs := by
  simp [codeWidth, widthsOfCode]

@[simp] theorem codeDropSum_pair_cons
    (r d : ℕ)
    (cs : WidthDropCode) :
    codeDropSum ((r, d) :: cs) = d + codeDropSum cs := by
  simp [codeDropSum, dropsOfCode]

/-- positive plateau code は append に分解できる。 -/
theorem positiveWidthDropCode_append
    (a b : WidthDropCode) :
    PositiveWidthDropCode (a ++ b) ↔
      PositiveWidthDropCode a ∧ PositiveWidthDropCode b := by
  induction a with
  | nil =>
      simp [PositiveWidthDropCode]
  | cons p a ih =>
      rcases p with ⟨r, d⟩
      simp [PositiveWidthDropCode, ih, and_assoc]

/-- Young 共役は width/drop positivity を保存する。 -/
theorem positiveWidthDropCode_conjugate
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c) :
    PositiveWidthDropCode (conjugateWidthDropCode c) := by
  induction c with
  | nil =>
      simp [conjugateWidthDropCode, PositiveWidthDropCode]
  | cons p cs ih =>
      rcases p with ⟨r, d⟩
      change 0 < r ∧ 0 < d ∧ PositiveWidthDropCode cs at hPos
      rcases hPos with ⟨hr, hd, hTail⟩
      have hConjTail := ih hTail
      have hEq :
          conjugateWidthDropCode ((r, d) :: cs) =
            conjugateWidthDropCode cs ++ [(d, r)] := by
        simp [conjugateWidthDropCode]
      rw [hEq]
      apply (positiveWidthDropCode_append _ _).2
      refine ⟨hConjTail, ?_⟩
      simp [PositiveWidthDropCode, hd, hr]

/-- drop-height boundary は共役 code の width boundary そのもの。 -/
theorem dropHeightBoundaryAt_iff_conjugateWidthBoundaryAt
    (c : WidthDropCode)
    (t : ℕ) :
    DropHeightBoundaryAt c t ↔
      WidthBoundaryAt (conjugateWidthDropCode c) t := by
  unfold DropHeightBoundaryAt WidthBoundaryAt
  rw [widthsOfCode_conjugate]

/--
正の plateau code では、internal horizontal endpoint と列高の strict change が一致する。
-/
theorem widthBoundaryAt_iff_columnHeight_ne :
    ∀ (c : WidthDropCode),
      PositiveWidthDropCode c →
      ∀ t : ℕ,
        0 < t →
        t < codeWidth c →
        (WidthBoundaryAt c t ↔
          columnHeightFromWidthDropCode c (t - 1) ≠
            columnHeightFromWidthDropCode c t)
  | [], _hPos, t, _ht, hW => by
      simp [codeWidth, widthsOfCode] at hW
  | (r, d) :: cs, hPos, t, ht, hW => by
      change 0 < r ∧ 0 < d ∧ PositiveWidthDropCode cs at hPos
      rcases hPos with ⟨hr, hd, hTail⟩
      have hW' : t < r + codeWidth cs := by
        simpa using hW
      by_cases htr : t < r
      · have hprev : t - 1 < r := by omega
        have hNot : ¬ WidthBoundaryAt ((r, d) :: cs) t := by
          unfold WidthBoundaryAt
          change ¬ BoundaryAtWidths (r :: widthsOfCode cs) t
          simp [BoundaryAtWidths]
          omega
        have hEq :
            columnHeightFromWidthDropCode ((r, d) :: cs) (t - 1) =
              columnHeightFromWidthDropCode ((r, d) :: cs) t := by
          simp [columnHeightFromWidthDropCode, hprev, htr]
        constructor
        · intro hB
          exact False.elim (hNot hB)
        · intro hNe
          exact False.elim (hNe hEq)
      · have hrt : r ≤ t := le_of_not_gt htr
        by_cases hEqtr : t = r
        · subst t
          have hprev : r - 1 < r := by omega
          have hTailBound :=
            columnHeightFromWidthDropCode_le_dropSum cs 0
          have hNe :
              columnHeightFromWidthDropCode ((r, d) :: cs) (r - 1) ≠
                columnHeightFromWidthDropCode ((r, d) :: cs) r := by
            simp only [columnHeightFromWidthDropCode, hprev,
              lt_irrefl, ↓reduceIte, Nat.sub_self]
            omega
          constructor
          · intro _hB
            exact hNe
          · intro _hNe
            unfold WidthBoundaryAt
            change BoundaryAtWidths (r :: widthsOfCode cs) r
            exact Or.inl rfl
        · have hrt' : r < t := lt_of_le_of_ne hrt (Ne.symm hEqtr)
          have hprevNot : ¬ t - 1 < r := by omega
          have hnowNot : ¬ t < r := by omega
          have huPos : 0 < t - r := by omega
          have huW : t - r < codeWidth cs := by omega
          have hIndex : t - 1 - r = (t - r) - 1 := by omega
          have ih :=
            widthBoundaryAt_iff_columnHeight_ne
              cs hTail (t - r) huPos huW
          have hBoundary :
              WidthBoundaryAt ((r, d) :: cs) t ↔
                WidthBoundaryAt cs (t - r) := by
            unfold WidthBoundaryAt
            change
              BoundaryAtWidths (r :: widthsOfCode cs) t ↔
                BoundaryAtWidths (widthsOfCode cs) (t - r)
            simp [BoundaryAtWidths, hrt', hEqtr]
          constructor
          · intro hB
            have hBTail := hBoundary.1 hB
            have hNeTail := ih.1 hBTail
            simpa [columnHeightFromWidthDropCode, hprevNot,
              hnowNot, hIndex] using hNeTail
          · intro hNe
            have hNeTail :
                columnHeightFromWidthDropCode cs ((t - r) - 1) ≠
                  columnHeightFromWidthDropCode cs (t - r) := by
              simpa [columnHeightFromWidthDropCode, hprevNot,
                hnowNot, hIndex] using hNe
            exact hBoundary.2 (ih.2 hNeTail)

/--
正の plateau code では、internal suffix-height endpoint と行長の strict change が一致する。
-/
theorem dropHeightBoundaryAt_iff_rowLength_ne
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c)
    (t : ℕ)
    (ht : 0 < t)
    (hH : t < codeDropSum c) :
    DropHeightBoundaryAt c t ↔
      frobeniusRowLength c (t - 1) ≠ frobeniusRowLength c t := by
  have hConjPos := positiveWidthDropCode_conjugate c hPos
  have hW : t < codeWidth (conjugateWidthDropCode c) := by
    rw [codeWidth_conjugate]
    exact hH
  have h :=
    widthBoundaryAt_iff_columnHeight_ne
      (conjugateWidthDropCode c) hConjPos t ht hW
  rw [dropHeightBoundaryAt_iff_conjugateWidthBoundaryAt]
  simpa [frobeniusRowLength] using h

/-- arm の最小 gap は、その row plateau に boundary が無いことと同値。 -/
theorem frobeniusArm_tight_iff_not_dropHeightBoundary
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c)
    (start : ℕ)
    (hDepth : start + 2 ≤ frobeniusDepth c) :
    ((frobeniusArmAt c start : ℤ) =
        (frobeniusArmAt c (start + 1) : ℤ) + 1) ↔
      ¬ DropHeightBoundaryAt c (start + 1) := by
  have h0 : start < frobeniusDepth c := by omega
  have h1 : start + 1 < frobeniusDepth c := by omega
  have hRow0 := frobeniusRow_diagonal c h0
  have hRow1 := frobeniusRow_diagonal c h1
  have hH : start + 1 < codeDropSum c :=
    lt_of_lt_of_le h1 (frobeniusDepth_le_codeDropSum c)
  have hBoundary :=
    dropHeightBoundaryAt_iff_rowLength_ne
      c hPos (start + 1) (by omega) hH
  have hTightRow :
      ((frobeniusArmAt c start : ℤ) =
          (frobeniusArmAt c (start + 1) : ℤ) + 1) ↔
        frobeniusRowLength c start =
          frobeniusRowLength c (start + 1) := by
    unfold frobeniusArmAt
    constructor
    · intro h
      have hNat :
          frobeniusRowLength c start - (start + 1) =
            (frobeniusRowLength c (start + 1) - (start + 2)) + 1 := by
        exact_mod_cast h
      omega
    · intro hEq
      have hNat :
          frobeniusRowLength c start - (start + 1) =
            (frobeniusRowLength c (start + 1) - (start + 2)) + 1 := by
        omega
      exact_mod_cast hNat
  have hNoBoundary :
      (¬ DropHeightBoundaryAt c (start + 1)) ↔
        frobeniusRowLength c start =
          frobeniusRowLength c (start + 1) := by
    constructor
    · intro hNo
      by_contra hNe
      exact hNo (hBoundary.2 hNe)
    · intro hEq hB
      exact (hBoundary.1 hB) hEq
  exact hTightRow.trans hNoBoundary.symm

/-- leg の最小 gap は、その column plateau に boundary が無いことと同値。 -/
theorem frobeniusLeg_tight_iff_not_widthBoundary
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c)
    (start : ℕ)
    (hDepth : start + 2 ≤ frobeniusDepth c) :
    ((frobeniusLegAt c start : ℤ) =
        (frobeniusLegAt c (start + 1) : ℤ) + 1) ↔
      ¬ WidthBoundaryAt c (start + 1) := by
  have h0 : start < frobeniusDepth c := by omega
  have h1 : start + 1 < frobeniusDepth c := by omega
  have hCol0 := frobeniusColumn_diagonal c h0
  have hCol1 := frobeniusColumn_diagonal c h1
  have hW : start + 1 < codeWidth c :=
    lt_of_lt_of_le h1 (frobeniusDepth_le_codeWidth c)
  have hBoundary :=
    widthBoundaryAt_iff_columnHeight_ne
      c hPos (start + 1) (by omega) hW
  have hTightCol :
      ((frobeniusLegAt c start : ℤ) =
          (frobeniusLegAt c (start + 1) : ℤ) + 1) ↔
        frobeniusColumnHeight c start =
          frobeniusColumnHeight c (start + 1) := by
    unfold frobeniusLegAt
    constructor
    · intro h
      have hNat :
          frobeniusColumnHeight c start - (start + 1) =
            (frobeniusColumnHeight c (start + 1) - (start + 2)) + 1 := by
        exact_mod_cast h
      omega
    · intro hEq
      have hNat :
          frobeniusColumnHeight c start - (start + 1) =
            (frobeniusColumnHeight c (start + 1) - (start + 2)) + 1 := by
        omega
      exact_mod_cast hNat
  have hNoBoundary :
      (¬ WidthBoundaryAt c (start + 1)) ↔
        frobeniusColumnHeight c start =
          frobeniusColumnHeight c (start + 1) := by
    constructor
    · intro hNo
      by_contra hNe
      exact hNo (hBoundary.2 hNe)
    · intro hEq hB
      exact (hBoundary.1 hB) hEq
  exact hTightCol.trans hNoBoundary.symm

/--
F7 の条件を plateau boundary だけで読む再帰形。
internal step では width boundary と drop-height boundary の同時発生を禁止する。
terminal step は F7 の terminal tightness をそのまま保持する。
-/
def PlateauBasisConditionFrom
    (c : WidthDropCode) : ℕ → ℕ → Prop
  | _start, 0 => True
  | start, 1 =>
      (frobeniusArmAt c start : ℤ) = 0 ∨
        (frobeniusArmAt c start : ℤ) = frobeniusRankAt c start
  | start, n + 2 =>
      ¬ (WidthBoundaryAt c (start + 1) ∧
          DropHeightBoundaryAt c (start + 1)) ∧
        PlateauBasisConditionFrom c (start + 1) (n + 1)

/-- actual Frobenius depth 全体に対する plateau basis condition。 -/
def PlateauBasisCondition
    (c : WidthDropCode) : Prop :=
  PlateauBasisConditionFrom c 0 (frobeniusDepth c)

/--
actual Frobenius vectors 上では F7 の no-simultaneous-corner 条件と
plateau boundary collision-free 条件が exact に一致する。
-/
theorem noSimultaneousDiagonalCorner_iff_plateauBasisConditionFrom
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c) :
    ∀ (start n : ℕ),
      start + n ≤ frobeniusDepth c →
      (NoSimultaneousDiagonalCorner
          (successiveRankVectorFrom c start n)
          (frobeniusArmsZFrom c start n) ↔
        PlateauBasisConditionFrom c start n)
  | start, 0, _hDepth => by
      constructor
      · intro _h
        trivial
      · intro _h
        exact NoSimultaneousDiagonalCorner.nil
  | start, 1, _hDepth => by
      simp only [successiveRankVectorFrom, frobeniusArmsZFrom,
        PlateauBasisConditionFrom]
      constructor
      · intro h
        cases h with
        | single _ _ hTerminal =>
            exact hTerminal
      · intro hTerminal
        exact NoSimultaneousDiagonalCorner.single _ _ hTerminal
  | start, n + 2, hDepth => by
      simp only [successiveRankVectorFrom, frobeniusArmsZFrom,
        PlateauBasisConditionFrom]
      constructor
      · intro h
        cases h with
        | cons hTail hTight =>
            refine ⟨?_, ?_⟩
            · have hArm :=
                frobeniusArm_tight_iff_not_dropHeightBoundary
                  c hPos start (by omega)
              have hLeg :=
                frobeniusLeg_tight_iff_not_widthBoundary
                  c hPos start (by omega)
              rcases hTight with hArmTight | hRankTight
              · have hNoDrop := hArm.1 hArmTight
                intro hBoth
                exact hNoDrop hBoth.2
              · have hLegTight :
                    (frobeniusLegAt c start : ℤ) =
                      (frobeniusLegAt c (start + 1) : ℤ) + 1 := by
                  unfold frobeniusRankAt at hRankTight
                  omega
                have hNoWidth := hLeg.1 hLegTight
                intro hBoth
                exact hNoWidth hBoth.1
            · exact
                (noSimultaneousDiagonalCorner_iff_plateauBasisConditionFrom
                  c hPos (start + 1) (n + 1) (by omega)).1 hTail
      · intro h
        rcases h with ⟨hNoBoth, hTail⟩
        apply NoSimultaneousDiagonalCorner.cons
        · exact
            (noSimultaneousDiagonalCorner_iff_plateauBasisConditionFrom
              c hPos (start + 1) (n + 1) (by omega)).2 hTail
        · have hArm :=
            frobeniusArm_tight_iff_not_dropHeightBoundary
              c hPos start (by omega)
          have hLeg :=
            frobeniusLeg_tight_iff_not_widthBoundary
              c hPos start (by omega)
          by_cases hW : WidthBoundaryAt c (start + 1)
          · have hNoDrop : ¬ DropHeightBoundaryAt c (start + 1) := by
              intro hD
              exact hNoBoth ⟨hW, hD⟩
            exact Or.inl (hArm.2 hNoDrop)
          · have hLegTight := hLeg.2 hW
            right
            unfold frobeniusRankAt
            omega

/-- F7 条件と plateau condition の whole-shape exact bridge。 -/
theorem noSimultaneousDiagonalCorner_iff_plateauBasisCondition
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c) :
    NoSimultaneousDiagonalCorner
        (successiveRankVector c)
        (frobeniusArmsZ c) ↔
      PlateauBasisCondition c := by
  unfold successiveRankVector frobeniusArmsZ PlateauBasisCondition
  exact
    noSimultaneousDiagonalCorner_iff_plateauBasisConditionFrom
      c hPos 0 (frobeniusDepth c) (by simp)

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted
open GenericRecordFerrers

/-- RecordFerrers の canonical width 累積境界。 -/
def canonicalWidthBoundaryAt
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (t : ℕ) : Prop :=
  BoundaryAtWidths (canonicalRecordLengths β m R.height) t

/--
RecordFerrers の rank-drop height 境界。
reverse rank-drop の prefix sum、すなわち元 shape の suffix rank-drop height を読む。
-/
def rankDropHeightBoundaryAt
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (t : ℕ) : Prop :=
  BoundaryAtWidths
    (((canonicalRecordLengths β m R.height).map (rankDropNat β m)).reverse) t

/-- canonical width boundary は plateau code の width boundary と exact に同じ。 -/
theorem canonicalWidthBoundaryAt_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (t : ℕ) :
    R.canonicalWidthBoundaryAt t ↔
      WidthBoundaryAt R.plateauWidthDropCode t := by
  unfold canonicalWidthBoundaryAt WidthBoundaryAt
  rw [R.plateauWidths_eq_canonicalRecordLengths]

/-- rank-drop height boundary は plateau code の drop-height boundary と exact に同じ。 -/
theorem rankDropHeightBoundaryAt_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (t : ℕ) :
    R.rankDropHeightBoundaryAt t ↔
      DropHeightBoundaryAt R.plateauWidthDropCode t := by
  unfold rankDropHeightBoundaryAt DropHeightBoundaryAt
  rw [R.plateauDrops_eq_rankDrops]

/-- canonical width endpoint と rank-drop height endpoint が同じ対角 level に衝突すること。 -/
def HasCanonicalBoundaryCollision
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (t : ℕ) : Prop :=
  R.canonicalWidthBoundaryAt t ∧ R.rankDropHeightBoundaryAt t

/-- canonical collision は一般 plateau collision と exact に同じ。 -/
theorem hasCanonicalBoundaryCollision_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m)
    (t : ℕ) :
    R.HasCanonicalBoundaryCollision t ↔
      (WidthBoundaryAt R.plateauWidthDropCode t ∧
        DropHeightBoundaryAt R.plateauWidthDropCode t) := by
  unfold HasCanonicalBoundaryCollision
  rw [R.canonicalWidthBoundaryAt_iff, R.rankDropHeightBoundaryAt_iff]

/-- positive integer rank drop は自然数化しても正。 -/
theorem rankDropNat_pos_of_rankDropInt_pos
    {β : ℕ → ℕ}
    {m r : ℕ}
    (h : 0 < rankDropInt β m r) :
    0 < rankDropNat β m r := by
  unfold rankDropNat
  have hNonneg : 0 ≤ rankDropInt β m r := le_of_lt h
  have hCast := Int.toNat_of_nonneg hNonneg
  omega

/-- positive canonical widths と positive integer rank drops から genuine positive plateau code を得る。 -/
theorem positiveWidthDropCode_widthDropCodeFromLengths
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∀ (rs : List ℕ),
      (∀ r ∈ rs, 0 < r) →
      PositiveRankDrops β m rs →
      PositiveWidthDropCode (widthDropCodeFromLengths β m rs)
  | [], _hWidth, _hDrop => by
      trivial
  | r :: rs, hWidth, hDrop => by
      simp only [PositiveRankDrops] at hDrop
      change
        0 < r ∧ 0 < rankDropNat β m r ∧
          PositiveWidthDropCode (widthDropCodeFromLengths β m rs)
      refine ⟨hWidth r (by simp),
        rankDropNat_pos_of_rankDropInt_pos hDrop.1, ?_⟩
      apply positiveWidthDropCode_widthDropCodeFromLengths β m rs
      · intro q hq
        exact hWidth q (by simp [hq])
      · exact hDrop.2

/-- 完成 RecordFerrers の canonical plateau code は genuine positive code。 -/
theorem plateauWidthDropCode_positiveWidthDropCode
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    PositiveWidthDropCode R.plateauWidthDropCode := by
  unfold plateauWidthDropCode
  apply positiveWidthDropCode_widthDropCodeFromLengths β m
  · intro r hr
    exact canonicalRecordLengths_pos R.one_lt_width r hr
  · exact R.positiveRankDrops

/--
RecordFerrers 専用の F7 plateau condition。
internal step では canonical width / rank-drop-height collision を直接禁止する。
-/
def CanonicalPlateauBasisConditionFrom
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) : ℕ → ℕ → Prop
  | _start, 0 => True
  | start, 1 =>
      (frobeniusArmAt R.plateauWidthDropCode start : ℤ) = 0 ∨
        (frobeniusArmAt R.plateauWidthDropCode start : ℤ) =
          frobeniusRankAt R.plateauWidthDropCode start
  | start, n + 2 =>
      ¬ R.HasCanonicalBoundaryCollision (start + 1) ∧
        R.CanonicalPlateauBasisConditionFrom (start + 1) (n + 1)

/-- whole RecordFerrers shape に対する canonical plateau basis condition。 -/
def CanonicalPlateauBasisCondition
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) : Prop :=
  R.CanonicalPlateauBasisConditionFrom 0
    (frobeniusDepth R.plateauWidthDropCode)

/-- generic plateau condition と RecordFerrers canonical condition は exact に同じ。 -/
theorem canonicalPlateauBasisConditionFrom_iff
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    ∀ start n,
      R.CanonicalPlateauBasisConditionFrom start n ↔
        PlateauBasisConditionFrom R.plateauWidthDropCode start n
  | _start, 0 => by
      rfl
  | _start, 1 => by
      rfl
  | start, n + 2 => by
      simp only [CanonicalPlateauBasisConditionFrom, PlateauBasisConditionFrom]
      rw [R.hasCanonicalBoundaryCollision_iff]
      rw [R.canonicalPlateauBasisConditionFrom_iff (start + 1) (n + 1)]

/-- F7 の Frobenius condition を canonical widths / rank drops へ exact に翻訳する。 -/
theorem noSimultaneousDiagonalCorner_iff_canonicalPlateauBasisCondition
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    NoSimultaneousDiagonalCorner
        R.successiveRanks
        (frobeniusArmsZ R.plateauWidthDropCode) ↔
      R.CanonicalPlateauBasisCondition := by
  unfold successiveRanks CanonicalPlateauBasisCondition
  rw [R.canonicalPlateauBasisConditionFrom_iff]
  exact
    noSimultaneousDiagonalCorner_iff_plateauBasisCondition
      R.plateauWidthDropCode R.plateauWidthDropCode_positiveWidthDropCode

/--
最終 bridge：RecordFerrers が successive-rank basis の最小面積を達成することと、
canonical width / rank-drop-height の internal collision が無いこと
（および terminal tightness）が exact に同値。
-/
theorem youngCellCount_eq_basisWeightZ_iff_canonicalPlateauBasisCondition
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    (R.youngCellCount : ℤ) = basisWeightZ R.successiveRanks ↔
      R.CanonicalPlateauBasisCondition := by
  rw [R.youngCellCount_eq_basisWeightZ_iff_noSimultaneousDiagonalCorner]
  exact R.noSimultaneousDiagonalCorner_iff_canonicalPlateauBasisCondition

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
