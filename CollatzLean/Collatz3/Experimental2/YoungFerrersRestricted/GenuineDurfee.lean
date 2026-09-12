import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.GenuineConjugate
import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.Durfee



/-!
# Collatz3 Experimental2: code Durfee crossing と genuine Durfee square

`Durfee` では block endpoint ごとの

  min(cumulative width, suffix height)

の最大値を `codeDurfeeSize` とした。
本ファイルでは、古典的な列 partition

  h₀ ≥ h₁ ≥ ...

に対する Durfee size を

  max_i min(i+1, h_i)

として独立に定義し、positive-width code では両者が exact に一致することを証明する。

RecordFerrers の canonical block length はすべて正なので、この仮定は自動的に満たされる。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- width-drop code の各 plateau width が正。 -/
def PositiveWidths : WidthDropCode → Prop
  | [] => True
  | (r, _d) :: cs => 0 < r ∧ PositiveWidths cs

/--
古典的な column-partition Durfee scan。
`leftWidth` 列を既に通過した状態で、各列 `h` に対し `min(index+1,h)` を最大化する。
-/
def classicalDurfeeFromColumns : ℕ → List ℕ → ℕ
  | _leftWidth, [] => 0
  | leftWidth, h :: hs =>
      max (min (leftWidth + 1) h)
        (classicalDurfeeFromColumns (leftWidth + 1) hs)

/-- 左端から読む genuine Durfee size。 -/
def genuineDurfeeSize (c : WidthDropCode) : ℕ :=
  classicalDurfeeFromColumns 0 (columnListFromWidthDropCode c)

/--
高さ `h` の同一列が正の本数 `r+1` 続く plateau では、
`min(index+1,h)` の最大値は plateau 右端で達成される。
-/
theorem classicalDurfeeFromColumns_repeat_succ
    (leftWidth r h : ℕ)
    (xs : List ℕ) :
    classicalDurfeeFromColumns leftWidth
        (repeatValue (r + 1) h ++ xs) =
      max (min (leftWidth + (r + 1)) h)
        (classicalDurfeeFromColumns (leftWidth + (r + 1)) xs) := by
  induction r generalizing leftWidth with
  | zero =>
      simp [classicalDurfeeFromColumns, repeatValue]
  | succ r ih =>
      simp only [repeatValue_succ, List.cons_append]
      rw [classicalDurfeeFromColumns]
      have hIH :
          classicalDurfeeFromColumns (leftWidth + 1)
              (h :: (repeatValue r h ++ xs)) =
            max
              (min ((leftWidth + 1) + (r + 1)) h)
              (classicalDurfeeFromColumns
                ((leftWidth + 1) + (r + 1)) xs) := by
        simpa [repeatValue] using
          (ih (leftWidth := leftWidth + 1))
      rw [hIH]
      have hmin :
          min (leftWidth + 1) h ≤
            min ((leftWidth + 1) + (r + 1)) h := by
        exact min_le_min (by omega) (Nat.le_refl h)
      rw [← max_assoc]
      rw [max_eq_right hmin]
      congr 2 <;> omega

/--
positive-width code では、全列を一列ずつ走査した genuine Durfee scan と、
block endpoint だけを見る crossing scan が exact に一致する。
-/
theorem classicalDurfeeFromColumns_eq_candidates
    (leftWidth : ℕ) :
    ∀ (c : WidthDropCode),
      PositiveWidths c →
      classicalDurfeeFromColumns leftWidth
          (columnListFromWidthDropCode c) =
        maxNatList (durfeeCandidatesFrom leftWidth c)
  | [], _h => by
      rfl
  | (r, d) :: cs, hPos => by
      rcases hPos with ⟨hr, hTail⟩
      cases r with
      | zero =>
          omega
      | succ r =>
          simp only [
            columnListFromWidthDropCode,
            durfeeCandidatesFrom,
            maxNatList
          ]
          rw [classicalDurfeeFromColumns_repeat_succ]
          rw [
            classicalDurfeeFromColumns_eq_candidates
              (leftWidth + (r + 1)) cs hTail
          ]

/-- B: positive-width code では crossing Durfee size = genuine classical Durfee size。 -/
theorem genuineDurfeeSize_eq_codeDurfeeSize
    (c : WidthDropCode)
    (hPos : PositiveWidths c) :
    genuineDurfeeSize c = codeDurfeeSize c := by
  unfold genuineDurfeeSize codeDurfeeSize durfeeCandidates
  exact classicalDurfeeFromColumns_eq_candidates 0 c hPos

/-- 正の length 列から作る RecordFerrers 型 code は positive-width。 -/
theorem positiveWidths_widthDropCodeFromLengths
    (β : ℕ → ℕ)
    (m : ℕ) :
    ∀ (rs : List ℕ),
      (∀ r ∈ rs, 0 < r) →
      PositiveWidths (widthDropCodeFromLengths β m rs)
  | [], _h => by
      trivial
  | r :: rs, h => by
      simp only [widthDropCodeFromLengths, List.map_cons, PositiveWidths]
      refine ⟨h r (by simp), ?_⟩
      apply positiveWidths_widthDropCodeFromLengths β m rs
      intro q hq
      exact h q (by simp [hq])

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- 完成 RecordFerrers の plateau widths はすべて正。 -/
theorem plateauWidthDropCode_positiveWidths
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    PositiveWidths R.plateauWidthDropCode := by
  unfold plateauWidthDropCode
  apply positiveWidths_widthDropCodeFromLengths
  intro r hr
  exact
    canonicalRecordLengths_pos R.one_lt_width r hr

/--
B の RecordFerrers 版：既存 `rankDurfeeSize` は genuine classical Durfee size と exact に一致する。
-/
theorem rankDurfeeSize_eq_genuineDurfeeSize
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    R.rankDurfeeSize = genuineDurfeeSize R.plateauWidthDropCode := by
  unfold rankDurfeeSize
  exact
    (genuineDurfeeSize_eq_codeDurfeeSize
      R.plateauWidthDropCode R.plateauWidthDropCode_positiveWidths).symm

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
