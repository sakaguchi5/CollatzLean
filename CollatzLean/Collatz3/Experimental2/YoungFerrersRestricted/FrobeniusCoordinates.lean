import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.ClassicalDominance

/-!
# Collatz3 Experimental2: Frobenius 座標

Young/Ferrers 図形の対角線を直接読むための薄い座標層。

* `frobeniusColumnHeight` は元図形の列高。
* `frobeniusRowLength` は genuine Young 共役から読む元図形の行長。
* `frobeniusDepth` は対角 cell が連続して存在する最大幅。
* arm / leg は各対角 cell から右 / 下へ伸びる cell 数。

既存 `genuineDurfeeSize` と独立に対角線を走査してから、両者が exact に一致することを証明する。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- 元図形の第 `i` 列の高さ。 -/
def frobeniusColumnHeight (c : WidthDropCode) (i : ℕ) : ℕ :=
  columnHeightFromWidthDropCode c i

/-- genuine Young 共役から読む、元図形の第 `i` 行の長さ。 -/
def frobeniusRowLength (c : WidthDropCode) (i : ℕ) : ℕ :=
  columnHeightFromWidthDropCode (conjugateWidthDropCode c) i

/--
`start` から右へ対角 cell `(i,i)` を走査する。
`fuel` は残りの列数。最初に対角 cell が消える絶対 index を返す。
-/
def diagonalDepthAux (c : WidthDropCode) : ℕ → ℕ → ℕ
  | start, 0 => start
  | start, fuel + 1 =>
      if start < frobeniusColumnHeight c start then
        diagonalDepthAux c (start + 1) fuel
      else
        start

/-- width-drop code が表す Young 図形の対角線長。 -/
def frobeniusDepth (c : WidthDropCode) : ℕ :=
  diagonalDepthAux c 0 (codeWidth c)

/-- 対角走査は開始位置より左へ戻らない。 -/
theorem diagonalDepthAux_ge_start
    (c : WidthDropCode) :
    ∀ start fuel, start ≤ diagonalDepthAux c start fuel
  | start, 0 => by rfl
  | start, fuel + 1 => by
      by_cases h : start < frobeniusColumnHeight c start
      · simp only [diagonalDepthAux, h, ↓reduceIte]
        exact le_trans (Nat.le_succ start)
          (diagonalDepthAux_ge_start c (start + 1) fuel)
      · simp [diagonalDepthAux, h]

/-- 対角走査は与えた fuel を越えない。 -/
theorem diagonalDepthAux_le_start_add
    (c : WidthDropCode) :
    ∀ start fuel,
      diagonalDepthAux c start fuel ≤ start + fuel
  | start, 0 => by simp [diagonalDepthAux]
  | start, fuel + 1 => by
      by_cases h : start < frobeniusColumnHeight c start
      · simp only [diagonalDepthAux, h, ↓reduceIte]
        have ih := diagonalDepthAux_le_start_add c (start + 1) fuel
        omega
      · simp [diagonalDepthAux, h]

/-- 走査結果より手前の index では必ず対角 cell が存在する。 -/
theorem diagonal_of_lt_diagonalDepthAux
    (c : WidthDropCode) :
    ∀ start fuel i,
      start ≤ i →
      i < diagonalDepthAux c start fuel →
      i < frobeniusColumnHeight c i
  | start, 0, i, hsi, hi => by
      simp [diagonalDepthAux] at hi
      omega
  | start, fuel + 1, i, hsi, hi => by
      by_cases h : start < frobeniusColumnHeight c start
      · simp only [diagonalDepthAux, h, ↓reduceIte] at hi
        by_cases his : i = start
        · simpa [his] using h
        · have hnext : start + 1 ≤ i := by omega
          exact diagonal_of_lt_diagonalDepthAux c (start + 1) fuel i hnext hi
      · simp [diagonalDepthAux, h] at hi
        omega

/-- fuel を使い切る前に止まったなら、その停止位置には対角 cell がない。 -/
theorem columnHeight_le_of_diagonalDepthAux_lt
    (c : WidthDropCode) :
    ∀ start fuel,
      diagonalDepthAux c start fuel < start + fuel →
      frobeniusColumnHeight c (diagonalDepthAux c start fuel) ≤
        diagonalDepthAux c start fuel
  | start, 0, h => by
      simp [diagonalDepthAux] at h
  | start, fuel + 1, hlt => by
      by_cases h : start < frobeniusColumnHeight c start
      · simp only [diagonalDepthAux, h, ↓reduceIte] at hlt ⊢
        have htail :
            diagonalDepthAux c (start + 1) fuel < (start + 1) + fuel := by
          omega
        exact columnHeight_le_of_diagonalDepthAux_lt c (start + 1) fuel htail
      · simp [diagonalDepthAux, h]
        omega

/-- Frobenius depth は図形の横幅以下。 -/
theorem frobeniusDepth_le_codeWidth
    (c : WidthDropCode) :
    frobeniusDepth c ≤ codeWidth c := by
  simpa [frobeniusDepth] using
    diagonalDepthAux_le_start_add c 0 (codeWidth c)

/-- `i < Frobenius depth` なら元図形の `(i,i)` cell が存在する。 -/
theorem frobeniusColumn_diagonal
    (c : WidthDropCode)
    {i : ℕ}
    (hi : i < frobeniusDepth c) :
    i < frobeniusColumnHeight c i := by
  exact diagonal_of_lt_diagonalDepthAux c 0 (codeWidth c) i (Nat.zero_le i) hi

/-- Frobenius depth は全縦高以下。 -/
theorem frobeniusDepth_le_codeDropSum
    (c : WidthDropCode) :
    frobeniusDepth c ≤ codeDropSum c := by
  by_cases hD : frobeniusDepth c = 0
  · simp [hD]
  · let i := frobeniusDepth c - 1
    have hDpos : 0 < frobeniusDepth c := by
      exact Nat.pos_of_ne_zero hD
    have hi : i < frobeniusDepth c := by
      dsimp [i]
      omega
    have hdiag :=
      frobeniusColumn_diagonal c hi
    have hbound :=
      columnHeightFromWidthDropCode_le_dropSum c i
    have hdiag' :
        frobeniusDepth c - 1 <
          columnHeightFromWidthDropCode c
            (frobeniusDepth c - 1) := by
      simpa [frobeniusColumnHeight, i] using hdiag
    have hbound' :
        columnHeightFromWidthDropCode c
            (frobeniusDepth c - 1) ≤
          codeDropSum c := by
      simpa [i] using hbound
    omega

/-- `i < Frobenius depth` なら共役側にも同じ対角 cell が存在する。 -/
theorem frobeniusRow_diagonal
    (c : WidthDropCode)
    {i : ℕ}
    (hi : i < frobeniusDepth c) :
    i < frobeniusRowLength c i := by
  have hiW : i < codeWidth c :=
    lt_of_lt_of_le hi (frobeniusDepth_le_codeWidth c)
  have hcol := frobeniusColumn_diagonal c hi
  have hiH : i < codeDropSum c :=
    lt_of_lt_of_le hi (frobeniusDepth_le_codeDropSum c)
  have hcell :=
    (coordinateConjugate_hasCell_iff
      c ⟨i, hiW⟩ ⟨i, hiH⟩).2
      hcol
  simpa [Combinatorics.HasCell, coordinateConjugateShape,
    frobeniusRowLength] using hcell

/-- Frobenius depth が横幅より小さいなら、その位置で対角線が止まる。 -/
theorem frobeniusColumnHeight_le_depth_of_lt_width
    (c : WidthDropCode)
    (h : frobeniusDepth c < codeWidth c) :
    frobeniusColumnHeight c (frobeniusDepth c) ≤ frobeniusDepth c := by
  exact columnHeight_le_of_diagonalDepthAux_lt c 0 (codeWidth c) (by simpa [frobeniusDepth] using h)

/-- classical Durfee scan の一つの候補。 -/
def durfeeCandidateAt
    (leftWidth : ℕ)
    (xs : List ℕ)
    (j : ℕ) : ℕ :=
  min (leftWidth + j + 1) (xs.getD j 0)

/-- 任意の有効 index の候補は classical Durfee scan 以下。 -/
theorem durfeeCandidateAt_le_classicalDurfeeFromColumns
    (leftWidth : ℕ) :
    ∀ (xs : List ℕ) (j : ℕ),
      j < xs.length →
      durfeeCandidateAt leftWidth xs j ≤
        classicalDurfeeFromColumns leftWidth xs
  | [], j, hj => by simp at hj
  | x :: xs, 0, _hj => by
      simp [durfeeCandidateAt, classicalDurfeeFromColumns]
  | x :: xs, j + 1, hj => by
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hj
      have ih :=
        durfeeCandidateAt_le_classicalDurfeeFromColumns
          (leftWidth + 1) xs j hj
      have htail :
          classicalDurfeeFromColumns (leftWidth + 1) xs ≤
            classicalDurfeeFromColumns leftWidth (x :: xs) := by
        simp [classicalDurfeeFromColumns]
      have hcand :
          durfeeCandidateAt leftWidth (x :: xs) (j + 1) =
            durfeeCandidateAt (leftWidth + 1) xs j := by
        simp [durfeeCandidateAt]
        congr 1
        omega
      rw [hcand]
      exact le_trans ih htail

/-- 全候補が `B` 以下なら classical Durfee scan も `B` 以下。 -/
theorem classicalDurfeeFromColumns_le_of_candidates_le
    (leftWidth B : ℕ) :
    ∀ xs : List ℕ,
      (∀ j < xs.length, durfeeCandidateAt leftWidth xs j ≤ B) →
      classicalDurfeeFromColumns leftWidth xs ≤ B
  | [], _h => by simp [classicalDurfeeFromColumns]
  | x :: xs, h => by
      have h0 := h 0 (by simp)
      have htail :
          ∀ j < xs.length,
            durfeeCandidateAt (leftWidth + 1) xs j ≤ B := by
        intro j hj
        have hs := h (j + 1) (by simp [hj])
        simpa [durfeeCandidateAt, List.getD_cons_succ, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using hs
      have ih :=
        classicalDurfeeFromColumns_le_of_candidates_le
          (leftWidth + 1) B xs htail
      simp only [classicalDurfeeFromColumns]
      exact max_le h0 ih

/-- 対角線走査で得た depth は既存 genuine Durfee size と一致する。 -/
theorem frobeniusDepth_eq_genuineDurfeeSize
    (c : WidthDropCode) :
    frobeniusDepth c = genuineDurfeeSize c := by
  let xs := columnListFromWidthDropCode c
  let D := frobeniusDepth c
  have hLen : xs.length = codeWidth c := by
    simpa [xs] using columnListFromWidthDropCode_length c
  have hUpper :
      classicalDurfeeFromColumns 0 xs ≤ D := by
    apply classicalDurfeeFromColumns_le_of_candidates_le 0 D xs
    intro j hj
    have hjW : j < codeWidth c := by simpa [hLen] using hj
    unfold durfeeCandidateAt
    rw [show xs.getD j 0 = frobeniusColumnHeight c j by
      simpa [xs, frobeniusColumnHeight] using getD_columnListFromWidthDropCode c j]
    by_cases hjD : j < D
    · have hJD : j + 1 ≤ D := by
        omega
      exact
        le_trans
          (min_le_left _ _)
          (by simpa using hJD)
    · have hDj : D ≤ j := le_of_not_gt hjD
      have hDlt : D < codeWidth c := by
        by_contra hnot
        have hDW : codeWidth c ≤ D := le_of_not_gt hnot
        omega
      have hstop := frobeniusColumnHeight_le_depth_of_lt_width c hDlt
      have hmono :
          frobeniusColumnHeight c j ≤ frobeniusColumnHeight c D := by
        exact columnHeightFromWidthDropCode_antitone c hDj
      exact le_trans (min_le_right _ _) (le_trans hmono hstop)
  have hLower :
      D ≤ classicalDurfeeFromColumns 0 xs := by
    by_cases hD0 : D = 0
    · simp [hD0]
    · let j := D - 1
      have hjD : j < D := by
        dsimp [j]
        omega
      have hjW : j < codeWidth c :=
        lt_of_lt_of_le hjD (frobeniusDepth_le_codeWidth c)
      have hjLen : j < xs.length := by simpa [hLen] using hjW
      have hcand :=
        durfeeCandidateAt_le_classicalDurfeeFromColumns 0 xs j hjLen
      have hdiag := frobeniusColumn_diagonal c hjD
      have hget : xs.getD j 0 = frobeniusColumnHeight c j := by
        simpa [xs, frobeniusColumnHeight] using
          getD_columnListFromWidthDropCode c j
      have hcandEq : durfeeCandidateAt 0 xs j = D := by
        rw [durfeeCandidateAt, hget]
        dsimp [j]
        have hOne : 1 ≤ D := by
          omega
        have hIdx : D - 1 + 1 = D :=
          Nat.sub_add_cancel hOne
        simp only [Nat.zero_add]
        rw [hIdx]
        have hdiag' :
            D - 1 <
              frobeniusColumnHeight c (D - 1) := by
          simpa [j] using hdiag
        have hheight :
            D ≤ frobeniusColumnHeight c (D - 1) := by
          omega
        exact min_eq_left hheight
      rw [hcandEq] at hcand
      exact hcand
  unfold genuineDurfeeSize
  change D = classicalDurfeeFromColumns 0 xs
  omega

/-- Frobenius arm 長。 -/
def frobeniusArmAt (c : WidthDropCode) (i : ℕ) : ℕ :=
  frobeniusRowLength c i - (i + 1)

/-- Frobenius leg 長。 -/
def frobeniusLegAt (c : WidthDropCode) (i : ℕ) : ℕ :=
  frobeniusColumnHeight c i - (i + 1)

/-- `start` から `n` 個の arm を並べる。 -/
def frobeniusArmsFrom (c : WidthDropCode) : ℕ → ℕ → List ℕ
  | _start, 0 => []
  | start, n + 1 =>
      frobeniusArmAt c start :: frobeniusArmsFrom c (start + 1) n

/-- `start` から `n` 個の leg を並べる。 -/
def frobeniusLegsFrom (c : WidthDropCode) : ℕ → ℕ → List ℕ
  | _start, 0 => []
  | start, n + 1 =>
      frobeniusLegAt c start :: frobeniusLegsFrom c (start + 1) n

/-- genuine Frobenius arm vector。 -/
def frobeniusArms (c : WidthDropCode) : List ℕ :=
  frobeniusArmsFrom c 0 (frobeniusDepth c)

/-- genuine Frobenius leg vector。 -/
def frobeniusLegs (c : WidthDropCode) : List ℕ :=
  frobeniusLegsFrom c 0 (frobeniusDepth c)

@[simp] theorem frobeniusArmsFrom_length
    (c : WidthDropCode) :
    ∀ start n, (frobeniusArmsFrom c start n).length = n
  | _start, 0 => rfl
  | start, n + 1 => by
      simp [frobeniusArmsFrom, frobeniusArmsFrom_length c (start + 1) n]

@[simp] theorem frobeniusLegsFrom_length
    (c : WidthDropCode) :
    ∀ start n, (frobeniusLegsFrom c start n).length = n
  | _start, 0 => rfl
  | start, n + 1 => by
      simp [frobeniusLegsFrom, frobeniusLegsFrom_length c (start + 1) n]

@[simp] theorem frobeniusArms_length
    (c : WidthDropCode) :
    (frobeniusArms c).length = frobeniusDepth c := by
  simp [frobeniusArms]

@[simp] theorem frobeniusLegs_length
    (c : WidthDropCode) :
    (frobeniusLegs c).length = frobeniusDepth c := by
  simp [frobeniusLegs]

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/-- RecordFerrers の既存 Durfee size は Frobenius depth と同じ。 -/
theorem rankDurfeeSize_eq_frobeniusDepth
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    R.rankDurfeeSize = frobeniusDepth R.plateauWidthDropCode := by
  rw [R.rankDurfeeSize_eq_genuineDurfeeSize]
  exact (frobeniusDepth_eq_genuineDurfeeSize R.plateauWidthDropCode).symm

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
