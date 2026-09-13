import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.BasisMinimality
import Mathlib.Tactic.Ring

/-!
# Collatz3 Experimental2: Frobenius basis lower bound と RecordFerrers

一般 basis minimality を、実際の Young/Ferrers 図形の Frobenius symbol へ適用する。

このファイルの要点は二つ。

1. genuine Frobenius arm / leg は `IsArmRealization` を満たす。
2. Frobenius symbol weight は既存 `codeArea` と exact に一致する。

従って successive rank vector だけから作る `basisWeightZ` は actual Young 面積の下界になる。
RecordFerrers では右辺が既存 `youngCellCount` そのものになる。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- arm の隣接差は少なくとも1。 -/
theorem frobeniusArmAt_succ_add_one_le
    (c : WidthDropCode)
    {i : ℕ}
    (h : i + 2 ≤ frobeniusDepth c) :
    frobeniusArmAt c (i + 1) + 1 ≤ frobeniusArmAt c i := by
  have hi1 : i + 1 < frobeniusDepth c := by omega
  have hrow1 := frobeniusRow_diagonal c hi1
  have hmono :
      frobeniusRowLength c (i + 1) ≤ frobeniusRowLength c i := by
    exact columnHeightFromWidthDropCode_antitone
      (conjugateWidthDropCode c) (by omega)
  unfold frobeniusArmAt
  omega

/-- leg の隣接差も少なくとも1。 -/
theorem frobeniusLegAt_succ_add_one_le
    (c : WidthDropCode)
    {i : ℕ}
    (h : i + 2 ≤ frobeniusDepth c) :
    frobeniusLegAt c (i + 1) + 1 ≤ frobeniusLegAt c i := by
  have hi1 : i + 1 < frobeniusDepth c := by omega
  have hcol1 := frobeniusColumn_diagonal c hi1
  have hmono :
      frobeniusColumnHeight c (i + 1) ≤ frobeniusColumnHeight c i := by
    exact columnHeightFromWidthDropCode_antitone c (by omega)
  unfold frobeniusLegAt
  omega

/--
Frobenius successive rank / arm の任意の連続区間は abstract `IsArmRealization` を満たす。
-/
theorem frobeniusVectors_realize_from
    (c : WidthDropCode) :
    ∀ start n,
      start + n ≤ frobeniusDepth c →
      IsArmRealization
        (successiveRankVectorFrom c start n)
        (frobeniusArmsZFrom c start n)
  | _start, 0, _h => by
      exact IsArmRealization.nil
  | start, 1, _h => by
      simp only [successiveRankVectorFrom, frobeniusArmsZFrom]
      apply IsArmRealization.single
      · positivity
      · unfold frobeniusRankAt
        have hleg : (0 : ℤ) ≤ (frobeniusLegAt c start : ℤ) := by positivity
        omega
  | start, n + 2, h => by
      have hTail :
          IsArmRealization
            (successiveRankVectorFrom c (start + 1) (n + 1))
            (frobeniusArmsZFrom c (start + 1) (n + 1)) := by
        apply frobeniusVectors_realize_from c (start + 1) (n + 1)
        omega
      simp only [successiveRankVectorFrom, frobeniusArmsZFrom]
      apply IsArmRealization.cons hTail
      · positivity
      · unfold frobeniusRankAt
        have hleg : (0 : ℤ) ≤ (frobeniusLegAt c start : ℤ) := by positivity
        omega
      · have hArm :=
          frobeniusArmAt_succ_add_one_le c
            (i := start) (by omega)
        exact_mod_cast hArm
      · have hLeg :=
          frobeniusLegAt_succ_add_one_le c
            (i := start) (by omega)
        have hLegZ :
            (frobeniusLegAt c (start + 1) : ℤ) + 1 ≤
              (frobeniusLegAt c start : ℤ) := by
          exact_mod_cast hLeg
        unfold frobeniusRankAt
        omega

/-- actual Frobenius vector 全体は successive rank を genuine に実現する。 -/
theorem frobeniusVectors_realize
    (c : WidthDropCode) :
    IsArmRealization
      (successiveRankVector c)
      (frobeniusArmsZ c) := by
  unfold successiveRankVector frobeniusArmsZ
  exact frobeniusVectors_realize_from c 0 (frobeniusDepth c) (by simp)

/-- 高さの連続和。 -/
def columnMassFrom
    (c : WidthDropCode) : ℕ → ℕ → ℕ
  | _start, 0 => 0
  | start, n + 1 =>
      frobeniusColumnHeight c start +
        columnMassFrom c (start + 1) n

/-- 行長の連続和。 -/
def rowMassFrom
    (c : WidthDropCode) : ℕ → ℕ → ℕ
  | _start, 0 => 0
  | start, n + 1 =>
      frobeniusRowLength c start +
        rowMassFrom c (start + 1) n

/-- `start+1,...,start+n` の staircase 和。 -/
def staircaseMassFrom : ℕ → ℕ → ℕ
  | _start, 0 => 0
  | start, n + 1 =>
      (start + 1) + staircaseMassFrom (start + 1) n

/-- prefix column mass を一列伸ばす差分。 -/
theorem prefixColumnMass_succ_eq
    (c : WidthDropCode)
    (k : ℕ) :
    prefixColumnMass c (k + 1) =
      prefixColumnMass c k + frobeniusColumnHeight c k := by
  unfold prefixColumnMass
  rw [sum_take_succ_eq_sum_take_add_getD]
  rw [getD_columnListFromWidthDropCode]
  rfl

/-- prefix row mass を一行伸ばす差分。 -/
theorem prefixRowMass_succ_eq
    (c : WidthDropCode)
    (k : ℕ) :
    prefixColumnMass (conjugateWidthDropCode c) (k + 1) =
      prefixColumnMass (conjugateWidthDropCode c) k +
        frobeniusRowLength c k := by
  simpa [frobeniusRowLength, frobeniusColumnHeight] using
    prefixColumnMass_succ_eq (conjugateWidthDropCode c) k

/-- 連続 column mass は二つの prefix mass の差分を加法的に表す。 -/
theorem columnMassFrom_add_prefix
    (c : WidthDropCode) :
    ∀ start n,
      columnMassFrom c start n + prefixColumnMass c start =
        prefixColumnMass c (start + n)
  | start, 0 => by simp [columnMassFrom]
  | start, n + 1 => by
      have ih := columnMassFrom_add_prefix c (start + 1) n
      rw [prefixColumnMass_succ_eq c start] at ih
      simp only [columnMassFrom]
      rw [Nat.add_assoc]
      have hidx : start + (n + 1) = (start + 1) + n := by omega
      rw [hidx]
      omega

/-- 連続 row mass についても同じ。 -/
theorem rowMassFrom_add_prefix
    (c : WidthDropCode) :
    ∀ start n,
      rowMassFrom c start n +
          prefixColumnMass (conjugateWidthDropCode c) start =
        prefixColumnMass (conjugateWidthDropCode c) (start + n)
  | start, 0 => by simp [rowMassFrom]
  | start, n + 1 => by
      have ih := rowMassFrom_add_prefix c (start + 1) n
      rw [prefixRowMass_succ_eq c start] at ih
      simp only [rowMassFrom]
      have hidx : start + (n + 1) = (start + 1) + n := by omega
      rw [hidx]
      omega

/-- staircase 和の閉じた二倍公式。 -/
theorem two_mul_staircaseMassFrom
    (start : ℕ) :
    ∀ n : ℕ,
      2 * staircaseMassFrom start n =
        n * (2 * start + n + 1)
  | 0 => by
      simp [staircaseMassFrom]
  | n + 1 => by
      rw [staircaseMassFrom]
      rw [Nat.mul_add]
      rw [two_mul_staircaseMassFrom (start + 1) n]
      ring

/-- arm の和 = row mass - staircase mass。 -/
theorem sum_frobeniusArmsZFrom
    (c : WidthDropCode) :
    ∀ start n,
      start + n ≤ frobeniusDepth c →
      (frobeniusArmsZFrom c start n).sum =
        (rowMassFrom c start n : ℤ) -
          (staircaseMassFrom start n : ℤ)
  | _start, 0, _h => by simp [frobeniusArmsZFrom, rowMassFrom, staircaseMassFrom]
  | start, n + 1, h => by
      have hdiag : start < frobeniusDepth c := by omega
      have hrow : start + 1 ≤ frobeniusRowLength c start :=
        Nat.succ_le_iff.mpr (frobeniusRow_diagonal c hdiag)
      have ih := sum_frobeniusArmsZFrom c (start + 1) n (by omega)
      simp only [frobeniusArmsZFrom, List.sum_cons, frobeniusArmAt,
        rowMassFrom, staircaseMassFrom]
      rw [Nat.cast_sub hrow, ih]
      push_cast
      ring

/-- leg の和 = column mass - staircase mass。 -/
theorem sum_frobeniusLegsZFrom
    (c : WidthDropCode) :
    ∀ start n,
      start + n ≤ frobeniusDepth c →
      (frobeniusLegsZFrom c start n).sum =
        (columnMassFrom c start n : ℤ) -
          (staircaseMassFrom start n : ℤ)
  | _start, 0, _h => by simp [frobeniusLegsZFrom, columnMassFrom, staircaseMassFrom]
  | start, n + 1, h => by
      have hdiag : start < frobeniusDepth c := by omega
      have hcol : start + 1 ≤ frobeniusColumnHeight c start :=
        Nat.succ_le_iff.mpr (frobeniusColumn_diagonal c hdiag)
      have ih := sum_frobeniusLegsZFrom c (start + 1) n (by omega)
      simp only [frobeniusLegsZFrom, List.sum_cons, frobeniusLegAt,
        columnMassFrom, staircaseMassFrom]
      rw [Nat.cast_sub hcol, ih]
      push_cast
      ring

/-- successive rank の和は arm 和 - leg 和。 -/
theorem sum_successiveRankVectorFrom
    (c : WidthDropCode) :
    ∀ start n,
      (successiveRankVectorFrom c start n).sum =
        (frobeniusArmsZFrom c start n).sum -
          (frobeniusLegsZFrom c start n).sum
  | _start, 0 => by simp [successiveRankVectorFrom, frobeniusArmsZFrom, frobeniusLegsZFrom]
  | start, n + 1 => by
      simp only [successiveRankVectorFrom, frobeniusArmsZFrom,
        frobeniusLegsZFrom, List.sum_cons, frobeniusRankAt]
      rw [sum_successiveRankVectorFrom c (start + 1) n]
      ring

/-- Frobenius depth より左の列高はすべて depth 以上。 -/
theorem frobeniusDepth_le_columnHeight_of_lt
    (c : WidthDropCode)
    {i : ℕ}
    (hi : i < frobeniusDepth c) :
    frobeniusDepth c ≤ frobeniusColumnHeight c i := by
  by_cases hD : frobeniusDepth c = 0
  · simp [hD]
  · let j := frobeniusDepth c - 1
    have hDpos : 0 < frobeniusDepth c := by
      exact Nat.pos_of_ne_zero hD
    have hj : j < frobeniusDepth c := by
      dsimp [j]
      omega
    have hdiag :=
      frobeniusColumn_diagonal c hj
    have hij : i ≤ j := by
      dsimp [j]
      omega
    have hmono :
        frobeniusColumnHeight c j ≤
          frobeniusColumnHeight c i :=
      columnHeightFromWidthDropCode_antitone c hij
    have hdiag' :
        frobeniusDepth c - 1 <
          frobeniusColumnHeight c (frobeniusDepth c - 1) := by
      simpa [j] using hdiag
    have hmono' :
        frobeniusColumnHeight c (frobeniusDepth c - 1) ≤
          frobeniusColumnHeight c i := by
      simpa [j] using hmono
    have hlast :
        frobeniusDepth c ≤
          frobeniusColumnHeight c (frobeniusDepth c - 1) := by
      omega
    exact le_trans hlast hmono'

/-- depth 以後の有効列高は depth 以下。 -/
theorem columnHeight_le_frobeniusDepth_of_ge
    (c : WidthDropCode)
    {i : ℕ}
    (hDi : frobeniusDepth c ≤ i)
    (hiW : i < codeWidth c) :
    frobeniusColumnHeight c i ≤ frobeniusDepth c := by
  have hDlt : frobeniusDepth c < codeWidth c := lt_of_le_of_lt hDi hiW
  have hstop := frobeniusColumnHeight_le_depth_of_lt_width c hDlt
  exact le_trans (columnHeightFromWidthDropCode_antitone c hDi) hstop

/--
一般 list を高さ `cut`、prefix 長 `k` で切る補題。
最初の `k` 要素が `cut` 以上、残りが `cut` 以下なら、truncated mass は
`cut*k + tail sum` になる。
-/
theorem truncatedMass_eq_mul_add_drop_of_cut
    (cut : ℕ) :
    ∀ (k : ℕ) (xs : List ℕ),
      k ≤ xs.length →
      (∀ j < k, cut ≤ xs.getD j 0) →
      (∀ j, k ≤ j → j < xs.length → xs.getD j 0 ≤ cut) →
      truncatedMass cut xs = cut * k + (xs.drop k).sum
  | 0, [], _hk, _hpre, _htail => by
      rfl
  | 0, x :: xs, _hk, _hpre, htail => by
      have hx : x ≤ cut := by
        simpa using htail 0 (by omega) (by simp)
      have htail' :
          ∀ j, 0 ≤ j → j < xs.length → xs.getD j 0 ≤ cut := by
        intro j _hj0 hj
        have h := htail (j + 1) (by omega) (by simp [hj])
        simpa [List.getD_cons_succ] using h
      have ih := truncatedMass_eq_mul_add_drop_of_cut cut 0 xs
        (by simp) (by intro j hj; omega) htail'
      simp [truncatedMass, min_eq_right hx, ih]
  | k + 1, [], hk, _hpre, _htail => by
      simp at hk
  | k + 1, x :: xs, hk, hpre, htail => by
      have hx : cut ≤ x := by
        simpa using hpre 0 (by omega)
      have hk' : k ≤ xs.length := by
        simpa using hk
      have hpre' : ∀ j < k, cut ≤ xs.getD j 0 := by
        intro j hj
        have h := hpre (j + 1) (by omega)
        simpa [List.getD_cons_succ] using h
      have htail' :
          ∀ j, k ≤ j → j < xs.length → xs.getD j 0 ≤ cut := by
        intro j hkj hj
        have h := htail (j + 1) (by omega) (by simp [hj])
        simpa [List.getD_cons_succ] using h
      have ih :=
        truncatedMass_eq_mul_add_drop_of_cut cut k xs hk' hpre' htail'
      simp only [truncatedMass, min_eq_left hx, List.drop_succ_cons]
      rw [ih]
      rw [Nat.mul_succ]
      omega

/--
Frobenius depth `D` で切ると、row-prefix と column-prefix の和は
全 cell 数に `D²` を足したものになる。
-/
theorem frobenius_prefix_union
    (c : WidthDropCode) :
    prefixColumnMass (conjugateWidthDropCode c) (frobeniusDepth c) +
        prefixColumnMass c (frobeniusDepth c) =
      codeArea c + frobeniusDepth c * frobeniusDepth c := by
  let xs := columnListFromWidthDropCode c
  let D := frobeniusDepth c
  have hLen : xs.length = codeWidth c := by
    simpa [xs] using columnListFromWidthDropCode_length c
  have hDLen : D ≤ xs.length := by
    simpa [D, hLen] using frobeniusDepth_le_codeWidth c
  have hpre : ∀ j < D, D ≤ xs.getD j 0 := by
    intro j hj
    have hget : xs.getD j 0 = frobeniusColumnHeight c j := by
      simpa [xs, frobeniusColumnHeight] using
        getD_columnListFromWidthDropCode c j
    rw [hget]
    exact frobeniusDepth_le_columnHeight_of_lt c hj
  have htail :
      ∀ j, D ≤ j → j < xs.length → xs.getD j 0 ≤ D := by
    intro j hDj hj
    have hjW : j < codeWidth c := by simpa [hLen] using hj
    have hget : xs.getD j 0 = frobeniusColumnHeight c j := by
      simpa [xs, frobeniusColumnHeight] using
        getD_columnListFromWidthDropCode c j
    rw [hget]
    exact columnHeight_le_frobeniusDepth_of_ge c hDj hjW
  have hTrunc :=
    truncatedMass_eq_mul_add_drop_of_cut D D xs hDLen hpre htail
  have hRow :
      prefixColumnMass (conjugateWidthDropCode c) D =
        truncatedMass D xs := by
    simpa [D, xs, columnPartitionOfCode] using
      prefixColumnMass_conjugate_eq_truncatedMass c D
  have hCol :
      prefixColumnMass c D = (xs.take D).sum := by
    rfl
  have hSplit :
      (xs.take D).sum + (xs.drop D).sum = xs.sum := by
    rw [← List.sum_append, List.take_append_drop]
  have hArea : xs.sum = codeArea c := by
    simpa [xs] using columnListFromWidthDropCode_sum c
  rw [hRow, hCol, hTrunc]
  rw [hArea] at hSplit
  dsimp [D] at *
  omega

/--
actual Frobenius symbol weight は既存 Young 面積と exact に一致する。
-/
theorem frobeniusSymbolWeight_eq_codeArea
    (c : WidthDropCode) :
    symbolWeightZ (successiveRankVector c) (frobeniusArmsZ c) =
      (codeArea c : ℤ) := by
  let D := frobeniusDepth c
  have hArm :=
    sum_frobeniusArmsZFrom c 0 D (by simp [D])
  have hLeg :=
    sum_frobeniusLegsZFrom c 0 D (by simp [D])
  have hRank :=
    sum_successiveRankVectorFrom c 0 D
  have hColMass :=
    columnMassFrom_add_prefix c 0 D
  have hRowMass :=
    rowMassFrom_add_prefix c 0 D
  have hStair :=
    two_mul_staircaseMassFrom 0 D
  have hUnion :=
    frobenius_prefix_union c
  have hStairNat :
      2 * staircaseMassFrom 0 D =
        D * (D + 1) := by
    simpa using hStair
  have hStairZ :
      (2 : ℤ) * (staircaseMassFrom 0 D : ℤ) =
        (D : ℤ) * ((D : ℤ) + 1) := by
    exact_mod_cast hStairNat
  have hColMass0 :
      columnMassFrom c 0 D =
        prefixColumnMass c D := by
    simpa [prefixColumnMass] using hColMass
  have hRowMass0 :
      rowMassFrom c 0 D =
        prefixColumnMass (conjugateWidthDropCode c) D := by
    simpa [prefixColumnMass] using hRowMass
  change
    symbolWeightZ
      (successiveRankVectorFrom c 0 D)
      (frobeniusArmsZFrom c 0 D) =
        (codeArea c : ℤ)
  unfold symbolWeightZ
  rw [successiveRankVectorFrom_length]
  rw [hRank, hArm, hLeg]
  rw [hColMass0, hRowMass0]
  have hUnionZ :
      (prefixColumnMass (conjugateWidthDropCode c) D : ℤ) +
          (prefixColumnMass c D : ℤ) =
        (codeArea c : ℤ) +
          (D : ℤ) * (D : ℤ) := by
    exact_mod_cast hUnion
  ring_nf at hStairZ hUnionZ ⊢
  linarith

/-- F5: basis weight は任意 Young/Ferrers code の actual cell 数以下。 -/
theorem basisWeightZ_le_codeArea
    (c : WidthDropCode) :
    basisWeightZ (successiveRankVector c) ≤ (codeArea c : ℤ) := by
  have hMin := basisWeightZ_le_symbolWeightZ (frobeniusVectors_realize c)
  rw [frobeniusSymbolWeight_eq_codeArea] at hMin
  exact hMin

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/--
F5 の RecordFerrers 版。
successive rank vector だけから決まる basis weight は rank-envelope Young 面積以下。
-/
theorem basisWeightZ_le_youngCellCount
    {β : ℕ → ℕ}
    {m : ℕ}
    (R : RecordFerrers β m) :
    basisWeightZ R.successiveRanks ≤ (R.youngCellCount : ℤ) := by
  unfold successiveRanks youngCellCount
  exact basisWeightZ_le_codeArea R.plateauWidthDropCode

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
