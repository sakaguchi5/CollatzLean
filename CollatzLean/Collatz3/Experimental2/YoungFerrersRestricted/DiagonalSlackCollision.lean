import CollatzLean.Collatz3.Experimental2.YoungFerrersRestricted.BasisExcessDecomposition

/-!
# Collatz3 Experimental2: diagonal slack と boundary collision の定量化

F12 では actual-basis 面積差を recurrence slack の weighted sum の2倍として分解した。
本ファイルではその抽象 slack を Young 図形の対角幾何へ戻す。

internal diagonal `i` では

* arm 側 slack = row length の落差
* leg 側 slack = column height の落差

であり、basis recurrence が採用する slack は両者の小さい方である。
従って F8 の simultaneous boundary collision は internal slack が正であることと exact に同値。

さらに collision level `t` の slack は左側 `t` 個の arm excess へ伝播するため、
weighted basis excess は少なくとも `t`。
したがって RecordFerrers では

`collision at t  ->  actual area - basis area >= 2*t`

まで定量化できる。
-/

namespace Collatz3
namespace Experimental2
namespace YoungFerrersRestricted

/-- internal diagonal step の幾何 slack。row/column の落差の小さい方。 -/
def internalDiagonalSlack
    (c : WidthDropCode)
    (i : ℕ) : ℕ :=
  min
    (frobeniusRowLength c i - frobeniusRowLength c (i + 1))
    (frobeniusColumnHeight c i - frobeniusColumnHeight c (i + 1))

/-- terminal diagonal step の幾何 slack。arm / leg の小さい方。 -/
def terminalDiagonalSlack
    (c : WidthDropCode)
    (i : ℕ) : ℕ :=
  min (frobeniusArmAt c i) (frobeniusLegAt c i)

/--
internal basis recurrence slack は row/column plateau drop の minimum と exact に一致する。
-/
theorem stepBasisSlack_frobenius_eq_internalDiagonalSlack
    (c : WidthDropCode)
    (i : ℕ)
    (hDepth : i + 2 ≤ frobeniusDepth c) :
    stepBasisSlack
        (frobeniusRankAt c i)
        (frobeniusRankAt c (i + 1))
        (frobeniusArmAt c i : ℤ)
        (frobeniusArmAt c (i + 1) : ℤ) =
      (internalDiagonalSlack c i : ℤ) := by
  have hi : i < frobeniusDepth c := by omega
  have hi1 : i + 1 < frobeniusDepth c := by omega
  have hRow0 : i + 1 ≤ frobeniusRowLength c i :=
    Nat.succ_le_iff.mpr (frobeniusRow_diagonal c hi)
  have hRow1 : i + 2 ≤ frobeniusRowLength c (i + 1) := by
    have h := frobeniusRow_diagonal c hi1
    omega
  have hCol0 : i + 1 ≤ frobeniusColumnHeight c i :=
    Nat.succ_le_iff.mpr (frobeniusColumn_diagonal c hi)
  have hCol1 : i + 2 ≤ frobeniusColumnHeight c (i + 1) := by
    have h := frobeniusColumn_diagonal c hi1
    omega
  have hRowMono :
      frobeniusRowLength c (i + 1) ≤ frobeniusRowLength c i := by
    exact
      columnHeightFromWidthDropCode_antitone
        (conjugateWidthDropCode c) (Nat.le_succ i)
  have hColMono :
      frobeniusColumnHeight c (i + 1) ≤ frobeniusColumnHeight c i := by
    exact columnHeightFromWidthDropCode_antitone c (Nat.le_succ i)
  have hArmGap :
      (frobeniusArmAt c i : ℤ) -
          ((frobeniusArmAt c (i + 1) : ℤ) + 1) =
        (frobeniusRowLength c i - frobeniusRowLength c (i + 1) : ℕ) := by
    unfold frobeniusArmAt
    rw [Nat.cast_sub hRow0, Nat.cast_sub hRow1, Nat.cast_sub hRowMono]
    push_cast
    ring
  have hLegGap :
      (frobeniusLegAt c i : ℤ) -
          ((frobeniusLegAt c (i + 1) : ℤ) + 1) =
        (frobeniusColumnHeight c i - frobeniusColumnHeight c (i + 1) : ℕ) := by
    unfold frobeniusLegAt
    rw [Nat.cast_sub hCol0, Nat.cast_sub hCol1, Nat.cast_sub hColMono]
    push_cast
    ring
  by_cases hRank : frobeniusRankAt c i ≤ frobeniusRankAt c (i + 1)
  · have hGapLeZ :
        (frobeniusRowLength c i - frobeniusRowLength c (i + 1) : ℕ) ≤
          (frobeniusColumnHeight c i - frobeniusColumnHeight c (i + 1) : ℕ) := by
      have hGapLeInt :
          ((frobeniusRowLength c i - frobeniusRowLength c (i + 1) : ℕ) : ℤ) ≤
            ((frobeniusColumnHeight c i - frobeniusColumnHeight c (i + 1) : ℕ) : ℤ) := by
        unfold frobeniusRankAt at hRank
        omega
      exact_mod_cast hGapLeInt
    unfold stepBasisSlack internalDiagonalSlack
    rw [ite_eq_left hRank, min_eq_left hGapLeZ]
    exact hArmGap
  · have hRank' : frobeniusRankAt c (i + 1) < frobeniusRankAt c i :=
      lt_of_not_ge hRank
    have hGapLeZ :
        (frobeniusColumnHeight c i - frobeniusColumnHeight c (i + 1) : ℕ) ≤
          (frobeniusRowLength c i - frobeniusRowLength c (i + 1) : ℕ) := by
      have hGapLeInt :
          ((frobeniusColumnHeight c i - frobeniusColumnHeight c (i + 1) : ℕ) : ℤ) ≤
            ((frobeniusRowLength c i - frobeniusRowLength c (i + 1) : ℕ) : ℤ) := by
        unfold frobeniusRankAt at hRank'
        omega
      exact_mod_cast hGapLeInt
    unfold stepBasisSlack internalDiagonalSlack
    rw [ite_eq_right hRank, min_eq_right hGapLeZ]
    unfold frobeniusRankAt
    omega

/-- terminal recurrence slack は terminal arm / leg の minimum。 -/
theorem terminalBasisSlack_frobenius_eq_terminalDiagonalSlack
    (c : WidthDropCode)
    (i : ℕ) :
    terminalBasisSlack
        (frobeniusRankAt c i)
        (frobeniusArmAt c i : ℤ) =
      (terminalDiagonalSlack c i : ℤ) := by
  by_cases hAL : frobeniusArmAt c i ≤ frobeniusLegAt c i
  · have hALZ :
        (frobeniusArmAt c i : ℤ) ≤ (frobeniusLegAt c i : ℤ) := by
      exact_mod_cast hAL
    have hRank : frobeniusRankAt c i ≤ 0 := by
      unfold frobeniusRankAt
      omega
    unfold terminalBasisSlack terminalDiagonalSlack
    rw [ite_eq_left hRank, min_eq_left hAL]
  · have hLA : frobeniusLegAt c i ≤ frobeniusArmAt c i :=
      Nat.le_of_lt (lt_of_not_ge hAL)
    have hlt : frobeniusLegAt c i < frobeniusArmAt c i :=
      lt_of_not_ge hAL
    have hltZ :
        (frobeniusLegAt c i : ℤ) < (frobeniusArmAt c i : ℤ) := by
      exact_mod_cast hlt
    have hRank : ¬ frobeniusRankAt c i ≤ 0 := by
      unfold frobeniusRankAt
      omega
    unfold terminalBasisSlack terminalDiagonalSlack
    rw [ite_eq_right hRank, min_eq_right hLA]
    unfold frobeniusRankAt
    ring

/--
Frobenius intervalを幾何 slack だけで並べる。
最後だけ terminal slack、その他は internal slack を使う。
-/
def diagonalBasisSlackVectorFrom
    (c : WidthDropCode) : ℕ → ℕ → List ℤ
  | _start, 0 => []
  | start, 1 => [(terminalDiagonalSlack c start : ℤ)]
  | start, n + 2 =>
      (internalDiagonalSlack c start : ℤ) ::
        diagonalBasisSlackVectorFrom c (start + 1) (n + 1)

/--
abstract recurrence slack vector と幾何 diagonal slack vector は exact に同じ。
-/
theorem basisSlackVector_frobeniusFrom_eq_diagonal
    (c : WidthDropCode) :
    ∀ start n,
      start + n ≤ frobeniusDepth c →
      basisSlackVector
          (successiveRankVectorFrom c start n)
          (frobeniusArmsZFrom c start n) =
        diagonalBasisSlackVectorFrom c start n
  | _start, 0, _h => by
      rfl
  | start, 1, _h => by
      simp only [
        successiveRankVectorFrom,
        frobeniusArmsZFrom,
        basisSlackVector,
        diagonalBasisSlackVectorFrom
      ]
      rw [terminalBasisSlack_frobenius_eq_terminalDiagonalSlack]
  | start, n + 2, h => by
      simp only [
        successiveRankVectorFrom,
        frobeniusArmsZFrom,
        basisSlackVector,
        diagonalBasisSlackVectorFrom
      ]
      rw [stepBasisSlack_frobenius_eq_internalDiagonalSlack c start (by omega)]
      have ih :=
        basisSlackVector_frobeniusFrom_eq_diagonal
          c (start + 1) (n + 1) (by omega)
      congr 1

/-- whole-shape 版の幾何 slack vector。 -/
def diagonalBasisSlackVector
    (c : WidthDropCode) : List ℤ :=
  diagonalBasisSlackVectorFrom c 0 (frobeniusDepth c)

/-- whole-shape でも abstract slack と geometric slack は一致する。 -/
theorem frobeniusBasisSlacks_eq_diagonalBasisSlackVector
    (c : WidthDropCode) :
    frobeniusBasisSlacks c = diagonalBasisSlackVector c := by
  unfold frobeniusBasisSlacks successiveRankVector frobeniusArmsZ
  unfold diagonalBasisSlackVector
  exact basisSlackVector_frobeniusFrom_eq_diagonal c 0 (frobeniusDepth c) (by simp)

/--
internal geometric slack が正であることと
simultaneous plateau boundary collision は同値。
-/
theorem internalDiagonalSlack_pos_iff_boundaryCollision
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c)
    (i : ℕ)
    (hDepth : i + 2 ≤ frobeniusDepth c) :
    0 < internalDiagonalSlack c i ↔
      WidthBoundaryAt c (i + 1) ∧
        DropHeightBoundaryAt c (i + 1) := by
  have hW : i + 1 < codeWidth c :=
    lt_of_lt_of_le
      (by omega)
      (frobeniusDepth_le_codeWidth c)
  have hH : i + 1 < codeDropSum c :=
    lt_of_lt_of_le
      (by omega)
      (frobeniusDepth_le_codeDropSum c)
  have hWidth :=
    widthBoundaryAt_iff_columnHeight_ne
      c hPos (i + 1) (by omega) hW
  have hDrop :=
    dropHeightBoundaryAt_iff_rowLength_ne
      c hPos (i + 1) (by omega) hH
  have hWidth' :
      WidthBoundaryAt c (i + 1) ↔
        frobeniusColumnHeight c i ≠
          frobeniusColumnHeight c (i + 1) := by
    simpa [frobeniusColumnHeight] using hWidth
  have hDrop' :
      DropHeightBoundaryAt c (i + 1) ↔
        frobeniusRowLength c i ≠
          frobeniusRowLength c (i + 1) := by
    simpa using hDrop
  have hRowMono :
      frobeniusRowLength c (i + 1) ≤
        frobeniusRowLength c i := by
    exact
      columnHeightFromWidthDropCode_antitone
        (conjugateWidthDropCode c) (Nat.le_succ i)
  have hColMono :
      frobeniusColumnHeight c (i + 1) ≤
        frobeniusColumnHeight c i := by
    exact
      columnHeightFromWidthDropCode_antitone
        c (Nat.le_succ i)
  constructor
  · intro hSlack
    unfold internalDiagonalSlack at hSlack
    have hMin :
        0 <
            frobeniusRowLength c i -
              frobeniusRowLength c (i + 1) ∧
          0 <
            frobeniusColumnHeight c i -
              frobeniusColumnHeight c (i + 1) := by
      exact (lt_min_iff.mp hSlack)
    have hRowNe :
        frobeniusRowLength c i ≠
          frobeniusRowLength c (i + 1) := by
      omega
    have hColNe :
        frobeniusColumnHeight c i ≠
          frobeniusColumnHeight c (i + 1) := by
      omega
    exact
      ⟨hWidth'.2 hColNe,
        hDrop'.2 hRowNe⟩
  · rintro ⟨hWB, hDB⟩
    have hColNe :
        frobeniusColumnHeight c i ≠
          frobeniusColumnHeight c (i + 1) :=
      hWidth'.1 hWB
    have hRowNe :
        frobeniusRowLength c i ≠
          frobeniusRowLength c (i + 1) :=
      hDrop'.1 hDB
    have hRowPos :
        0 <
          frobeniusRowLength c i -
            frobeniusRowLength c (i + 1) := by
      omega
    have hColPos :
        0 <
          frobeniusColumnHeight c i -
            frobeniusColumnHeight c (i + 1) := by
      omega
    unfold internalDiagonalSlack
    exact
      (lt_min_iff).2
        ⟨hRowPos, hColPos⟩

/-- geometric slack vector の各要素は非負。 -/
theorem diagonalBasisSlackVectorFrom_nonneg
    (c : WidthDropCode) :
    ∀ start n z,
      z ∈ diagonalBasisSlackVectorFrom c start n →
      0 ≤ z
  | _start, 0, z, hz => by
      simp [diagonalBasisSlackVectorFrom] at hz
  | start, 1, z, hz => by
      simp only [diagonalBasisSlackVectorFrom, List.mem_singleton] at hz
      subst z
      positivity
  | start, n + 2, z, hz => by
      simp only [diagonalBasisSlackVectorFrom, List.mem_cons] at hz
      rcases hz with hEq | hTail
      · subst z
        positivity
      · exact diagonalBasisSlackVectorFrom_nonneg c (start + 1) (n + 1) z hTail

/--
区間内の boundary collision は geometric slack vector の総和を正にする。
後段の weighted lower bound で tail に少なくとも1の slack があることを保証する。
-/
theorem diagonalBasisSlackVectorFrom_sum_pos_of_collision
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c) :
    ∀ start n t,
      start + n ≤ frobeniusDepth c →
      start < t →
      t < start + n →
      WidthBoundaryAt c t ∧ DropHeightBoundaryAt c t →
      0 < (diagonalBasisSlackVectorFrom c start n).sum
  | _start, 0, _t, _hDepth, hStart, hEnd, _hC => by
      omega
  | start, 1, t, _hDepth, hStart, hEnd, _hC => by
      omega
  | start, n + 2, t, hDepth, hStart, hEnd, hC => by
      simp only [diagonalBasisSlackVectorFrom, List.sum_cons]
      by_cases hEq : t = start + 1
      · subst t
        have hHeadNat : 0 < internalDiagonalSlack c start :=
          (internalDiagonalSlack_pos_iff_boundaryCollision
            c hPos start (by omega)).2 hC
        have hHead : (0 : ℤ) < (internalDiagonalSlack c start : ℤ) := by
          exact_mod_cast hHeadNat
        have hTailAll :
            ∀ z ∈ diagonalBasisSlackVectorFrom c (start + 1) (n + 1), 0 ≤ z := by
          intro z hz
          exact diagonalBasisSlackVectorFrom_nonneg c (start + 1) (n + 1) z hz
        have hTailSum :=
          sum_nonneg_of_mem_nonneg
            (diagonalBasisSlackVectorFrom c (start + 1) (n + 1)) hTailAll
        omega
      · have hNext : start + 1 < t := by omega
        have hTailPos :=
          diagonalBasisSlackVectorFrom_sum_pos_of_collision
            c hPos (start + 1) (n + 1) t (by omega) hNext (by omega) hC
        have hHeadNonneg :
            (0 : ℤ) ≤ (internalDiagonalSlack c start : ℤ) := by
          positivity
        omega

/--
collision level `t` は、その区間の weighted slack の下界になる。
level `t` の positive slack が左側の `t-start` 個の arm excess へ伝播することの定量形。
-/
theorem collisionDistance_le_weightedDiagonalSlack
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c) :
    ∀ start n t,
      start + n ≤ frobeniusDepth c →
      start < t →
      t < start + n →
      WidthBoundaryAt c t ∧ DropHeightBoundaryAt c t →
      ((t - start : ℕ) : ℤ) ≤
        weightedBasisSlack (diagonalBasisSlackVectorFrom c start n)
  | _start, 0, _t, _hDepth, hStart, hEnd, _hC => by
      omega
  | start, 1, t, _hDepth, hStart, hEnd, _hC => by
      omega
  | start, n + 2, t, hDepth, hStart, hEnd, hC => by
      simp only [diagonalBasisSlackVectorFrom, weightedBasisSlack]
      have hTailAll :
          ∀ z ∈ diagonalBasisSlackVectorFrom c (start + 1) (n + 1), 0 ≤ z := by
        intro z hz
        exact diagonalBasisSlackVectorFrom_nonneg c (start + 1) (n + 1) z hz
      have hTailW :=
        weightedBasisSlack_nonneg
          (diagonalBasisSlackVectorFrom c (start + 1) (n + 1)) hTailAll
      have hTailSumNonneg :=
        sum_nonneg_of_mem_nonneg
          (diagonalBasisSlackVectorFrom c (start + 1) (n + 1)) hTailAll
      by_cases hEq : t = start + 1
      · subst t
        have hHeadNat : 0 < internalDiagonalSlack c start :=
          (internalDiagonalSlack_pos_iff_boundaryCollision
            c hPos start (by omega)).2 hC
        have hHead : (1 : ℤ) ≤ (internalDiagonalSlack c start : ℤ) := by
          exact_mod_cast hHeadNat
        have hDist : start + 1 - start = 1 := by omega
        have hDistZ : (((start + 1 - start : ℕ) : ℤ)) = 1 := by
          exact_mod_cast hDist
        rw [hDistZ]
        omega
      · have hNext : start + 1 < t := by omega
        have hTailBound :=
          collisionDistance_le_weightedDiagonalSlack
            c hPos (start + 1) (n + 1) t (by omega) hNext (by omega) hC
        have hTailSumPos :=
          diagonalBasisSlackVectorFrom_sum_pos_of_collision
            c hPos (start + 1) (n + 1) t (by omega) hNext (by omega) hC
        have hDist : t - start = (t - (start + 1)) + 1 := by
          omega
        have hDistZ :
            ((t - start : ℕ) : ℤ) =
              ((t - (start + 1) : ℕ) : ℤ) + 1 := by
          exact_mod_cast hDist
        rw [hDistZ]
        omega

/-- whole shape で collision level `t` は weighted basis excess 以下。 -/
theorem collisionLevel_le_frobeniusWeightedBasisExcess
    (c : WidthDropCode)
    (hPos : PositiveWidthDropCode c)
    {t : ℕ}
    (ht : 0 < t)
    (htD : t < frobeniusDepth c)
    (hC : WidthBoundaryAt c t ∧ DropHeightBoundaryAt c t) :
    (t : ℤ) ≤ frobeniusWeightedBasisExcess c := by
  unfold frobeniusWeightedBasisExcess
  rw [frobeniusBasisSlacks_eq_diagonalBasisSlackVector]
  unfold diagonalBasisSlackVector
  have h :=
    collisionDistance_le_weightedDiagonalSlack
      c hPos 0 (frobeniusDepth c) t (by simp) ht (by simpa using htD) hC
  simpa using h

end YoungFerrersRestricted

namespace GenericRecordFerrers
namespace RecordFerrers

open YoungFerrersRestricted

/--
RecordFerrers の internal canonical collision level は weighted basis excess 以下。
-/
theorem collisionLevel_le_basisWeightedExcess
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode)
    (hC : R.HasCanonicalBoundaryCollision t) :
    (t : ℤ) ≤ R.basisWeightedExcess := by
  unfold basisWeightedExcess
  apply collisionLevel_le_frobeniusWeightedBasisExcess
    R.plateauWidthDropCode R.plateauWidthDropCode_positiveWidthDropCode ht htD
  exact (R.hasCanonicalBoundaryCollision_iff t).1 hC

/--
今回の調査で得た強い quantitative obstruction。
level `t` に internal canonical boundary collision があれば、
actual Young 面積は basis 最小面積より少なくとも `2*t` 大きい。
-/
theorem two_mul_collisionLevel_le_youngCellCount_sub_basisWeightZ
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode)
    (hC : R.HasCanonicalBoundaryCollision t) :
    (2 : ℤ) * (t : ℤ) ≤
      (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks := by
  have hLevel := R.collisionLevel_le_basisWeightedExcess ht htD hC
  rw [R.youngCellCount_sub_basisWeightZ_eq_two_mul_weightedExcess]
  omega

/--
collision level は gcd modulus の正の倍数でもあるため、
一つの internal collision は少なくとも `2 * rankDropGcd` の面積余剰を強制する。
-/
theorem two_mul_rankDropGcd_le_youngCellCount_sub_basisWeightZ_of_internalCollision
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode)
    (hC : R.HasCanonicalBoundaryCollision t) :
    (2 : ℤ) * (rankDropGcd β m : ℤ) ≤
      (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks := by
  have hDvd := R.hasCanonicalBoundaryCollision_rankDropGcd_dvd_nat hC
  have hGleNat : rankDropGcd β m ≤ t := Nat.le_of_dvd ht hDvd
  have hGle : (rankDropGcd β m : ℤ) ≤ (t : ℤ) := by
    exact_mod_cast hGleNat
  have hStrong :=
    R.two_mul_collisionLevel_le_youngCellCount_sub_basisWeightZ ht htD hC
  omega

/--
F10 の `>= 2` は `>= 2*t` の直接の系。
正の internal level では `t >= 1` だから最低余剰は2。
-/
theorem two_le_youngCellCount_sub_basisWeightZ_of_internalCollision_viaSlack
    {β : ℕ → ℕ}
    {m t : ℕ}
    (R : RecordFerrers β m)
    (ht : 0 < t)
    (htD : t < frobeniusDepth R.plateauWidthDropCode)
    (hC : R.HasCanonicalBoundaryCollision t) :
    (2 : ℤ) ≤
      (R.youngCellCount : ℤ) - basisWeightZ R.successiveRanks := by
  have hStrong :=
    R.two_mul_collisionLevel_le_youngCellCount_sub_basisWeightZ ht htD hC
  have htZ : (1 : ℤ) ≤ (t : ℤ) := by
    exact_mod_cast ht
  omega

end RecordFerrers
end GenericRecordFerrers
end Experimental2
end Collatz3
