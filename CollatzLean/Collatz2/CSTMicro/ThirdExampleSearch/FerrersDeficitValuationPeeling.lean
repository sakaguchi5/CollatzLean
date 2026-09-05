import CollatzLean.Collatz2.CSTMicro.ThirdExampleSearch.ThirdExampleFirstDefectOneCell

/-!
# 第3例探索 5: Ferrers deficit の valuation peeling

既に処理済みの列を critical roof へ「修復」してから残差を見る。
cutoff より左を roof に戻した profile と critical roof の Ferrers code 差を

  residualZ(w, cutoff)

とする。

cutoff 以降で次に roof から外れる列を `j` とすると、その残差の exact 2進深さは
actual height `prefixTwoDepth w j` に一致する。

これにより defect depth を一個ずつ総当たりせず、残差の 2進 valuation から
次の visible defect を読める。
-/

namespace Collatz2
namespace CSTMicro
namespace ThirdExampleSearch
namespace FerrersDeficit

open DoubleDecomposition

/-- cutoff より左を critical roof へ修復した高さ profile。 -/
def repairedHeight (w : Word) (cutoff k : ℕ) : ℕ :=
  if k < cutoff then Word.criticalHeight k else Word.prefixTwoDepth w k

/-- 処理済み prefix を消した後の signed Ferrers residual。 -/
def residualZ (w : Word) (cutoff : ℕ) : ℤ :=
  Word.criticalFerrersCodeDiffZ
    (Word.oddSteps w)
    Word.criticalHeight
    (repairedHeight w cutoff)

/-- cutoff 以降で最初に現れる critical defect。 -/
structure NextCriticalDefectAt (w : Word) (cutoff j : ℕ) : Prop where
  cutoff_le : cutoff ≤ j
  index_lt : j < Word.oddSteps w
  before : ∀ i : ℕ, cutoff ≤ i → i < j →
    Word.prefixTwoDepth w i = Word.criticalHeight i
  current_lt :
    Word.prefixTwoDepth w j < Word.criticalHeight j

/-- executable decoder が返す一つの visible defect。 -/
structure VisibleDefect where
  index : ℕ
  height : ℕ
  deriving DecidableEq, Repr

/-- visible entry の defect depth。 -/
def VisibleDefect.depth (E : VisibleDefect) : ℕ :=
  Word.criticalHeight E.index - E.height

/--
次の defect より前の critical heights は、その defect の actual height より低い。
-/
theorem criticalHeight_lt_nextHeight_before
    {w : Word}
    (hValid : Word.Valid w)
    {cutoff j i : ℕ}
    (N : NextCriticalDefectAt w cutoff j)
    (hci : cutoff ≤ i)
    (hij : i < j) :
    Word.criticalHeight i < Word.prefixTwoDepth w j := by
  have hEq := N.before i hci hij
  have hInc := Word.prefixTwoDepth_lt_of_valid hValid
    (i := i) (j := j) hij (Nat.le_of_lt N.index_lt)
  rw [hEq] at hInc
  exact hInc

/--
valuation-peeling の中心補題。
`residualZ` の exact 2進深さは、cutoff 以降の次 defect の actual height である。
-/
theorem nextVisibleDefect_exactTwoPow
    {w : Word}
    (hValid : Word.Valid w)
    {cutoff j : ℕ}
    (N : NextCriticalDefectAt w cutoff j) :
    Word.ExactTwoPowZ
      (Word.prefixTwoDepth w j)
      (residualZ w cutoff) := by
  let a := Word.prefixTwoDepth w j
  have hCutoffJ : cutoff ≤ j :=
    N.cutoff_le
  have hCurrentLt :
      Word.prefixTwoDepth w j <
        Word.criticalHeight j :=
    N.current_lt
  have hBefore :
      ∀ i : ℕ, i < j →
        Word.criticalHeight i =
          repairedHeight w cutoff i := by
    intro i hij
    by_cases hi : i < cutoff
    · simp [repairedHeight, hi]
    · have hci : cutoff ≤ i :=
        Nat.le_of_not_gt hi
      have hEq :
          Word.prefixTwoDepth w i =
            Word.criticalHeight i :=
        N.before i hci hij
      simp [repairedHeight, hi, hEq]
  have hAtJ :
      repairedHeight w cutoff j =
        Word.prefixTwoDepth w j := by
    have hnot : ¬ j < cutoff :=
      Nat.not_lt_of_ge hCutoffJ
    simp [repairedHeight, hnot]
  have hNe :
      Word.criticalHeight j ≠
        repairedHeight w cutoff j := by
    rw [hAtJ]
    exact (Nat.ne_of_lt hCurrentLt).symm
  have hMin :
      a =
        min
          (Word.criticalHeight j)
          (repairedHeight w cutoff j) := by
    rw [hAtJ]
    dsimp [a]
    rw [
      Nat.min_eq_right
        (Nat.le_of_lt hCurrentLt)
    ]
  have hAfter :
      ∀ i : ℕ, j < i → i < Word.oddSteps w →
        a < Word.criticalHeight i ∧
          a < repairedHeight w cutoff i := by
    intro i hji hi
    have hCrit :
        Word.criticalHeight j <
          Word.criticalHeight i := by
      have hb := beattyIndex_strictMono hji
      simpa [criticalHeight_eq_beattyIndex] using hb
    have hActual :
        Word.prefixTwoDepth w j <
          Word.prefixTwoDepth w i :=
      Word.prefixTwoDepth_lt_of_valid
        hValid
        hji
        (Nat.le_of_lt hi)
    have hCutoffI : cutoff ≤ i :=
      le_trans hCutoffJ (Nat.le_of_lt hji)
    have hnot : ¬ i < cutoff :=
      Nat.not_lt_of_ge hCutoffI
    constructor
    · dsimp [a]
      exact lt_trans hCurrentLt hCrit
    · simpa [repairedHeight, hnot, a] using hActual
  unfold residualZ
  exact
    Word.firstDifference_twoPow_exact
      N.index_lt
      hBefore
      hNe
      hMin
      hAfter

/--
`nextVisibleDefect` は valuation と幾何を一度に返す wrapper。
-/
theorem nextVisibleDefect
    {w : Word}
    (hValid : Word.Valid w)
    {cutoff j : ℕ}
    (N : NextCriticalDefectAt w cutoff j) :
    Word.ExactTwoPowZ
        (Word.prefixTwoDepth w j) (residualZ w cutoff) ∧
      (∀ i : ℕ, cutoff ≤ i → i < j →
        Word.criticalHeight i < Word.prefixTwoDepth w j) ∧
      Word.prefixTwoDepth w j < Word.criticalHeight j := by
  refine ⟨nextVisibleDefect_exactTwoPow hValid N, ?_, N.current_lt⟩
  intro i hci hij
  exact criticalHeight_lt_nextHeight_before hValid N hci hij

end FerrersDeficit
end ThirdExampleSearch
end CSTMicro
end Collatz2
