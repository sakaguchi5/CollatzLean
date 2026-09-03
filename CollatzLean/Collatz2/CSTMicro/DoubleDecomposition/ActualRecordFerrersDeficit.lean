import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.CriticalGapOneFerrersCertificate
import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.RecordFerrersRowBandPhi
import Mathlib.Tactic.Linarith

/-!
# actual critical defect から作る RecordFerrers deficit

前段の `integerFerrersDeficit` は任意の `List FerrersRowBand` を評価できる。
第3例探索では、その帯列が actual word の critical defect から本当に生じたことを
保証する必要がある。

ここでは最も canonical で証明しやすい表現として、欠けた Ferrers セルを
「長さ1の水平帯」へ一つずつ分解する。

cut `k` の defect が `d` なら、level `1,...,d` に一セルずつ置く。
各セルの重みは

  2^(criticalHeight k - level) * 3^(p-(k+1))

であり、actual contribution とこれらのセルを足すと critical contribution に戻る。
これを全 cut で足し合わせることで

  affineConst(w) + FerrersDeficit(w) = criticalAffineConst(p)

を exact に得る。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

open scoped BigOperators

/--
一つの cut `k` に defect `d` 個の Ferrers セルを置く。
順序は上の level から下へ並ぶが、評価は加法的なので幾何内容は同じである。
-/
def criticalDefectColumnBands (k : ℕ) : ℕ → List FerrersRowBand
  | 0 => []
  | d + 1 =>
      ({ start := k, length := 1, level := d + 1 } : FerrersRowBand) ::
        criticalDefectColumnBands k d

/--
最初の `n` cut に対する actual Ferrers セル列。
各 cut `k` には `Word.criticalDefect w k` 個のセルを置く。
-/
def actualFerrersBandsPrefix (w : Word) : ℕ → List FerrersRowBand
  | 0 => []
  | n + 1 =>
      actualFerrersBandsPrefix w n ++
        criticalDefectColumnBands n (Word.criticalDefect w n)

/-- word 全体の affine sum に対応する canonical actual Ferrers セル列。 -/
def actualFerrersBands (w : Word) : List FerrersRowBand :=
  actualFerrersBandsPrefix w (Word.oddSteps w)

/-- `integerFerrersDeficit` は帯列の append に対して加法的。 -/
theorem integerFerrersDeficit_append
    (globalLength : ℕ)
    (xs ys : List FerrersRowBand) :
    integerFerrersDeficit globalLength (xs ++ ys) =
      integerFerrersDeficit globalLength xs +
        integerFerrersDeficit globalLength ys := by
  induction xs with
  | nil =>
      simp [integerFerrersDeficit]
  | cons x xs ih =>
      simp [integerFerrersDeficit, ih, add_assoc]

/-- 長さ1の帯は一つの Ferrers セルの重みそのもの。 -/
theorem rowBandExpandedCellSum_unit
    (globalLength k level : ℕ) :
    rowBandExpandedCellSum globalLength
      ({ start := k, length := 1, level := level } : FerrersRowBand) =
      (2 : ℤ) ^ (Word.criticalHeight k - level) *
        (3 : ℤ) ^ (globalLength - (k + 1)) := by
  simp [rowBandExpandedCellSum]

/--
同じ cut に縦に積んだ `d` 個の Ferrers セルは、
critical contribution と depth `d` 下の contribution の差を exact に埋める。

subtraction ではなく加法形で証明することで、自然数差分の切り捨てを避ける。
-/
theorem criticalDefectColumnBands_budget
    (globalLength k d : ℕ)
    (hd : d ≤ Word.criticalHeight k) :
    (2 : ℤ) ^ (Word.criticalHeight k - d) *
        (3 : ℤ) ^ (globalLength - (k + 1)) +
      integerFerrersDeficit globalLength
        (criticalDefectColumnBands k d) =
    (2 : ℤ) ^ Word.criticalHeight k *
      (3 : ℤ) ^ (globalLength - (k + 1)) := by
  revert hd
  induction d with
  | zero =>
      intro hd
      simp [criticalDefectColumnBands, integerFerrersDeficit]
  | succ d ih =>
      intro hd
      have hdPrev : d ≤ Word.criticalHeight k := by
        omega
      have hStep :
          Word.criticalHeight k - d =
            (Word.criticalHeight k - (d + 1)) + 1 := by
        omega
      have ihPrev := ih hdPrev
      simp only [criticalDefectColumnBands, integerFerrersDeficit]
      rw [rowBandExpandedCellSum_unit]
      calc
        (2 : ℤ) ^ (Word.criticalHeight k - (d + 1)) *
              (3 : ℤ) ^ (globalLength - (k + 1)) +
            ((2 : ℤ) ^ (Word.criticalHeight k - (d + 1)) *
                (3 : ℤ) ^ (globalLength - (k + 1)) +
              integerFerrersDeficit globalLength
                (criticalDefectColumnBands k d))
            =
          (2 : ℤ) ^ (Word.criticalHeight k - d) *
              (3 : ℤ) ^ (globalLength - (k + 1)) +
            integerFerrersDeficit globalLength
              (criticalDefectColumnBands k d) := by
                rw [hStep, pow_succ]
                ring
        _ =
          (2 : ℤ) ^ Word.criticalHeight k *
            (3 : ℤ) ^ (globalLength - (k + 1)) := ihPrev

/--
actual prefix depth が critical roof 以下なら、actual contribution と
その cut の canonical Ferrers セル列の和は critical contribution に一致する。
-/
theorem actualColumnBands_budget
    (w : Word)
    (globalLength k : ℕ)
    (hDepth : Word.prefixTwoDepth w k ≤ Word.criticalHeight k) :
    (2 : ℤ) ^ Word.prefixTwoDepth w k *
        (3 : ℤ) ^ (globalLength - (k + 1)) +
      integerFerrersDeficit globalLength
        (criticalDefectColumnBands k (Word.criticalDefect w k)) =
    (2 : ℤ) ^ Word.criticalHeight k *
      (3 : ℤ) ^ (globalLength - (k + 1)) := by
  have hDefLe :
      Word.criticalDefect w k ≤ Word.criticalHeight k := by
    unfold Word.criticalDefect
    omega
  have hRestore :
      Word.criticalHeight k - Word.criticalDefect w k =
        Word.prefixTwoDepth w k := by
    unfold Word.criticalDefect
    omega
  simpa [hRestore] using
    criticalDefectColumnBands_budget
      globalLength k (Word.criticalDefect w k) hDefLe

/-- actual affine contribution の整数版。 -/
def affinePathTermZ (w : Word) (k : ℕ) : ℤ :=
  (2 : ℤ) ^ Word.prefixTwoDepth w k *
    (3 : ℤ) ^ (Word.oddSteps w - (k + 1))

/-- critical roof contribution の整数版。 -/
def criticalAffineTermZ (p k : ℕ) : ℤ :=
  (2 : ℤ) ^ Word.criticalHeight k *
    (3 : ℤ) ^ (p - (k + 1))

/-- actual indexed sum の整数版は `affineConst` の cast に一致する。 -/
theorem affinePathTermZ_sum_eq_affineConst
    (w : Word) :
    Finset.sum (Finset.range (Word.oddSteps w))
        (fun k => affinePathTermZ w k) =
      (Word.affineConst w : ℤ) := by
  rw [← Word.affinePathSum_eq_affineConst]
  simp [Word.affinePathSum, affinePathTermZ, Word.affinePathTerm]

/-- critical indexed sum の整数版は `criticalAffineConst` の cast に一致する。 -/
theorem criticalAffineTermZ_sum_eq_criticalAffineConst
    (p : ℕ) :
    Finset.sum (Finset.range p) (fun k => criticalAffineTermZ p k) =
      (Word.criticalAffineConst p : ℤ) := by
  simp [Word.criticalAffineConst, Word.criticalAffineTerm, criticalAffineTermZ]

/--
最初の `n` cut について、actual affine sum と canonical Ferrers セル deficit の和は
critical roof affine sum に一致する。
-/
theorem actualFerrersBandsPrefix_budget
    (w : Word)
    (n : ℕ)
    (hDepth : ∀ k : ℕ, k < n →
      Word.prefixTwoDepth w k ≤ Word.criticalHeight k) :
    Finset.sum (Finset.range n) (fun k => affinePathTermZ w k) +
      integerFerrersDeficit (Word.oddSteps w)
        (actualFerrersBandsPrefix w n) =
    Finset.sum (Finset.range n)
      (fun k => criticalAffineTermZ (Word.oddSteps w) k) := by
  revert hDepth
  induction n with
  | zero =>
      intro hDepth
      simp [actualFerrersBandsPrefix, integerFerrersDeficit]
  | succ n ih =>
      intro hDepth
      have hPrev : ∀ k : ℕ, k < n →
          Word.prefixTwoDepth w k ≤ Word.criticalHeight k := by
        intro k hk
        exact hDepth k (by omega)
      have hThis :
          Word.prefixTwoDepth w n ≤ Word.criticalHeight n :=
        hDepth n (by omega)
      have ihPrev := ih hPrev
      have hColumn :=
        actualColumnBands_budget w (Word.oddSteps w) n hThis
      simp only [actualFerrersBandsPrefix]
      rw [integerFerrersDeficit_append]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      change
        (Finset.sum (Finset.range n) (fun k => affinePathTermZ w k) +
            affinePathTermZ w n) +
          (integerFerrersDeficit (Word.oddSteps w)
              (actualFerrersBandsPrefix w n) +
            integerFerrersDeficit (Word.oddSteps w)
              (criticalDefectColumnBands n (Word.criticalDefect w n))) =
        Finset.sum (Finset.range n)
            (fun k => criticalAffineTermZ (Word.oddSteps w) k) +
          criticalAffineTermZ (Word.oddSteps w) n
      calc
        (Finset.sum (Finset.range n) (fun k => affinePathTermZ w k) +
              affinePathTermZ w n) +
            (integerFerrersDeficit (Word.oddSteps w)
                (actualFerrersBandsPrefix w n) +
              integerFerrersDeficit (Word.oddSteps w)
                (criticalDefectColumnBands n (Word.criticalDefect w n)))
            =
          (Finset.sum (Finset.range n) (fun k => affinePathTermZ w k) +
              integerFerrersDeficit (Word.oddSteps w)
                (actualFerrersBandsPrefix w n)) +
            (affinePathTermZ w n +
              integerFerrersDeficit (Word.oddSteps w)
                (criticalDefectColumnBands n (Word.criticalDefect w n))) := by
                  ring
        _ =
          Finset.sum (Finset.range n)
              (fun k => criticalAffineTermZ (Word.oddSteps w) k) +
            criticalAffineTermZ (Word.oddSteps w) n := by
              rw [ihPrev]
              simpa [affinePathTermZ, criticalAffineTermZ] using hColumn

/--
FirstCrossing の全 affine cut では actual prefix depth は critical roof 以下。
`k=0` だけは既存 proper-prefix theorem の正値仮定外なので直接処理する。
-/
theorem firstCrossing_prefixTwoDepth_le_criticalHeight_all_affineCuts
    {w : Word}
    (hF : Word.FirstCrossing w)
    {k : ℕ}
    (hk : k < Word.oddSteps w) :
    Word.prefixTwoDepth w k ≤ Word.criticalHeight k := by
  by_cases hk0 : k = 0
  · subst k
    simp [Word.prefixTwoDepth, Word.criticalHeight]
  · exact hF.prefixTwoDepth_le_criticalHeight
      (Nat.pos_of_ne_zero hk0) hk

/--
actual word の canonical Ferrers セル deficit を足すと critical affine budget に戻る。

これは subtraction を使わない中心等式である。
-/
theorem affineConst_add_actualFerrersDeficit_eq_criticalAffineConst
    {w : Word}
    (C : ValidMinimalCrossingBlock w) :
    (Word.affineConst w : ℤ) +
      integerFerrersDeficit (Word.oddSteps w) (actualFerrersBands w) =
    (Word.criticalAffineConst (Word.oddSteps w) : ℤ) := by
  have hMinimal : w.Valid ∧ Word.FirstCrossing w := by
    exact C
  have hBudget :=
    actualFerrersBandsPrefix_budget w (Word.oddSteps w)
      (fun k hk =>
        firstCrossing_prefixTwoDepth_le_criticalHeight_all_affineCuts hMinimal.2 hk)
  unfold actualFerrersBands
  rw [affinePathTermZ_sum_eq_affineConst,
    criticalAffineTermZ_sum_eq_criticalAffineConst] at hBudget
  exact hBudget

/--
第3例探索で欲しかった exact deficit identity。

  criticalAffineConst(p) - affineConst(w)
    = integerFerrersDeficit(actual bands)

左辺は Collatz affine arithmetic、右辺は actual `criticalDefect` から生成した
RecordFerrers セルの重み付き面積である。
-/
theorem criticalAffineConst_sub_affineConst_eq_integerFerrersDeficit
    {w : Word}
    (C : ValidMinimalCrossingBlock w) :
    (Word.criticalAffineConst (Word.oddSteps w) : ℤ) -
        (Word.affineConst w : ℤ) =
      integerFerrersDeficit (Word.oddSteps w) (actualFerrersBands w) := by
  have h := affineConst_add_actualFerrersDeficit_eq_criticalAffineConst C
  linarith

/--
3番の row-band/Phi 定理と合わせた直接 corollary。
actual Ferrers deficit は同じ canonical 帯列の shifted `Phi` 総和でもある。
-/
theorem criticalAffineConst_sub_affineConst_eq_actualRowBandPhiSum
    {w : Word}
    (C : ValidMinimalCrossingBlock w) :
    (Word.criticalAffineConst (Word.oddSteps w) : ℤ) -
        (Word.affineConst w : ℤ) =
      rowBandPhiSum (Word.oddSteps w) (actualFerrersBands w) := by
  rw [criticalAffineConst_sub_affineConst_eq_integerFerrersDeficit C]
  exact integerFerrersDeficit_eq_rowBandPhiSum
    (Word.oddSteps w) (actualFerrersBands w)

end DoubleDecomposition
end CSTMicro
end Collatz2
