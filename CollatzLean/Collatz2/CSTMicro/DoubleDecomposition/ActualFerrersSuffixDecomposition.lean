import CollatzLean.Collatz2.CSTMicro.DoubleDecomposition.ActualRecordFerrersDeficit

/-!
# actual Ferrers suffix decomposition

`actualFerrersBandsPrefix` は左から prefix を伸ばす定義である。
このファイルでは同じ actual critical-defect cells を任意の start から有限区間だけ
切り出す薄い区間定義を追加する。

その上で

* 全 actual Ferrers deficit = start 0 の suffix deficit,
* suffix は左端 column + 次 suffix に exact 分解,
* 一列 deficit は
    `2^prefixDepth * (2^criticalDefect - 1) * 3^remaining`
  に exact factorization,
* `CriticalGapOneFerrersDeficitCertificate.deficit` は actual suffix sum そのもの,

を derived theorem として得る。
-/

namespace Collatz2
namespace CSTMicro
namespace DoubleDecomposition

/--
`start` から `length` 個の actual Ferrers columns を、既存の
`criticalDefectColumnBands` で並べた区間帯列。
-/
def actualFerrersBandsSegment
    (w : Word)
    (start : ℕ) : ℕ → List FerrersRowBand
  | 0 => []
  | n + 1 =>
      actualFerrersBandsSegment w start n ++
        criticalDefectColumnBands (start + n)
          (Word.criticalDefect w (start + n))

/-- 一つの actual cut が持つ signed integer Ferrers deficit。 -/
def actualFerrersColumnDeficitZ
    (w : Word)
    (k : ℕ) : ℤ :=
  integerFerrersDeficit (Word.oddSteps w)
    (criticalDefectColumnBands k (Word.criticalDefect w k))

/-- actual Ferrers interval の signed integer deficit。 -/
def actualFerrersSegmentDeficitZ
    (w : Word)
    (start length : ℕ) : ℤ :=
  integerFerrersDeficit (Word.oddSteps w)
    (actualFerrersBandsSegment w start length)

/-- cut `k` から word terminal までの canonical actual Ferrers suffix bands。 -/
def actualFerrersSuffixBands
    (w : Word)
    (k : ℕ) : List FerrersRowBand :=
  actualFerrersBandsSegment w k (Word.oddSteps w - k)

/-- cut `k` から terminal までの signed actual Ferrers deficit。 -/
def actualFerrersSuffixZ
    (w : Word)
    (k : ℕ) : ℤ :=
  actualFerrersSegmentDeficitZ w k (Word.oddSteps w - k)

@[simp] theorem actualFerrersBandsSegment_zero
    (w : Word)
    (start : ℕ) :
    actualFerrersBandsSegment w start 0 = [] := rfl

/-- 区間を左端一列と残りに分ける。 -/
theorem actualFerrersBandsSegment_succ_left
    (w : Word)
    (start n : ℕ) :
    actualFerrersBandsSegment w start (n + 1) =
      criticalDefectColumnBands start (Word.criticalDefect w start) ++
        actualFerrersBandsSegment w (start + 1) n := by
  induction n with
  | zero =>
      simp [actualFerrersBandsSegment]
  | succ n ih =>
      calc
        actualFerrersBandsSegment w start ((n + 1) + 1) =
            actualFerrersBandsSegment w start (n + 1) ++
              criticalDefectColumnBands
                (start + (n + 1))
                (Word.criticalDefect w (start + (n + 1))) := by
          rfl
        _ =
            (criticalDefectColumnBands
                start
                (Word.criticalDefect w start) ++
              actualFerrersBandsSegment w (start + 1) n) ++
              criticalDefectColumnBands
                (start + (n + 1))
                (Word.criticalDefect w (start + (n + 1))) := by
          rw [ih]
        _ =
            criticalDefectColumnBands
                start
                (Word.criticalDefect w start) ++
              (actualFerrersBandsSegment w (start + 1) n ++
                criticalDefectColumnBands
                  ((start + 1) + n)
                  (Word.criticalDefect w ((start + 1) + n))) := by
          rw [List.append_assoc]
          have hIndex :
              start + (n + 1) = (start + 1) + n := by
            omega
          rw [hIndex]
        _ =
            criticalDefectColumnBands
                start
                (Word.criticalDefect w start) ++
              actualFerrersBandsSegment w (start + 1) (n + 1) := by
          rfl

/-- 二つの隣接区間を exact に連結する。 -/
theorem actualFerrersBandsSegment_add
    (w : Word)
    (start a b : ℕ) :
    actualFerrersBandsSegment w start (a + b) =
      actualFerrersBandsSegment w start a ++
        actualFerrersBandsSegment w (start + a) b := by
  induction b with
  | zero =>
      simp [actualFerrersBandsSegment]
  | succ b ih =>
      simp [actualFerrersBandsSegment, ih, List.append_assoc,
         Nat.add_left_comm, Nat.add_comm]

/-- 既存 prefix 構成は start `0` の segment と同じ帯列。 -/
theorem actualFerrersBandsPrefix_eq_segment_zero
    (w : Word)
    (n : ℕ) :
    actualFerrersBandsPrefix w n =
      actualFerrersBandsSegment w 0 n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [actualFerrersBandsPrefix, actualFerrersBandsSegment, ih]

/-- 全 actual bands は start `0` の suffix bands と一致。 -/
theorem actualFerrersSuffixBands_zero_eq_actualFerrersBands
    (w : Word) :
    actualFerrersSuffixBands w 0 = actualFerrersBands w := by
  unfold actualFerrersSuffixBands actualFerrersBands
  simp only [Nat.sub_zero]
  rw [← actualFerrersBandsPrefix_eq_segment_zero]

/-- interval deficit は隣接 interval の和に分解する。 -/
theorem actualFerrersSegmentDeficitZ_add
    (w : Word)
    (start a b : ℕ) :
    actualFerrersSegmentDeficitZ w start (a + b) =
      actualFerrersSegmentDeficitZ w start a +
        actualFerrersSegmentDeficitZ w (start + a) b := by
  unfold actualFerrersSegmentDeficitZ
  rw [actualFerrersBandsSegment_add]
  exact integerFerrersDeficit_append _ _ _

/-- interval deficit を右端一列だけ伸ばす recurrence。 -/
theorem actualFerrersSegmentDeficitZ_succ_right
    (w : Word)
    (start n : ℕ) :
    actualFerrersSegmentDeficitZ w start (n + 1) =
      actualFerrersSegmentDeficitZ w start n +
        actualFerrersColumnDeficitZ w (start + n) := by
  unfold actualFerrersSegmentDeficitZ actualFerrersColumnDeficitZ
  simp only [actualFerrersBandsSegment]
  exact integerFerrersDeficit_append _ _ _

/-- interval deficit の左端一列 recurrence。 -/
theorem actualFerrersSegmentDeficitZ_succ_left
    (w : Word)
    (start n : ℕ) :
    actualFerrersSegmentDeficitZ w start (n + 1) =
      actualFerrersColumnDeficitZ w start +
        actualFerrersSegmentDeficitZ w (start + 1) n := by
  unfold actualFerrersSegmentDeficitZ actualFerrersColumnDeficitZ
  rw [actualFerrersBandsSegment_succ_left]
  exact integerFerrersDeficit_append _ _ _

/-- `k <= p` なら whole deficit は prefix `[0,k)` と suffix `[k,p)` に分かれる。 -/
theorem actualFerrersSuffixZ_zero_split
    (w : Word)
    {k : ℕ}
    (hk : k ≤ Word.oddSteps w) :
    actualFerrersSuffixZ w 0 =
      actualFerrersSegmentDeficitZ w 0 k + actualFerrersSuffixZ w k := by
  unfold actualFerrersSuffixZ
  simp only [Nat.sub_zero]
  have hp : Word.oddSteps w = k + (Word.oddSteps w - k) := by
    omega
  rw [hp]
  rw [actualFerrersSegmentDeficitZ_add]
  simp

/-- proper cut では suffix は左端 column + 次 suffix。 -/
theorem actualFerrersSuffixZ_step
    (w : Word)
    {k : ℕ}
    (hk : k < Word.oddSteps w) :
    actualFerrersSuffixZ w k =
      actualFerrersColumnDeficitZ w k + actualFerrersSuffixZ w (k + 1) := by
  unfold actualFerrersSuffixZ
  have hLen :
      Word.oddSteps w - k =
        (Word.oddSteps w - (k + 1)) + 1 := by
    omega
  rw [hLen]
  simpa using
    (actualFerrersSegmentDeficitZ_succ_left
      w k (Word.oddSteps w - (k + 1)))

/-- terminal cut の suffix deficit は zero。 -/
@[simp] theorem actualFerrersSuffixZ_terminal
    (w : Word) :
    actualFerrersSuffixZ w (Word.oddSteps w) = 0 := by
  simp [actualFerrersSuffixZ, actualFerrersSegmentDeficitZ,integerFerrersDeficit]

/--
FirstCrossing proper cut の一列 Ferrers deficit の exact factorization。

  column(k)
    = 2^prefixDepth(k) * (2^criticalDefect(k)-1) * 3^(p-k-1).
-/
theorem actualFerrersColumnDeficitZ_eq_factor
    {w : Word}
    (hF : Word.FirstCrossing w)
    {k : ℕ}
    (hk : k < Word.oddSteps w) :
    actualFerrersColumnDeficitZ w k =
      (2 : ℤ) ^ Word.prefixTwoDepth w k *
        ((2 : ℤ) ^ Word.criticalDefect w k - 1) *
        (3 : ℤ) ^ (Word.oddSteps w - (k + 1)) := by
  have hDepth :
      Word.prefixTwoDepth w k ≤ Word.criticalHeight k :=
    firstCrossing_prefixTwoDepth_le_criticalHeight_all_affineCuts hF hk
  have hBudget :=
    actualColumnBands_budget w (Word.oddSteps w) k hDepth
  have hRestore :
      Word.criticalHeight k =
        Word.prefixTwoDepth w k + Word.criticalDefect w k := by
    unfold Word.criticalDefect
    omega
  unfold actualFerrersColumnDeficitZ at hBudget ⊢
  rw [hRestore, pow_add] at hBudget
  nlinarith

/-- start `0` の suffix deficit は既存 canonical actual Ferrers deficit。 -/
theorem actualFerrersSuffixZ_zero_eq_integerFerrersDeficit
    (w : Word) :
    actualFerrersSuffixZ w 0 =
      integerFerrersDeficit (Word.oddSteps w) (actualFerrersBands w) := by
  unfold actualFerrersSuffixZ actualFerrersSegmentDeficitZ
  simp only [Nat.sub_zero]
  rw [← actualFerrersBandsPrefix_eq_segment_zero]
  rfl

/--
強化 gap-one certificate が保持する `deficit` は、別の自由変数ではなく
actual word の canonical Ferrers suffix sum そのもの。
-/
theorem exactGapOne_deficit_eq_actualSuffixSum
    {w : Word}
    {p H deficit gap m : ℕ}
    (C : CriticalGapOneFerrersDeficitCertificate
      w p H deficit gap m) :
    (deficit : ℤ) = actualFerrersSuffixZ w 0 := by
  have hFerrers :=
    criticalAffineConst_sub_affineConst_eq_integerFerrersDeficit C.minimal
  rw [C.oddSteps_eq] at hFerrers
  have hBudgetZ := congrArg (fun n : ℕ => (n : ℤ)) C.affine_budget
  push_cast at hBudgetZ
  have hSuffix := actualFerrersSuffixZ_zero_eq_integerFerrersDeficit w
  rw [C.oddSteps_eq] at hSuffix
  linarith

end DoubleDecomposition
end CSTMicro
end Collatz2
