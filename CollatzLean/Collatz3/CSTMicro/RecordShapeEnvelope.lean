import CollatzLean.Collatz3.CSTMicro.RecordCompatibility

/-!
# Collatz3 CSTMicro Stage 7B: RecordFerrers shape-sensitive affine envelope

RecordFerrers の canonical block widths を

  [r₁, ..., r_s]

とする。

各 local critical block の exact affine translation を、その block width だけで決まる
Stage 3 の `roofAffineBound r_i` で置き換える。一方、block composition の
3/2 weights は既存 `affineConstBlocks` と同じものを exact に保つ。

これにより whole width `p` だけの一様 roof ではなく、canonical record partition の形に
依存する finite envelope を得る。
-/

namespace Collatz3
namespace CSTMicro

open Critical

/--
canonical block width 列だけから作る affine roof fold。

head block `r` の translation は `roofAffineBound r` で抑え、
suffix の odd width は `rs.sum`、head の two-depth は `criticalTwoDepth r` を使う。
-/
def recordShapeRoofBlocks : List ℕ → ℕ
  | [] => 0
  | r :: rs =>
      3 ^ rs.sum * roofAffineBound r +
        2 ^ criticalTwoDepth r * recordShapeRoofBlocks rs

/-- RecordFerrers whole word の shape-sensitive roof。 -/
def recordShapeRoof
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) : ℕ :=
  3 ^ (m - 1) +
    2 * recordShapeRoofBlocks
      (Ferrers.canonicalRecordLengths R.profile.1)

/-- critical block 対応があれば local word 列の total odd width は width 列の和。 -/
theorem wordsOddSteps_eq_sum_of_forall₂_critical
    {rs : List ℕ}
    {ws : List Word}
    (h : List.Forall₂
      (fun r w => Critical.IsCriticalWord r w) rs ws) :
    Ferrers.wordsOddSteps ws = rs.sum := by
  induction h with
  | nil =>
      simp [Ferrers.wordsOddSteps]
  | @cons r w rs ws hHead hTail ih =>
      change
        w.oddSteps + Ferrers.wordsOddSteps ws =
          r + rs.sum
      rw [hHead.oddSteps_eq, ih]

/--
critical local word 列の exact affine fold は、対応 width 列の shape roof fold 以下。
-/
theorem affineConstBlocks_le_recordShapeRoofBlocks_of_forall₂_critical
    {rs : List ℕ}
    {ws : List Word}
    (h : List.Forall₂
      (fun r w => Critical.IsCriticalWord r w) rs ws) :
    Ferrers.affineConstBlocks ws ≤ recordShapeRoofBlocks rs := by
  induction h with
  | nil =>
      simp [Ferrers.affineConstBlocks, recordShapeRoofBlocks]
  | @cons r w rs ws hHead hTail ih =>
      have hOdd : Ferrers.wordsOddSteps ws = rs.sum :=
        wordsOddSteps_eq_sum_of_forall₂_critical hTail
      have hFirst : Word.CriticalFirstPassage w :=
        Critical.criticalFirstPassage_of_isCriticalWord hHead
      have hB : Word.affineConst w ≤ roofAffineBound r := by
        have hRaw := affineConst_le_roofAffineBound_of_critical hFirst
        rw [hHead.oddSteps_eq] at hRaw
        exact hRaw
      unfold Ferrers.affineConstBlocks recordShapeRoofBlocks
      rw [hOdd, hHead.twoSteps_eq]
      exact Nat.add_le_add
        (Nat.mul_le_mul_left _ hB)
        (Nat.mul_le_mul_left _ ih)

/-- canonical RecordFerrers block fold は canonical record-length shape roof 以下。 -/
theorem recordFerrers_affineConstBlocks_le_recordShapeRoofBlocks
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    Ferrers.affineConstBlocks R.canonicalLocalWords ≤
      recordShapeRoofBlocks
        (Ferrers.canonicalRecordLengths R.profile.1) := by
  exact
    affineConstBlocks_le_recordShapeRoofBlocks_of_forall₂_critical
      R.canonicalLocalWords_forall₂_critical

/--
RecordFerrers profile word の affine translation は shape-sensitive roof 以下。
-/
theorem recordFerrers_affineConst_wordOfProfile_le_recordShapeRoof
    {m : ℕ}
    (R : Ferrers.RecordFerrers m) :
    Word.affineConst (Critical.wordOfProfile R.profile.1) ≤
      recordShapeRoof R := by
  rw [R.affineConst_wordOfProfile_eq_head_add_two_mul_blocks]
  unfold recordShapeRoof
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left 2
      (recordFerrers_affineConstBlocks_le_recordShapeRoofBlocks R))
    _

namespace FirstPassagePath

/-- standard Record-compatible path の shape-sensitive roof。 -/
def recordShapeAffineBound
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp) : ℕ :=
  recordShapeRoof (P.recordFerrers hp hRecord)

/-- Record-compatible branch では standard affine numerator `B` は shape roof 以下。 -/
theorem affineConst_le_recordShapeAffineBound
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp) :
    affineConst P.word ≤ P.recordShapeAffineBound hp hRecord := by
  rw [P.affineConst_eq_recordFactorization hp hRecord]
  unfold recordShapeAffineBound recordShapeRoof
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left 2
      (recordFerrers_affineConstBlocks_le_recordShapeRoofBlocks
        (P.recordFerrers hp hRecord)))
    _

/-- `D*x ≤ B_shape` を division-free に保持する shape capacity cutoff。 -/
theorem terminalGap_mul_start_le_recordShapeAffineBound_of_withinCapacity
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp)
    {x : ℕ}
    (hCap : P.WithinCapacity x) :
    P.terminalGap * x ≤ P.recordShapeAffineBound hp hRecord := by
  exact le_trans hCap (P.affineConst_le_recordShapeAffineBound hp hRecord)

/-- 非下降 affine realization は RecordFerrers shape cutoff 内にある。 -/
theorem terminalGap_mul_start_le_recordShapeAffineBound_of_nondecreasing
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp)
    {x y : ℕ}
    (h : AffineRealizes P.word x y)
    (hxy : x ≤ y) :
    P.terminalGap * x ≤ P.recordShapeAffineBound hp hRecord := by
  have hCap := P.withinCapacity_of_affine_start_le_end h hxy
  exact
    P.terminalGap_mul_start_le_recordShapeAffineBound_of_withinCapacity
      hp hRecord hCap

/-- exact parity trace 版の RecordFerrers shape cutoff。 -/
theorem terminalGap_mul_start_le_recordShapeAffineBound_of_nondecreasing_trace
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y) :
    P.terminalGap * x ≤ P.recordShapeAffineBound hp hRecord := by
  exact
    P.terminalGap_mul_start_le_recordShapeAffineBound_of_nondecreasing
      hp hRecord h.affine hxy

/-- shape roof を terminal gap で割った Archimedean start bound。 -/
def recordShapeStartBound
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp) : ℕ :=
  P.recordShapeAffineBound hp hRecord / P.terminalGap

/-- 非下降 trace の start は `B_shape / D` 以下。 -/
theorem start_le_recordShapeStartBound_of_nondecreasing_trace
    (P : FirstPassagePath)
    (hp : 0 < P.endpointOddCount)
    (hRecord : P.RecordCompatible hp)
    {x y : ℕ}
    (h : TraceRealizes P.word x y)
    (hxy : x ≤ y) :
    x ≤ P.recordShapeStartBound hp hRecord := by
  unfold recordShapeStartBound
  apply (Nat.le_div_iff_mul_le P.terminalGap_pos).2
  have hBound :=
    P.terminalGap_mul_start_le_recordShapeAffineBound_of_nondecreasing_trace
      hp hRecord h hxy
  simpa [Nat.mul_comm] using hBound

end FirstPassagePath
end CSTMicro
end Collatz3
